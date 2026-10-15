// acengine — command-line front end.  All I/O is JSON Lines.
//
//   acengine replay                       {r0,r1,path} -> final state, work, peak
//   acengine build-endgame --radius B --out FILE
//   acengine solve   [--key value ...]    {id,r0,r1[,seed][,params]} -> {id,solved,path,...}
//   acengine shorten [--key value ...]    {id,r0,r1,path} -> {id,path,before,after}
//   acengine features                     {r0,r1,path} -> {X:[[..]],y:[..]} along the path
//   acengine random-test --n N --len L    random sequences for cross-checking
//
// Common flags: --endgame FILE --model FILE --macros FILE --threads T
// Search flags map 1:1 onto ac::Params fields (see search.hpp), and can be
// overridden per input line with a "params" object.
#include <atomic>
#include <fstream>
#include <iostream>
#include <mutex>
#include <thread>

#include "json.hpp"
#include "shorten.hpp"

using namespace ac;

namespace ac {
std::string word_str(const Word& w) { return mj::arr(w); }
}  // namespace ac

static std::map<std::string, std::string> parse_flags(int argc, char** argv, int from) {
  std::map<std::string, std::string> f;
  for (int i = from; i < argc; ++i) {
    std::string k = argv[i];
    if (k.rfind("--", 0) != 0) throw std::runtime_error("bad flag " + k);
    k = k.substr(2);
    std::string v = (i + 1 < argc && std::string(argv[i + 1]).rfind("--", 0) != 0) ? argv[++i] : "1";
    f[k] = v;
  }
  return f;
}

static void set_param(Params& P, ShortenParams& SP, const std::string& k, const std::string& v) {
  if (k == "strategy") P.strategy = v;
  else if (k == "max_nodes") P.max_nodes = std::stoll(v);
  else if (k == "time_limit") P.time_limit = std::stod(v);
  else if (k == "maxlen") P.maxlen = std::stoi(v);
  else if (k == "lam") P.lam = std::stod(v);
  else if (k == "noise") P.noise = std::stod(v);
  else if (k == "beam_width") P.beam_width = std::stoi(v);
  else if (k == "max_depth") P.max_depth = std::stoi(v);
  else if (k == "p_greedy") P.p_greedy = std::stod(v);
  else if (k == "walk_len") P.walk_len = std::stoi(v);
  else if (k == "T0") P.T0 = std::stod(v);
  else if (k == "T1") P.T1 = std::stod(v);
  else if (k == "bidir_fwd") P.bidir_fwd = std::stoi(v);
  else if (k == "w_len") P.w_len = std::stod(v);
  else if (k == "w_model") P.w_model = std::stod(v);
  else if (k == "w_cyc") P.w_cyc = std::stod(v);
  else if (k == "stop_first") P.stop_first = v != "0";
  else if (k == "d1") SP.d1 = std::stoi(v);
  else if (k == "d2") SP.d2 = std::stoi(v);
  else if (k == "ball_budget") SP.ball_budget = std::stoll(v);
  else if (k == "shorten_rounds") SP.max_rounds = std::stoi(v);
  else if (k == "shorten_time") SP.time_limit = std::stod(v);
  // flags consumed elsewhere
  else if (k == "endgame" || k == "model" || k == "macros" || k == "threads" || k == "seed" || k == "shorten" ||
           k == "radius" || k == "out" || k == "n" || k == "len")
    ;
  else throw std::runtime_error("unknown parameter " + k);
}

static std::string val_to_str(const mj::Value& v) {
  if (v.t == mj::Value::STR) return v.s;
  if (v.t == mj::Value::BOOL) return v.b ? "1" : "0";
  if (v.is_int) return std::to_string(v.i);
  std::ostringstream ss;
  ss.precision(12);
  ss << v.num;
  return ss.str();
}

static State state_of(const mj::Value& v) {
  State s;
  for (int x : v["r0"].as_ints()) s.r[0].push_back((Letter)x);
  for (int x : v["r1"].as_ints()) s.r[1].push_back((Letter)x);
  if (free_reduce(s.r[0]) != s.r[0] || free_reduce(s.r[1]) != s.r[1])
    throw std::runtime_error("input relators not freely reduced");
  return s;
}

static uint64_t str_hash(const std::string& s) {
  uint64_t h = 1469598103934665603ULL;
  for (char c : s) h = (h ^ (uint8_t)c) * 1099511628211ULL;
  return mix64(h);
}

static std::vector<std::string> read_lines(std::istream& in) {
  std::vector<std::string> lines;
  std::string l;
  while (std::getline(in, l))
    if (!l.empty() && l.find_first_not_of(" \t\r") != std::string::npos) lines.push_back(l);
  return lines;
}

struct Shared {
  Endgame eg;
  MLP mlp;
  std::vector<std::vector<int>> macros;
};

static void load_shared(Shared& S, std::map<std::string, std::string>& F) {
  if (F.count("endgame")) {
    if (!S.eg.load(F["endgame"])) throw std::runtime_error("cannot load endgame " + F["endgame"]);
    fprintf(stderr, "endgame radius %d, %zu states\n", S.eg.radius, S.eg.map.size());
  }
  if (F.count("model")) S.mlp.load(F["model"]);
  if (F.count("macros")) {
    std::ifstream f(F["macros"]);
    for (auto& l : read_lines(f)) {
      auto v = mj::parse(l);
      auto ms = v.t == mj::Value::ARR ? v.as_ints() : v["moves"].as_ints();
      if (!ms.empty()) S.macros.push_back(ms);
    }
  }
}

template <class Fn>
static void parallel_lines(const std::vector<std::string>& lines, int threads, Fn fn) {
  std::atomic<size_t> next{0};
  std::mutex out_mu;
  auto worker = [&](int tid) {
    while (true) {
      size_t i = next++;
      if (i >= lines.size()) break;
      std::string out;
      try {
        out = fn(lines[i], tid);
      } catch (std::exception& e) {
        out = mj::ObjWriter().str("error", e.what()).integer("line", (long long)i).done();
      }
      std::lock_guard<std::mutex> g(out_mu);
      std::cout << out << "\n" << std::flush;
    }
  };
  std::vector<std::thread> ts;
  for (int t = 0; t < threads; ++t) ts.emplace_back(worker, t);
  for (auto& t : ts) t.join();
}

int main(int argc, char** argv) {
  std::ios::sync_with_stdio(false);
  if (argc < 2) {
    fprintf(stderr, "usage: acengine <replay|build-endgame|solve|shorten|features|random-test> [flags]\n");
    return 3;
  }
  std::string cmd = argv[1];
  try {
    auto F = parse_flags(argc, argv, 2);
    Params base;
    ShortenParams sbase;
    for (auto& [k, v] : F) set_param(base, sbase, k, v);
    int threads = F.count("threads") ? std::stoi(F["threads"]) : (int)std::thread::hardware_concurrency();
    uint64_t seed = F.count("seed") ? std::stoull(F["seed"]) : 12345;

    if (cmd == "build-endgame") {
      Endgame eg;
      eg.build(std::stoi(F["radius"]));
      eg.save(F["out"]);
      return 0;
    }
    if (cmd == "replay") {
      for (auto& l : read_lines(std::cin)) {
        auto v = mj::parse(l);
        State s = state_of(v);
        auto r = replay(s, v["path"].as_ints());
        std::cout << mj::ObjWriter()
                         .ints("r0", r.final.r[0])
                         .ints("r1", r.final.r[1])
                         .integer("work", r.work)
                         .integer("peak", r.peak)
                         .boolean("target", is_target(r.final))
                         .done()
                  << "\n";
      }
      return 0;
    }
    if (cmd == "random-test") {
      // Emit random start states (freely reduced) and random move paths, with
      // the engine's final state, for cross-checking against the verifier.
      std::mt19937_64 rng(seed);
      int N = F.count("n") ? std::stoi(F["n"]) : 1000, L = F.count("len") ? std::stoi(F["len"]) : 50;
      const Letter LET[4] = {1, -1, 2, -2};
      for (int t = 0; t < N; ++t) {
        State s;
        for (int r = 0; r < 2; ++r) {
          Word w;
          int len = (int)(rng() % 12);
          for (int i = 0; i < len; ++i) w.push_back(LET[rng() % 4]);
          s.r[r] = free_reduce(w);
        }
        std::vector<int> p;
        int len = (int)(rng() % (L + 1));
        // keep only the prefix that stays within the verifier's limits
        State cur = s;
        long long work = (long long)cur.total();
        for (int i = 0; i < len; ++i) {
          int m = (int)(rng() % NUM_MOVES);
          apply_move(cur, m);
          work += (long long)cur.total();
          if (cur.total() > 10000 || work > 5000000) break;
          p.push_back(m);
        }
        auto r = replay(s, p);
        std::cout << mj::ObjWriter()
                         .ints("r0", s.r[0])
                         .ints("r1", s.r[1])
                         .ints("path", p)
                         .ints("f0", r.final.r[0])
                         .ints("f1", r.final.r[1])
                         .integer("work", r.work)
                         .done()
                  << "\n";
      }
      return 0;
    }

    Shared S;
    load_shared(S, F);
    if (!S.eg.loaded()) fprintf(stderr, "warning: no endgame table; only exact target is terminal\n");
    auto lines = read_lines(std::cin);

    if (cmd == "solve") {
      bool do_shorten = F.count("shorten") && F["shorten"] != "0";
      parallel_lines(lines, threads, [&](const std::string& l, int) {
        auto v = mj::parse(l);
        Params P = base;
        ShortenParams SP = sbase;
        P.macros = S.macros;
        if (v.has("params"))
          for (auto& [k, pv] : v["params"].o) set_param(P, SP, k, val_to_str(pv));
        std::string id = v["id"].as_str();
        uint64_t s = v.has("seed") ? (uint64_t)v["seed"].as_int() : seed;
        State st = state_of(v);
        Ctx C;
        C.eg = &S.eg;
        C.mlp = &S.mlp;
        C.rng.seed(mix64(s ^ str_hash(id)));
        C.t0 = std::chrono::steady_clock::now();
        SearchResult R = run_search(st, P, C);
        mj::ObjWriter w;
        w.str("id", id).str("strategy", P.strategy).integer("seed", (long long)s);
        if (v.has("job")) w.integer("job", v["job"].as_int());
        if (R.solved && !reaches_target(st, R.path)) {
          R.solved = false;
          R.note = "replay_mismatch";
        }
        w.boolean("solved", R.solved);
        if (R.solved) {
          w.integer("raw_len", (long long)R.path.size());
          if (do_shorten) {
            Ctx C2 = C;
            C2.t0 = std::chrono::steady_clock::now();
            R.path = shorten(st, R.path, S.eg, SP, C2);
          }
          w.integer("len", (long long)R.path.size()).ints("path", R.path);
        }
        if (P.strategy == "bidir") w.boolean("optimal", R.optimal).integer("lower_bound", R.lower_bound);
        w.integer("nodes", R.nodes).num("secs", C.elapsed()).str("note", R.note);
        return w.done();
      });
      return 0;
    }
    if (cmd == "shorten") {
      parallel_lines(lines, threads, [&](const std::string& l, int) {
        auto v = mj::parse(l);
        Params P = base;
        ShortenParams SP = sbase;
        if (v.has("params"))
          for (auto& [k, pv] : v["params"].o) set_param(P, SP, k, val_to_str(pv));
        State st = state_of(v);
        auto path = v["path"].as_ints();
        Ctx C;
        C.eg = &S.eg;
        C.t0 = std::chrono::steady_clock::now();
        bool valid = reaches_target(st, path);
        auto np = valid ? shorten(st, path, S.eg, SP, C) : path;
        mj::ObjWriter w;
        w.str("id", v["id"].as_str());
        if (v.has("job")) w.integer("job", v["job"].as_int());
        return w.boolean("valid", valid)
            .integer("before", (long long)path.size())
            .integer("after", (long long)np.size())
            .ints("path", np)
            .num("secs", C.elapsed())
            .done();
      });
      return 0;
    }
    if (cmd == "features") {
      parallel_lines(lines, threads, [&](const std::string& l, int) {
        auto v = mj::parse(l);
        State s = state_of(v);
        auto path = v["path"].as_ints();
        std::string X = "[", Y = "[";
        float f[NFEAT];
        for (size_t i = 0; i <= path.size(); ++i) {
          compute_features(s.r[0].data(), (int)s.r[0].size(), s.r[1].data(), (int)s.r[1].size(), &S.eg, f);
          if (i) X += ",", Y += ",";
          X += "[";
          for (int k = 0; k < NFEAT; ++k) X += (k ? "," : "") + std::to_string((int)f[k]);
          X += "]";
          Y += std::to_string(path.size() - i);
          if (i < path.size()) apply_move(s, path[i]);
        }
        return mj::ObjWriter().str("id", v["id"].as_str()).raw("X", X + "]").raw("y", Y + "]").done();
      });
      return 0;
    }
    fprintf(stderr, "unknown command %s\n", cmd.c_str());
    return 3;
  } catch (std::exception& e) {
    fprintf(stderr, "error: %s\n", e.what());
    return 2;
  }
}
