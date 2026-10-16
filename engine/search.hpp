// Search strategies.  Every strategy works on the same Arena/HashMap
// primitives and stops as soon as it touches the shared endgame table,
// whose exact shortest finish is then appended.
//
//   gbfs   greedy best-first search, key = score + lam * depth (+ noise)
//   beam   beam search of width W, dedup by a global visited set
//   walk   greedy-random walks: argmin-length move with prob p, else random
//   anneal simulated annealing walks (Metropolis on total length)
//   bidir  forward BFS to radius F meeting the endgame table (radius B):
//          exact optimum whenever the optimum is <= F + B
#pragma once
#include <chrono>
#include <cmath>
#include <queue>
#include <random>

#include "corridor.hpp"
#include "features.hpp"
#include "realize.hpp"

namespace ac {

struct Params {
  std::string strategy = "gbfs";
  long long max_nodes = 2000000;
  double time_limit = 10.0;  // seconds per problem
  int maxlen = 0;            // cap on total relator length during search (0 = 10000)
  double lam = 0.0;          // depth weight in the score
  double noise = 0.0;        // uniform noise amplitude added to scores
  int beam_width = 1000;
  int max_depth = 5000;
  double p_greedy = 0.8;
  int walk_len = 400;
  double T0 = 1.5, T1 = 0.05;
  int bidir_fwd = 6;
  double w_len = 1.0, w_model = 0.0;  // score = w_len*total + w_cyc*cyclic + w_model*model
  // + w_tdist * (class distance to (x, y) in the trivial table): a lower bound
  // on the remaining moves (conjugation/inversion keep the class), so with
  // w_len = 0 and lam = 1 GBFS is weighted A*; classes outside the table
  // score t_unknown + (total - table cap)
  double w_tdist = 0.0, t_unknown = 40.0;
  double w_cyc = 0.0;                 // weight of the cyclically reduced total length
  double w_max = 0.0, w_min = 0.0;    // weights of the longer / shorter relator length
  int tie = 0;                        // GBFS tie-break: 0 random, 1 newest, 2 oldest
  int bound = 1 << 30;                // accept a solution only if shorter than this
  double eps = 0.0;                   // epsilon-GBFS: expand a random open node with prob eps
  bool self_corridor = false;         // let a problem use its own stored paths (path-guided re-search)
  bool stop_first = true;
  std::vector<std::vector<int>> macros;  // macro-moves, usable as single steps
  // cflood (canonical minimax flood): budget = max_nodes classes, capmax = maxlen
  int cu = -1;                     // max insertion length |w| (-1: unbounded; needed for barrier_lb)
  int cbeam = 8;                   // realization beam width
  double clam = 1.0;               // realization: weight of leftover conjugator length
  long long ccompact = 200000;     // BFS compaction budget (classes); 0 disables
  int cslack = 0;                  // compaction cap = found peak + cslack
  double cdual = 0.5;              // >0: also flood without the corridor (this fraction of the budget)
                                   // and keep the shorter realization (corridor donors are often long)
  double ctime = 10.0;             // compaction time limit (seconds)
};

struct SearchResult {
  bool solved = false;
  bool optimal = false;  // proven optimal (bidir)
  int lower_bound = 0;   // proven lower bound on the optimum (bidir)
  std::vector<int> path;
  long long nodes = 0;
  double secs = 0;
  std::string note;
  // cflood
  int water = -1, barrier_lb = -1, csteps = -1;
  bool via_corridor = false;
  std::string fingerprint;
};

struct Ctx {
  const Endgame* eg = nullptr;
  const Corridor* cor = nullptr;  // optional: other problems' solution paths
  uint64_t self = 0;              // owner hash of the problem being searched
  bool via_corridor = false;      // last successful finish came from the corridor table
  const MLP* mlp = nullptr;
  const canon::TrivialTable* triv = nullptr;    // canonical trivial component
  const canon::CanonCorridor* ccor = nullptr;   // classes of corridor states
  std::mt19937_64 rng;
  std::chrono::steady_clock::time_point t0;
  double elapsed() const {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  }
  double uni() { return std::uniform_real_distribution<double>(0, 1)(rng); }
};

// Applies atomic move or macro (code >= NUM_MOVES) to a word pair held in
// two scratch vectors.
struct Mover {
  std::vector<Letter> w[2], tmp;
  void load(const Letter* a0, int n0, const Letter* a1, int n1) {
    w[0].assign(a0, a0 + n0);
    w[1].assign(a1, a1 + n1);
  }
  void step(int m) {
    tmp.resize(w[0].size() + w[1].size() + 2);
    int n = apply_into(m, w[0].data(), (int)w[0].size(), w[1].data(), (int)w[1].size(), tmp.data());
    tmp.resize(n);
    w[TARGET_REL[m]].swap(tmp);
  }
  int total() const { return (int)(w[0].size() + w[1].size()); }
};

inline std::vector<int> expand_codes(const std::vector<int>& codes, const Params& P) {
  std::vector<int> out;
  for (int c : codes) {
    if (c < NUM_MOVES)
      out.push_back(c);
    else
      for (int m : P.macros[c - NUM_MOVES]) out.push_back(m);
  }
  return out;
}

inline double score_state(const Letter* a0, int n0, const Letter* a1, int n1, const Params& P, Ctx& C) {
  double s = P.w_len * (n0 + n1);
  if (P.w_cyc != 0) s += P.w_cyc * ((n0 - cyc_slack(a0, n0)) + (n1 - cyc_slack(a1, n1)));
  if (P.w_max != 0) s += P.w_max * std::max(n0, n1);
  if (P.w_min != 0) s += P.w_min * std::min(n0, n1);
  if (P.w_tdist != 0 && C.triv) {
    State st;
    st.r[0].assign(a0, a0 + n0);
    st.r[1].assign(a1, a1 + n1);
    canon::CKey k;
    int d = canon::class_of(st, k) ? C.triv->dist(k) : -1;
    s += P.w_tdist * (d >= 0 ? d : P.t_unknown + std::max(0, n0 + n1 - C.triv->L));
  }
  if (P.w_model != 0 && C.mlp && C.mlp->loaded()) {
    float f[NFEAT];
    compute_features(a0, n0, a1, n1, C.eg, f);
    s += P.w_model * C.mlp->eval(f);
  }
  return s;
}

inline int cap_of(const Params& P) { return P.maxlen > 0 ? P.maxlen : 10000; }

// Try to finish from a state; returns true and fills `fin` on success.
inline bool try_finish(const Letter* a0, int n0, const Letter* a1, int n1, Ctx& C, std::vector<int>& fin) {
  bool in_eg = C.eg->dist(a0, n0, a1, n1) >= 0;
  bool in_cor = !in_eg && C.cor && C.cor->dist(a0, n0, a1, n1, C.self) >= 0;
  if (!in_eg && !in_cor) return false;
  State s;
  s.r[0].assign(a0, a0 + n0);
  s.r[1].assign(a1, a1 + n1);
  auto f = in_eg ? C.eg->finish(s) : C.cor->finish(s, C.self);
  if (!f) return false;
  fin = *f;
  C.via_corridor = in_cor;
  return true;
}

// -------------------------------------------------------------------------
// Compact storage for GBFS: words packed 2 bits per letter, a key-only hash
// set and 8-byte heap items (~50 bytes/node instead of ~110).
struct PackedArena {
  struct PNode {
    uint32_t off, parent;
    uint16_t l0, l1, depth;
    uint8_t move;
  };
  std::vector<uint8_t> bytes;
  std::vector<PNode> nodes;
  static constexpr Letter DEC[4] = {1, -1, 2, -2};
  bool full() const { return bytes.size() > 0xF0000000ULL; }
  uint32_t add(const Letter* a0, int n0, const Letter* a1, int n1, uint32_t parent, int move, int depth) {
    PNode nd{(uint32_t)bytes.size(), parent, (uint16_t)n0, (uint16_t)n1, (uint16_t)depth, (uint8_t)move};
    size_t at = bytes.size();
    bytes.resize(at + (n0 + n1 + 3) / 4, 0);
    uint8_t* b = bytes.data() + at;
    int k = 0;
    for (int i = 0; i < n0; ++i, ++k) b[k >> 2] |= (uint8_t)(code2(a0[i]) << ((k & 3) * 2));
    for (int i = 0; i < n1; ++i, ++k) b[k >> 2] |= (uint8_t)(code2(a1[i]) << ((k & 3) * 2));
    nodes.push_back(nd);
    return (uint32_t)(nodes.size() - 1);
  }
  // decode node i into out (r0 then r1 contiguous)
  void get(uint32_t i, Letter* out) const {
    const PNode& nd = nodes[i];
    const uint8_t* b = bytes.data() + nd.off;
    int n = nd.l0 + nd.l1;
    for (int k = 0; k < n; ++k) out[k] = DEC[(b[k >> 2] >> ((k & 3) * 2)) & 3];
  }
  std::vector<int> path_to(uint32_t i) const {
    std::vector<int> p;
    while (nodes[i].parent != UINT32_MAX) {
      p.push_back(nodes[i].move);
      i = nodes[i].parent;
    }
    std::reverse(p.begin(), p.end());
    return p;
  }
};

struct HashSet {
  std::vector<uint64_t> keys;
  size_t mask = 0, count = 0;
  explicit HashSet(size_t cap = 1 << 16) {
    size_t c = 16;
    while (c < cap) c <<= 1;
    keys.assign(c, 0);
    mask = c - 1;
  }
  bool insert(uint64_t k) {
    if ((count + 1) * 10 > keys.size() * 7) grow();
    size_t i = k & mask;
    while (true) {
      if (keys[i] == k) return false;
      if (keys[i] == 0) {
        keys[i] = k;
        ++count;
        return true;
      }
      i = (i + 1) & mask;
    }
  }
  void grow() {
    std::vector<uint64_t> old;
    old.swap(keys);
    keys.assign(old.size() * 2, 0);
    mask = keys.size() - 1;
    count = 0;
    for (uint64_t k : old)
      if (k) insert(k);
  }
};

inline SearchResult search_gbfs(const State& start, const Params& P, Ctx& C) {
  SearchResult R;
  std::vector<int> fin;
  if (try_finish(start.r[0].data(), (int)start.r[0].size(), start.r[1].data(), (int)start.r[1].size(), C,
                 fin) && (int)fin.size() < P.bound) {
    R.solved = true;
    R.path = fin;
    return R;
  }
  PackedArena A;
  HashSet H(1 << 16);
  A.add(start.r[0].data(), (int)start.r[0].size(), start.r[1].data(), (int)start.r[1].size(), UINT32_MAX, 255, 0);
  H.insert(hash_state(start));
  struct Item {
    float key;
    uint32_t idx;
  };
  // tie: 0 = random (tiny key noise), 1 = newest first, 2 = oldest first
  const int tie = P.tie;
  auto cmp = [tie](const Item& a, const Item& b) {
    if (a.key != b.key) return a.key > b.key;
    return tie == 2 ? a.idx > b.idx : a.idx < b.idx;
  };
  std::priority_queue<Item, std::vector<Item>, decltype(cmp)> pq(cmp);
  pq.push({0, 0});
  const int cap = cap_of(P);
  const int nm = NUM_MOVES + (int)P.macros.size();
  Mover mv;
  std::vector<Letter> cur, buf;
  long long expanded = 0;
  std::vector<bool> closed;
  while (!pq.empty() && (long long)A.nodes.size() < P.max_nodes) {
    if ((++expanded & 1023) == 0 && C.elapsed() > P.time_limit) {
      R.note = "time";
      break;
    }
    if (A.full()) {
      R.note = "memory";
      break;
    }
    uint32_t idx = UINT32_MAX;
    if (P.eps > 0 && C.uni() < P.eps) {  // epsilon-greedy: random open node
      for (int tries = 0; tries < 8 && idx == UINT32_MAX; ++tries) {
        uint32_t r = (uint32_t)(C.rng() % A.nodes.size());
        if (r >= closed.size() || !closed[r]) idx = r;
      }
    }
    if (idx == UINT32_MAX) {
      idx = pq.top().idx;
      pq.pop();
      if (idx < closed.size() && closed[idx]) continue;  // already expanded via a random pick
    }
    if (P.eps > 0) {
      if (closed.size() <= idx) closed.resize(A.nodes.size() + 1024, false);
      closed[idx] = true;
    }
    const auto nd = A.nodes[idx];
    cur.resize(nd.l0 + nd.l1 + 1);
    A.get(idx, cur.data());
    const Letter* a0 = cur.data();
    const Letter* a1 = cur.data() + nd.l0;
    for (int m = 0; m < nm; ++m) {
      if (m < NUM_MOVES && nd.move < NUM_MOVES && m == INVERSE[nd.move]) continue;
      const Letter *b0, *b1;
      int n0, n1;
      int dd = 1;
      if (m < NUM_MOVES) {
        buf.resize(nd.l0 + nd.l1 + 2);
        int n = apply_into(m, a0, nd.l0, a1, nd.l1, buf.data());
        if (TARGET_REL[m] == 0) b0 = buf.data(), n0 = n, b1 = a1, n1 = nd.l1;
        else b0 = a0, n0 = nd.l0, b1 = buf.data(), n1 = n;
      } else {
        mv.load(a0, nd.l0, a1, nd.l1);
        for (int am : P.macros[m - NUM_MOVES]) mv.step(am);
        b0 = mv.w[0].data(), n0 = (int)mv.w[0].size(), b1 = mv.w[1].data(), n1 = (int)mv.w[1].size();
        dd = (int)P.macros[m - NUM_MOVES].size();
      }
      if (n0 + n1 > cap) continue;
      if (!H.insert(hash_state(b0, n0, b1, n1))) continue;
      int depth = nd.depth + dd;
      uint32_t ni = A.add(b0, n0, b1, n1, idx, m, depth);
      if (try_finish(b0, n0, b1, n1, C, fin) && depth + (int)fin.size() < P.bound) {
        R.solved = true;
        R.path = expand_codes(A.path_to(ni), P);
        R.path.insert(R.path.end(), fin.begin(), fin.end());
        R.nodes = A.nodes.size();
        return R;
      }
      double key = score_state(b0, n0, b1, n1, P, C) + P.lam * depth;
      if (P.noise > 0) key += P.noise * C.uni();
      if (tie == 0) key += 1e-3 * C.uni();
      pq.push({(float)key, ni});
    }
  }
  R.nodes = A.nodes.size();
  if (R.note.empty()) R.note = pq.empty() ? "exhausted" : "nodes";
  return R;
}

// -------------------------------------------------------------------------
inline SearchResult search_beam(const State& start, const Params& P, Ctx& C) {
  SearchResult R;
  std::vector<int> fin;
  if (try_finish(start.r[0].data(), (int)start.r[0].size(), start.r[1].data(), (int)start.r[1].size(), C,
                 fin) && (int)fin.size() < P.bound) {
    R.solved = true;
    R.path = fin;
    return R;
  }
  Arena A, S;  // A: kept nodes; S: scratch children of the current level
  HashMap H(1 << 16);
  A.add(start.r[0].data(), (int)start.r[0].size(), start.r[1].data(), (int)start.r[1].size(), UINT32_MAX, 255, 0);
  H.insert(hash_state(start), 0);
  std::vector<uint32_t> beam = {0};
  const int cap = cap_of(P);
  const int nm = NUM_MOVES + (int)P.macros.size();
  Mover mv;
  std::vector<Letter> buf;
  std::vector<std::pair<float, uint32_t>> cand;
  HashMap level(1 << 12);
  long long generated = 0;
  for (int depth = 1; depth <= P.max_depth; ++depth) {
    S.clear();
    cand.clear();
    level.reset(std::max<size_t>(64, beam.size() * nm * 2));
    for (uint32_t idx : beam) {
      const Node nd = A.nodes[idx];
      for (int m = 0; m < nm; ++m) {
        if (m < NUM_MOVES && nd.move < NUM_MOVES && m == INVERSE[nd.move]) continue;
        const Letter* a0 = A.w0(idx);
        const Letter* a1 = A.w1(idx);
        const Letter *b0, *b1;
        int n0, n1;
        if (m < NUM_MOVES) {
          buf.resize(nd.l0 + nd.l1 + 2);
          int n = apply_into(m, a0, nd.l0, a1, nd.l1, buf.data());
          if (TARGET_REL[m] == 0) b0 = buf.data(), n0 = n, b1 = a1, n1 = nd.l1;
          else b0 = a0, n0 = nd.l0, b1 = buf.data(), n1 = n;
        } else {
          mv.load(a0, nd.l0, a1, nd.l1);
          for (int am : P.macros[m - NUM_MOVES]) mv.step(am);
          b0 = mv.w[0].data(), n0 = (int)mv.w[0].size(), b1 = mv.w[1].data(), n1 = (int)mv.w[1].size();
        }
        if (n0 + n1 > cap) continue;
        uint64_t h = hash_state(b0, n0, b1, n1);
        if (H.find(h) || !level.insert(h, 0)) continue;
        ++generated;
        uint32_t si = S.add(b0, n0, b1, n1, idx, m, depth);
        if (try_finish(b0, n0, b1, n1, C, fin) && depth + (int)fin.size() < P.bound) {
          std::vector<int> p = expand_codes(A.path_to(idx), P);
          std::vector<int> tail = expand_codes({m}, P);
          p.insert(p.end(), tail.begin(), tail.end());
          p.insert(p.end(), fin.begin(), fin.end());
          R.solved = true;
          R.path = p;
          R.nodes = generated;
          return R;
        }
        double sc = score_state(b0, n0, b1, n1, P, C);
        if (P.noise > 0) sc += P.noise * C.uni();
        cand.push_back({(float)sc, si});
      }
    }
    if (cand.empty()) {
      R.note = "exhausted";
      break;
    }
    if ((int)cand.size() > P.beam_width) {
      std::nth_element(cand.begin(), cand.begin() + P.beam_width, cand.end());
      cand.resize(P.beam_width);
    }
    beam.clear();
    for (auto& c : cand) {
      const Node& sn = S.nodes[c.second];
      uint32_t ni = A.add(S.w0(c.second), sn.l0, S.w1(c.second), sn.l1, sn.parent, sn.move, depth);
      H.insert(hash_state(A.w0(ni), sn.l0, A.w1(ni), sn.l1), ni);
      beam.push_back(ni);
    }
    if ((long long)A.nodes.size() > P.max_nodes) {
      R.note = "nodes";
      break;
    }
    if (C.elapsed() > P.time_limit) {
      R.note = "time";
      break;
    }
  }
  R.nodes = generated;
  return R;
}

// -------------------------------------------------------------------------
// Cheap cycle cut used inside walk strategies (full shortening is separate).
inline std::vector<int> cut_cycles(const State& start, const std::vector<int>& path) {
  std::vector<uint64_t> hs;
  State s = start;
  hs.push_back(hash_state(s));
  for (int m : path) {
    apply_move(s, m);
    hs.push_back(hash_state(s));
  }
  HashMap last(hs.size() * 2 + 16);
  for (size_t i = 0; i < hs.size(); ++i) {
    uint32_t* v = last.findm(hs[i]);
    if (v) *v = (uint32_t)i;
    else last.insert(hs[i], (uint32_t)i);
  }
  std::vector<int> out;
  size_t i = 0;
  while (i < path.size()) {
    size_t j = *last.find(hs[i]);
    if (j > i) {
      i = j;
      continue;
    }
    out.push_back(path[i]);
    ++i;
  }
  return out;
}

inline SearchResult search_walk(const State& start, const Params& P, Ctx& C, bool anneal) {
  SearchResult R;
  std::vector<int> fin;
  const int cap = cap_of(P);
  Mover mv;
  std::vector<Letter> cbuf[NUM_MOVES];
  int clen[NUM_MOVES];
  std::vector<int> path;
  long long steps = 0, walks = 0;
  while (C.elapsed() < P.time_limit && steps < P.max_nodes) {
    ++walks;
    mv.load(start.r[0].data(), (int)start.r[0].size(), start.r[1].data(), (int)start.r[1].size());
    path.clear();
    int last = -1;
    int cur = mv.total();
    for (int st = 0; st < P.walk_len; ++st) {
      ++steps;
      int m;
      if (anneal) {
        double T = P.T0 * std::pow(P.T1 / P.T0, (double)st / P.walk_len);
        do m = (int)(C.rng() % NUM_MOVES);
        while (last >= 0 && m == INVERSE[last]);
        auto& b = cbuf[m];
        b.resize(mv.total() + 2);
        int n = apply_into(m, mv.w[0].data(), (int)mv.w[0].size(), mv.w[1].data(), (int)mv.w[1].size(), b.data());
        int nt = cur - (int)mv.w[TARGET_REL[m]].size() + n;
        int dE = nt - cur;
        if (dE > 0 && C.uni() >= std::exp(-dE / T)) continue;
      } else {
        int best = INT32_MAX, nbest = 0;
        for (int k = 0; k < NUM_MOVES; ++k) {
          if (last >= 0 && k == INVERSE[last]) {
            clen[k] = INT32_MAX;
            continue;
          }
          auto& b = cbuf[k];
          b.resize(mv.total() + 2);
          int n = apply_into(k, mv.w[0].data(), (int)mv.w[0].size(), mv.w[1].data(), (int)mv.w[1].size(), b.data());
          clen[k] = cur - (int)mv.w[TARGET_REL[k]].size() + n;
          if (clen[k] < best) best = clen[k], nbest = 1;
          else if (clen[k] == best) ++nbest;
        }
        if (C.uni() < P.p_greedy) {
          int pick = (int)(C.rng() % nbest);
          m = 0;
          for (int k = 0; k < NUM_MOVES; ++k)
            if (clen[k] == best && pick-- == 0) {
              m = k;
              break;
            }
        } else {
          do m = (int)(C.rng() % NUM_MOVES);
          while (last >= 0 && m == INVERSE[last]);
        }
      }
      mv.step(m);
      path.push_back(m);
      last = m;
      cur = mv.total();
      if (cur > cap) break;
      if (try_finish(mv.w[0].data(), (int)mv.w[0].size(), mv.w[1].data(), (int)mv.w[1].size(), C, fin)) {
        std::vector<int> p = path;
        p.insert(p.end(), fin.begin(), fin.end());
        p = cut_cycles(start, p);
        if (!R.solved || p.size() < R.path.size()) {
          R.solved = true;
          R.path = p;
        }
        break;
      }
    }
    if (R.solved && P.stop_first) break;
  }
  R.nodes = steps;
  R.note = "walks=" + std::to_string(walks);
  return R;
}

// -------------------------------------------------------------------------
inline SearchResult search_bidir(const State& start, const Params& P, Ctx& C) {
  SearchResult R;
  const int B = C.eg->radius;
  Arena A;
  HashMap H(1 << 16);
  A.add(start.r[0].data(), (int)start.r[0].size(), start.r[1].data(), (int)start.r[1].size(), UINT32_MAX, 255, 0);
  H.insert(hash_state(start), 0);
  int best = INT32_MAX;
  uint32_t best_node = 0;
  int d0 = C.eg->dist(start);
  if (d0 >= 0) best = d0;
  std::vector<Letter> buf;
  size_t lvl_begin = 0, lvl_end = 1;
  int depth = 0;
  bool complete = true;
  const int cap = cap_of(P);
  while (depth < P.bidir_fwd && depth + 1 < best) {
    ++depth;
    for (size_t idx = lvl_begin; idx < lvl_end; ++idx) {
      const Node nd = A.nodes[idx];
      buf.resize(nd.l0 + nd.l1 + 2);
      for (int m = 0; m < NUM_MOVES; ++m) {
        const Letter* a0 = A.w0(idx);
        const Letter* a1 = A.w1(idx);
        int n = apply_into(m, a0, nd.l0, a1, nd.l1, buf.data());
        const Letter *b0 = a0, *b1 = a1;
        int n0 = nd.l0, n1 = nd.l1;
        if (TARGET_REL[m] == 0) b0 = buf.data(), n0 = n;
        else b1 = buf.data(), n1 = n;
        if (n0 + n1 > cap) {
          complete = false;
          continue;
        }
        uint64_t h = hash_state(b0, n0, b1, n1);
        uint32_t ni = (uint32_t)A.nodes.size();
        if (!H.insert(h, ni)) continue;
        A.add(b0, n0, b1, n1, (uint32_t)idx, m, depth);
        int d = C.eg->dist(A.w0(ni), n0, A.w1(ni), n1);
        if (d >= 0 && depth + d < best) {
          best = depth + d;
          best_node = ni;
        }
      }
      if ((long long)A.nodes.size() > P.max_nodes || ((idx & 255) == 0 && C.elapsed() > P.time_limit)) {
        complete = false;
        break;
      }
    }
    if (!complete) break;
    lvl_begin = lvl_end;
    lvl_end = A.nodes.size();
  }
  R.nodes = A.nodes.size();
  if (best != INT32_MAX) {
    State s = A.state(best_node);
    auto fin = C.eg->finish(s);
    if (fin) {
      R.solved = true;
      R.path = A.path_to(best_node);
      R.path.insert(R.path.end(), fin->begin(), fin->end());
      // optimal if every state within the searched radius was examined
      R.optimal = complete;
    }
  }
  // Fully expanded to `depth` with no hit => optimum > depth + B.
  R.lower_bound = complete ? (R.solved ? (int)R.path.size() : depth + B + 1) : 0;
  return R;
}

// Canonical minimax flood (flood.hpp), compaction, exact realization.
// `ccor` = corridor classes to stop at (nullptr: trivial table only).
inline SearchResult cflood_once(const State& start, const canon::CKey& k0, const Params& P, Ctx& C,
                                const canon::CanonCorridor* ccor, long long budget, double tlimit) {
  using namespace canon;
  SearchResult R;
  static const TrivialTable NOTABLE;
  const TrivialTable& T = C.triv ? *C.triv : NOTABLE;
  const double t0 = C.elapsed();
  FloodParams FP;
  FP.budget = budget;
  FP.capmax = P.maxlen;
  FP.umax = P.cu;
  FP.time_limit = tlimit;
  FloodResult F = flood(k0, FP, T, ccor, C.self);
  R.nodes = F.visited;
  R.water = F.water;
  R.barrier_lb = F.kind == HIT_NONE ? F.barrier_lb : -1;
  R.fingerprint = key_str(F.minkey);
  if (F.kind == HIT_NONE) {
    R.note = F.note + " water=" + std::to_string(F.water);
    return R;
  }
  const bool fixed_end = F.kind == HIT_CORRIDOR;
  const double tf = C.elapsed();
  std::vector<CKey> path = compact_path(F.path, T, fixed_end, P.cslack, P.ccompact, P.ctime);
  const double tc = C.elapsed();
  RealizeParams RP;
  RP.beam = P.cbeam;
  RP.lam = P.clam;
  const Endgame* eg = C.eg && C.eg->loaded() ? C.eg : nullptr;
  auto mv = realize_path(start, path, eg, C.cor, F.cor, RP);
  if (!mv && path.size() != F.path.size()) mv = realize_path(start, F.path, eg, C.cor, F.cor, RP);
  R.csteps = (int)path.size() - 1;
  char tbuf[96];
  snprintf(tbuf, sizeof tbuf, " t_flood=%.2f t_compact=%.2f t_realize=%.2f", tf - t0, tc - tf, C.elapsed() - tc);
  std::string info = F.note + " water=" + std::to_string(F.water) + " csteps=" + std::to_string(F.path.size() - 1) +
                     "->" + std::to_string(path.size() - 1) + " cpeak=" + std::to_string(path_peak(path)) + tbuf;
  if (!mv) {
    R.note = "realize_failed " + info;
    return R;
  }
  R.solved = true;
  R.path = *mv;
  R.via_corridor = fixed_end;
  R.note = info;
  return R;
}

inline SearchResult search_cflood(const State& start, const Params& P, Ctx& C) {
  using namespace canon;
  canon::CKey k0;
  if (!class_of(start, k0)) {
    SearchResult R;
    R.note = "too_long";
    return R;
  }
  const bool dual = P.cdual > 0 && C.ccor && C.ccor->loaded();
  SearchResult A, B;
  if (dual) {   // trivial-table finish only: usually much shorter than a corridor splice
    A = cflood_once(start, k0, P, C, nullptr, std::max(1LL, (long long)(P.max_nodes * P.cdual)),
                    P.time_limit * P.cdual);
    A.note = "[T] " + A.note;
  }
  B = cflood_once(start, k0, P, C, C.ccor, P.max_nodes, std::max(1.0, P.time_limit - C.elapsed()));
  SearchResult R = B;
  if (A.solved && (!B.solved || A.path.size() <= B.path.size())) {
    R = A;
    if (B.solved) R.note += " | corridor alt " + std::to_string(B.path.size());
  } else if (A.solved || dual) {
    R.note += " | " + (A.solved ? "[T] alt " + std::to_string(A.path.size()) : A.note);
  }
  R.nodes = A.nodes + B.nodes;
  if (!R.solved) R.barrier_lb = std::max(A.barrier_lb, B.barrier_lb);
  C.via_corridor = R.via_corridor;
  return R;
}

inline SearchResult run_search(const State& start, const Params& P, Ctx& C) {
  if (P.strategy == "cflood") return search_cflood(start, P, C);
  if (P.strategy == "gbfs") return search_gbfs(start, P, C);
  if (P.strategy == "beam") return search_beam(start, P, C);
  if (P.strategy == "walk") return search_walk(start, P, C, false);
  if (P.strategy == "anneal") return search_walk(start, P, C, true);
  if (P.strategy == "bidir") return search_bidir(start, P, C);
  throw std::runtime_error("unknown strategy " + P.strategy);
}

}  // namespace ac
