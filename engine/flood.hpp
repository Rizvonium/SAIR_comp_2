// Minimax flood over canonical classes (canon.hpp).
//
//   TrivialTable   the length-capped trivial component T_L: every class
//                  reachable from (x, y) through classes of total <= L,
//                  with its BFS distance to (x, y).  Built once
//                  (`acengine build-trivial`), stored as sorted compact keys
//                  (delta varints) + 16-bit distances.
//   CanonCorridor  classes of the states on known solution paths (other
//                  problems' corridors), for splicing.
//   flood          from the start class, always expand the frontier class of
//                  lowest total; raise the water level by one letter only
//                  when the whole sublevel component is exhausted.  Stops on
//                  touching T, a class with a one-letter relator (greedy
//                  descent finishes it), or a corridor class.  Exhausting a
//                  level without a hit proves that no exact AC path peaks
//                  at or below it (exact length >= class length, every
//                  exact move is class-preserving or a generalized
//                  product), which gives barrier_lb.
//   compact_path   shortcut DP + bounded BFS within the found peak.
#pragma once
#include <chrono>
#include <cstdio>
#include <mutex>
#include <thread>

#include "canon.hpp"
#include "corridor.hpp"

namespace ac {
namespace canon {

// ---------------------------------------------------------------------
struct TrivialTable {
  int L = -1;
  HashMap map;  // mix64(compact64(key)) -> BFS distance to (x, y)
  bool loaded() const { return L >= 0; }
  size_t size() const { return map.size(); }

  int dist(const CKey& k) const {
    if (L < 0) return k == trivial_key() ? 0 : -1;
    if (k.total() > L) return -1;
    const uint32_t* v = map.find(mix64(compact64(k)));
    return v ? (int)*v : -1;
  }

  // Layer-synchronous BFS from (x, y); children are generated in parallel
  // against the read-only visited set, then merged serially.
  void build(int cap, int threads, bool verbose = true) {
    if (cap > COMPACT_MAXT) throw std::runtime_error("build-trivial: cap must be <= 27");
    auto t0 = std::chrono::steady_clock::now();
    L = cap;
    map.reset(1 << 20);
    CKey st = trivial_key();
    map.insert(mix64(compact64(st)), 0);
    std::vector<uint64_t> cur = {compact64(st)}, nxt;
    if (threads < 1) threads = 1;
    for (int d = 1; !cur.empty(); ++d) {
      std::vector<std::vector<uint64_t>> out(threads);
      std::atomic<size_t> next{0};
      auto work = [&](int tid) {
        HashMap local(1 << 12);
        const size_t CH = 64;
        while (true) {
          size_t b = next.fetch_add(CH);
          if (b >= cur.size()) break;
          size_t e = std::min(cur.size(), b + CH);
          for (size_t q = b; q < e; ++q) {
            CKey k = from_compact64(cur[q]);
            neighbours_key(k, -1, cap, -1, [&](const CKey& k2, int, const EdgeInfo&) {
              uint64_t c = compact64(k2), h = mix64(c);
              if (map.find(h)) return;
              if (local.insert(h, 0)) out[tid].push_back(c);
            });
          }
        }
      };
      std::vector<std::thread> ts;
      for (int t = 0; t < threads; ++t) ts.emplace_back(work, t);
      for (auto& t : ts) t.join();
      nxt.clear();
      for (auto& o : out)
        for (uint64_t c : o)
          if (map.insert(mix64(c), (uint32_t)d)) nxt.push_back(c);
      cur.swap(nxt);
      if (verbose && !cur.empty())
        fprintf(stderr, "trivial cap %d: depth %d, %zu new, %zu total, %.1fs\n", cap, d, cur.size(), map.size(),
                std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
    }
  }

  // File: magic, cap, count, varint deltas of the sorted compact keys,
  // then count 16-bit distances in key order.
  void save(const std::string& path) const {
    std::vector<std::pair<uint64_t, uint16_t>> all;
    all.reserve(map.size());
    for (size_t i = 0; i < map.keys.size(); ++i)
      if (map.keys[i]) all.push_back({unmix64(map.keys[i]), (uint16_t)std::min<uint32_t>(map.vals[i], 65535)});
    std::sort(all.begin(), all.end());
    FILE* f = fopen(path.c_str(), "wb");
    if (!f) throw std::runtime_error("cannot write " + path);
    uint64_t magic = 0x4143545249563031ULL, cap = L, n = all.size();
    fwrite(&magic, 8, 1, f);
    fwrite(&cap, 8, 1, f);
    fwrite(&n, 8, 1, f);
    std::vector<uint8_t> buf;
    uint64_t prev = 0;
    for (auto& [k, d] : all) {
      uint64_t delta = k - prev;
      prev = k;
      while (delta >= 0x80) buf.push_back((uint8_t)(delta | 0x80)), delta >>= 7;
      buf.push_back((uint8_t)delta);
    }
    uint64_t nb = buf.size();
    fwrite(&nb, 8, 1, f);
    fwrite(buf.data(), 1, buf.size(), f);
    for (auto& kd : all) fwrite(&kd.second, 2, 1, f);
    fclose(f);
  }

  bool load(const std::string& path) {
    FILE* f = fopen(path.c_str(), "rb");
    if (!f) return false;
    uint64_t magic, cap, n, nb;
    bool ok = fread(&magic, 8, 1, f) == 1 && magic == 0x4143545249563031ULL && fread(&cap, 8, 1, f) == 1 &&
              fread(&n, 8, 1, f) == 1 && fread(&nb, 8, 1, f) == 1;
    std::vector<uint8_t> buf;
    std::vector<uint16_t> dist;
    if (ok) {
      buf.resize(nb);
      dist.resize(n);
      ok = fread(buf.data(), 1, nb, f) == nb && fread(dist.data(), 2, n, f) == n;
    }
    fclose(f);
    if (!ok) return false;
    map.reset(n * 2 + 16);
    uint64_t prev = 0;
    size_t p = 0;
    for (size_t i = 0; i < n; ++i) {
      uint64_t delta = 0;
      int sh = 0;
      while (p < nb) {
        uint8_t b = buf[p++];
        delta |= (uint64_t)(b & 0x7f) << sh;
        sh += 7;
        if (!(b & 0x80)) break;
      }
      prev += delta;
      map.insert(mix64(prev), dist[i]);
    }
    L = (int)cap;
    return true;
  }

  // inverse of mix64 (for listing the stored keys)
  static uint64_t unmix64(uint64_t z) {
    z ^= z >> 31 ^ z >> 62;
    z *= 0x319642b2d24d8ec3ULL;
    z ^= z >> 27 ^ z >> 54;
    z *= 0x96de1b173f119089ULL;
    z ^= z >> 30 ^ z >> 60;
    return z;
  }
};

// ---------------------------------------------------------------------
// Classes of the states on stored solution paths (any problem's).
struct CanonCorridor {
  struct Entry {
    uint32_t path, idx, rem;
  };
  HashMap map;  // chash -> entry
  std::vector<Entry> entries;
  const Corridor* cor = nullptr;
  bool loaded() const { return cor != nullptr && !entries.empty(); }

  void build(const Corridor& c, int min_total = 6) {
    cor = &c;
    map.reset(1 << 16);
    entries.clear();
    for (uint32_t p = 0; p < c.paths.size(); ++p) {
      State s = c.starts[p];
      const auto& path = c.paths[p];
      for (uint32_t i = 0; i <= path.size(); ++i) {
        if (i) apply_move(s, path[i - 1]);
        if (i == path.size()) break;
        CKey k;
        if (!class_of(s, k) || k.total() < min_total) continue;
        uint32_t rem = (uint32_t)(path.size() - i);
        uint64_t h = chash(k);
        uint32_t* e = map.findm(h);
        if (!e) {
          map.insert(h, (uint32_t)entries.size());
          entries.push_back({p, i, rem});
        } else if (entries[*e].rem > rem)
          entries[*e] = {p, i, rem};
      }
    }
  }
  // entry for a class, ignoring paths owned by `exclude`
  const Entry* find(const CKey& k, uint64_t exclude) const {
    if (!cor) return nullptr;
    const uint32_t* e = map.find(chash(k));
    if (!e) return nullptr;
    const Entry& en = entries[*e];
    if (exclude && cor->owner[en.path] == exclude) return nullptr;
    return &en;
  }
};

// ---------------------------------------------------------------------
struct FloodParams {
  long long budget = 300000;  // visited classes
  int capmax = 0;             // max water level (0: start + 30)
  int umax = -1;              // max insertion length (-1: unbounded, rigorous)
  double time_limit = 60;     // seconds
  long long compact_budget = 200000;  // BFS compaction budget (classes)
  int compact_slack = 0;      // compaction cap = peak + slack
};

enum HitKind { HIT_NONE = 0, HIT_TRIVIAL = 1, HIT_ONE = 2, HIT_CORRIDOR = 3 };

struct FloodResult {
  int kind = HIT_NONE;
  std::vector<CKey> path;  // canonical path start .. end (trivial class, or corridor class)
  const CanonCorridor::Entry* cor = nullptr;
  int water = 0, barrier_lb = 0, flood_steps = 0;
  bool exhausted = false;
  long long visited = 0, expanded = 0;
  CKey minkey = KMAX;
  std::string note;
};

inline int path_peak(const std::vector<CKey>& p) {
  int m = 0;
  for (auto& k : p) m = std::max(m, k.total());
  return m;
}

// Descend through T by BFS distance (appends to path, from path.back()).
inline bool descend_T(std::vector<CKey>& path, const TrivialTable& T) {
  CKey cur = path.back();
  int d = T.dist(cur);
  if (d < 0) return false;
  int cap = T.loaded() ? T.L : 2;
  while (d > 0) {
    CKey nx;
    bool found = false;
    neighbours_key(cur, -1, cap, -1, [&](const CKey& k2, int, const EdgeInfo&) {
      if (!found && T.dist(k2) == d - 1) nx = k2, found = true;
    });
    if (!found) return false;
    path.push_back(nx);
    cur = nx;
    --d;
  }
  return true;
}

// Greedy descent from a class with a one-letter relator: every step lowers
// the total by one when the presented group is trivial.  Stops at T.
inline bool descend_one(std::vector<CKey>& path, const TrivialTable& T) {
  CKey cur = path.back();
  const CKey triv = trivial_key();
  while (!(cur == triv) && T.dist(cur) < 0) {
    if (cur.n0() != 1) return false;
    CKey best = KMAX;
    int bt = 1 << 30;
    neighbours_key(cur, -1, cur.total() - 1, 0, [&](const CKey& k2, int t, const EdgeInfo&) {
      if (k2.n0() == 1 && (t < bt || (t == bt && k2 < best))) bt = t, best = k2;
    });
    if (bt >= cur.total()) return false;
    path.push_back(best);
    cur = best;
  }
  return T.dist(cur) < 0 ? true : descend_T(path, T);
}

inline FloodResult flood(const CKey& start, const FloodParams& FP, const TrivialTable& T, const CanonCorridor* CC,
                         uint64_t self) {
  using clk = std::chrono::steady_clock;
  auto t0 = clk::now();
  FloodResult R;
  const int st = start.total();
  int capmax = FP.capmax > 0 ? FP.capmax : st + 30;
  capmax = std::min(capmax, MAXT);
  struct FNode {
    CKey key;
    uint32_t parent;
    uint8_t ecap;
  };
  std::vector<FNode> nodes;
  HashMap seen(1 << 16);
  // fresh[t]: nodes not yet expanded; pend[t]: expanded nodes whose next
  // child above their cap has total t.
  std::vector<std::vector<uint32_t>> fresh(MAXT + 2), pend(MAXT + 2);
  std::vector<size_t> head(MAXT + 2, 0);
  int hit = -1;
  const CanonCorridor::Entry* hit_cor = nullptr;
  int hit_kind = HIT_NONE;

  auto classify = [&](const CKey& k) -> int {
    if (T.dist(k) >= 0) return HIT_TRIVIAL;
    if (k.n0() == 1) {
      std::vector<CKey> p = {k};
      if (descend_one(p, T)) return HIT_ONE;
    }
    if (CC && CC->loaded()) {
      const CanonCorridor::Entry* e = CC->find(k, self);
      if (e) {
        hit_cor = e;
        return HIT_CORRIDOR;
      }
    }
    return HIT_NONE;
  };
  auto add = [&](const CKey& k, uint32_t parent) {
    uint64_t h = chash(k);
    if (!seen.insert(h, (uint32_t)nodes.size())) return;
    uint32_t idx = (uint32_t)nodes.size();
    nodes.push_back({k, parent, 0});
    if (k.total() < R.minkey.total() || (k.total() == R.minkey.total() && k < R.minkey)) R.minkey = k;
    int c = classify(k);
    if (c != HIT_NONE) {
      hit = (int)idx;
      hit_kind = c;
      return;
    }
    fresh[k.total()].push_back(idx);
  };
  add(start, UINT32_MAX);
  int level = st;
  std::string stop = "exhausted";
  long long it = 0;
  while (hit < 0) {
    if ((long long)nodes.size() >= FP.budget) {
      stop = "budget";
      break;
    }
    if ((++it & 63) == 0 && std::chrono::duration<double>(clk::now() - t0).count() > FP.time_limit) {
      stop = "time";
      break;
    }
    // lowest non-empty fresh bucket
    int b = -1;
    for (int t = 2; t <= level; ++t)
      if (head[t] < fresh[t].size()) {
        b = t;
        break;
      }
    uint32_t idx;
    int lo;
    if (b >= 0) {
      idx = fresh[b][head[b]++];
      if (head[b] == fresh[b].size()) fresh[b].clear(), head[b] = 0;
      lo = -1;
    } else if (!pend[level].empty()) {
      idx = pend[level].back();
      pend[level].pop_back();
      lo = nodes[idx].ecap;
    } else {
      // sublevel component exhausted: raise the water level
      if (level >= capmax) {
        R.exhausted = true;
        break;
      }
      ++level;
      continue;
    }
    ++R.expanded;
    int thr = 1 << 30;
    CKey key = nodes[idx].key;
    neighbours_key(
        key, lo, level, FP.umax,
        [&](const CKey& k2, int, const EdgeInfo&) {
          if (hit < 0) add(k2, idx);
        },
        &thr);
    nodes[idx].ecap = (uint8_t)level;
    if (thr <= capmax) pend[thr].push_back(idx);
  }
  R.water = level;
  R.visited = (long long)nodes.size();
  if (hit < 0) {
    R.barrier_lb = R.exhausted ? capmax + 1 : level;
    if (FP.umax >= 0) R.barrier_lb = 0;  // incomplete move set: no proof
    R.note = stop;
    return R;
  }
  R.kind = hit_kind;
  R.cor = hit_kind == HIT_CORRIDOR ? hit_cor : nullptr;
  for (uint32_t x = (uint32_t)hit; x != UINT32_MAX; x = nodes[x].parent) R.path.push_back(nodes[x].key);
  std::reverse(R.path.begin(), R.path.end());
  R.flood_steps = (int)R.path.size() - 1;
  bool ok = true;
  if (hit_kind == HIT_TRIVIAL)
    ok = descend_T(R.path, T);
  else if (hit_kind == HIT_ONE)
    ok = descend_one(R.path, T);
  if (!ok) {
    R.kind = HIT_NONE;
    R.note = "descent_failed";
    R.path.clear();
  } else
    R.note = hit_kind == HIT_TRIVIAL ? "hit_T" : hit_kind == HIT_ONE ? "hit_one" : "hit_corridor";
  return R;
}

// ---------------------------------------------------------------------
// Path compaction.

// Shortcut DP along the path (unit steps): from each path class, jump to
// any later path class that is a neighbour (cap), or (unless fixed_end)
// into T, finishing with the BFS descent.
inline std::vector<CKey> shortcut_dp(const std::vector<CKey>& cur, const TrivialTable& T, bool fixed_end, int cap,
                                     int umax = 0) {
  const int n = (int)cur.size() - 1;
  if (n <= 1) return cur;
  HashMap pos(1 << 10);
  for (int j = 0; j <= n; ++j) {
    uint64_t h = chash(cur[j]);
    uint32_t* v = pos.findm(h);
    if (v)
      *v = (uint32_t)j;  // keep the last occurrence
    else
      pos.insert(h, (uint32_t)j);
  }
  std::vector<int> dist(n + 1, 1 << 30), from(n + 1, -1);
  dist[0] = 0;
  int best = 1 << 30, best_i = -1;
  bool best_child = false;
  CKey best_k;
  for (int i = 0; i < n; ++i) {
    if (dist[i] >= (1 << 30)) continue;
    if (!fixed_end) {
      int d0 = T.dist(cur[i]);
      if (d0 >= 0 && dist[i] + d0 < best) best = dist[i] + d0, best_i = i, best_child = false, best_k = cur[i];
    }
    neighbours_key(cur[i], -1, cap, umax, [&](const CKey& k2, int, const EdgeInfo&) {
      const uint32_t* v = pos.find(chash(k2));
      if (v && (int)*v > i && cur[*v] == k2 && dist[i] + 1 < dist[*v]) dist[*v] = dist[i] + 1, from[*v] = i;
      if (!fixed_end) {
        int d = T.dist(k2);
        if (d >= 0 && dist[i] + 1 + d < best) best = dist[i] + 1 + d, best_i = i, best_child = true, best_k = k2;
      }
    });
  }
  int end_i = n;
  std::vector<CKey> tail;
  if (dist[n] > best) {
    end_i = best_i;
    tail = {best_k};
    descend_T(tail, T);
    if (!best_child) tail.erase(tail.begin());
  }
  std::vector<CKey> out;
  for (int x = end_i; x >= 0; x = from[x]) {
    out.push_back(cur[x]);
    if (x == 0) break;
  }
  std::reverse(out.begin(), out.end());
  out.insert(out.end(), tail.begin(), tail.end());
  if (out.front() != cur.front() || out.size() >= cur.size()) return cur;
  return out;
}

// Bidirectional BFS a -> b through classes of total <= cap.  Returns a
// path with fewer than maxlen steps, or an empty vector.
inline std::vector<CKey> bidir_bfs(const CKey& a, const CKey& b, int cap, long long budget, double tlim,
                                   int maxlen, int umax = 0) {
  using clk = std::chrono::steady_clock;
  auto t0 = clk::now();
  std::vector<std::pair<CKey, uint32_t>> nd[2];
  HashMap seen[2] = {HashMap(1 << 12), HashMap(1 << 12)};
  nd[0].push_back({a, UINT32_MAX});
  nd[1].push_back({b, UINT32_MAX});
  seen[0].insert(chash(a), 0);
  seen[1].insert(chash(b), 0);
  if (a == b) return {a};
  size_t lb[2] = {0, 0}, le[2] = {1, 1};
  int depth[2] = {0, 0};
  long long it = 0;
  while (depth[0] + depth[1] + 1 < maxlen) {
    int sd = (le[0] - lb[0]) <= (le[1] - lb[1]) ? 0 : 1;
    if (lb[sd] >= le[sd]) return {};
    int meet_u = -1, meet_v = -1;
    for (size_t q = lb[sd]; q < le[sd] && meet_u < 0; ++q) {
      if ((long long)(nd[0].size() + nd[1].size()) > budget) return {};
      if ((++it & 31) == 0 && std::chrono::duration<double>(clk::now() - t0).count() > tlim) return {};
      CKey k = nd[sd][q].first;
      neighbours_key(k, -1, cap, umax, [&](const CKey& k2, int, const EdgeInfo&) {
        if (meet_u >= 0) return;
        uint64_t h = chash(k2);
        const uint32_t* o = seen[1 - sd].find(h);
        if (o && nd[1 - sd][*o].first == k2) {
          meet_u = (int)q, meet_v = (int)*o;
          return;
        }
        if (seen[sd].insert(h, (uint32_t)nd[sd].size())) nd[sd].push_back({k2, (uint32_t)q});
      });
    }
    if (meet_u >= 0) {
      // side sd: root .. node meet_u ; other side: node meet_v .. root
      std::vector<CKey> pa, pb;
      for (uint32_t x = (uint32_t)meet_u; x != UINT32_MAX; x = nd[sd][x].second) pa.push_back(nd[sd][x].first);
      std::reverse(pa.begin(), pa.end());
      for (uint32_t x = (uint32_t)meet_v; x != UINT32_MAX; x = nd[1 - sd][x].second) pb.push_back(nd[1 - sd][x].first);
      pa.insert(pa.end(), pb.begin(), pb.end());
      if (sd == 1) std::reverse(pa.begin(), pa.end());
      if ((int)pa.size() - 1 >= maxlen) return {};
      return pa;
    }
    lb[sd] = le[sd];
    le[sd] = nd[sd].size();
    ++depth[sd];
  }
  return {};
}

// Forward BFS from path[0] through classes of total <= cap; targets are
// the path classes (remaining = steps to the end) and, unless fixed_end,
// the classes of T (remaining = BFS distance).  Returns an improved path
// or an empty vector.
inline std::vector<CKey> forward_bfs(const std::vector<CKey>& cur, const TrivialTable& T, bool fixed_end, int cap,
                                     long long budget, double tlim, int umax = 0) {
  using clk = std::chrono::steady_clock;
  auto t0 = clk::now();
  const int n = (int)cur.size() - 1;
  HashMap pos(1 << 10);
  for (int j = 0; j <= n; ++j) {
    uint32_t* v = pos.findm(chash(cur[j]));
    if (v)
      *v = (uint32_t)j;
    else
      pos.insert(chash(cur[j]), (uint32_t)j);
  }
  std::vector<std::pair<CKey, uint32_t>> nodes;
  HashMap seen(1 << 12);
  nodes.push_back({cur[0], UINT32_MAX});
  seen.insert(chash(cur[0]), 0);
  int best = n, best_node = -1, best_kind = 0, best_j = 0;
  size_t lb = 0, le = 1;
  long long it = 0;
  bool stop = false;
  for (int depth = 0; lb < le && depth + 1 < best && !stop; ++depth) {
    for (size_t q = lb; q < le; ++q) {
      if ((long long)nodes.size() >= budget ||
          ((++it & 31) == 0 && std::chrono::duration<double>(clk::now() - t0).count() > tlim)) {
        stop = true;
        break;
      }
      CKey k = nodes[q].first;
      neighbours_key(k, -1, cap, umax, [&](const CKey& k2, int, const EdgeInfo&) {
        uint64_t h = chash(k2);
        if (!seen.insert(h, (uint32_t)nodes.size())) return;
        nodes.push_back({k2, (uint32_t)q});
        int dd = depth + 1;
        const uint32_t* v = pos.find(h);
        if (v && cur[*v] == k2 && dd + (n - (int)*v) < best)
          best = dd + (n - (int)*v), best_node = (int)nodes.size() - 1, best_kind = 0, best_j = (int)*v;
        if (!fixed_end) {
          int d = T.dist(k2);
          if (d >= 0 && dd + d < best) best = dd + d, best_node = (int)nodes.size() - 1, best_kind = 1;
        }
      });
    }
    lb = le;
    le = nodes.size();
  }
  if (best_node < 0 || best >= n) return {};
  std::vector<CKey> out;
  for (uint32_t x = (uint32_t)best_node; x != UINT32_MAX; x = nodes[x].second) out.push_back(nodes[x].first);
  std::reverse(out.begin(), out.end());
  if (best_kind == 0)
    out.insert(out.end(), cur.begin() + best_j + 1, cur.end());
  else if (!descend_T(out, T))
    return {};
  return out;
}

// `path` ends at the trivial class (or at a corridor class when
// fixed_end).  Plain AC' moves only (insertions are rarely shortcuts and
// cost 3^|w| per product).  1) shortcut DP, 2) forward BFS from the start
// to the path or into T, 3) bidirectional BFS between the start and the
// first class of T on the path (the end when fixed_end), 4) DP again.
// Budgets: classes per BFS stage and seconds.
inline std::vector<CKey> compact_path(const std::vector<CKey>& path, const TrivialTable& T, bool fixed_end,
                                      int slack, long long bfs_budget, double tlim = 10.0) {
  if (path.size() <= 2) return path;
  const int cap = std::min(MAXT, path_peak(path) + slack);
  std::vector<CKey> cur = shortcut_dp(path, T, fixed_end, cap);
  if (bfs_budget <= 0) return cur;
  std::vector<CKey> p = forward_bfs(cur, T, fixed_end, cap, bfs_budget, tlim / 2);
  if (!p.empty() && p.size() < cur.size()) cur = p;
  int e = (int)cur.size() - 1;
  if (!fixed_end)
    for (int j = 0; j < (int)cur.size(); ++j)
      if (T.dist(cur[j]) >= 0) {
        e = j;
        break;
      }
  if (e >= 2) {
    p = bidir_bfs(cur[0], cur[e], cap, bfs_budget, tlim / 2, e);
    if (!p.empty() && (int)p.size() - 1 < e) {
      p.insert(p.end(), cur.begin() + e + 1, cur.end());
      cur = p;
    }
  }
  return shortcut_dp(cur, T, fixed_end, cap);
}

}  // namespace canon
}  // namespace ac
