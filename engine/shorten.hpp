// Path shortening.
//
//   1. cycle cut: if a state repeats, drop the loop (this subsumes
//      cancelling adjacent inverse moves).
//   2. endgame truncation: from the earliest state in the endgame table,
//      use the exact shortest finish.
//   3. ball shortcuts ("window re-optimisation" over all windows at once):
//      every path state s_j gets a BFS ball of radius D2 stored in one map
//      u -> (j, b); then from each s_i a BFS ball of radius D1 looks up
//      those entries, giving shortcut edges s_i -> s_j of length a + b.
//      A forward DP picks the best combination of shortcuts and each chosen
//      shortcut is rebuilt exactly by bidirectional BFS (bridge()).
// Repeat until nothing improves.  The result is replayed and checked to
// reach the target before it is returned.
#pragma once
#include <optional>
#include <unordered_map>

#include "search.hpp"

namespace ac {

// BFS ball around s, up to radius r and at most max_nodes states.
inline void bfs_ball(const State& s, int r, Arena& A, HashMap& H, long long max_nodes = 50000000) {
  A.clear();
  H.reset(1 << 12);
  A.add(s.r[0].data(), (int)s.r[0].size(), s.r[1].data(), (int)s.r[1].size(), UINT32_MAX, 255, 0);
  H.insert(hash_state(s), 0);
  std::vector<Letter> buf;
  size_t b = 0, e = 1;
  for (int d = 1; d <= r; ++d) {
    for (size_t idx = b; idx < e; ++idx) {
      const Node nd = A.nodes[idx];
      buf.resize(nd.l0 + nd.l1 + 2);
      for (int m = 0; m < NUM_MOVES; ++m) {
        if (nd.move < NUM_MOVES && m == INVERSE[nd.move]) continue;
        const Letter* a0 = A.w0(idx);
        const Letter* a1 = A.w1(idx);
        int n = apply_into(m, a0, nd.l0, a1, nd.l1, buf.data());
        const Letter *b0 = a0, *b1 = a1;
        int n0 = nd.l0, n1 = nd.l1;
        if (TARGET_REL[m] == 0) b0 = buf.data(), n0 = n;
        else b1 = buf.data(), n1 = n;
        uint64_t h = hash_state(b0, n0, b1, n1);
        if (!H.insert(h, (uint32_t)A.nodes.size())) continue;
        A.add(b0, n0, b1, n1, (uint32_t)idx, m, d);
      }
      if ((long long)A.nodes.size() > max_nodes) return;
    }
    b = e;
    e = A.nodes.size();
  }
}

// Shortest path from s to t of length <= maxd (bidirectional BFS).
inline std::optional<std::vector<int>> bridge(const State& s, const State& t, int maxd) {
  uint64_t ht = hash_state(t);
  if (hash_state(s) == ht) return std::vector<int>{};
  Arena A[2];
  HashMap H[2];
  const State* src[2] = {&s, &t};
  size_t lb[2], le[2];
  int depth[2] = {0, 0};
  for (int k = 0; k < 2; ++k) {
    H[k].reset(1 << 12);
    A[k].add(src[k]->r[0].data(), (int)src[k]->r[0].size(), src[k]->r[1].data(), (int)src[k]->r[1].size(),
             UINT32_MAX, 255, 0);
    H[k].insert(hash_state(*src[k]), 0);
    lb[k] = 0;
    le[k] = 1;
  }
  std::vector<Letter> buf;
  while (depth[0] + depth[1] < maxd) {
    int k = (le[0] - lb[0] <= le[1] - lb[1]) ? 0 : 1;  // expand the smaller frontier
    ++depth[k];
    for (size_t idx = lb[k]; idx < le[k]; ++idx) {
      const Node nd = A[k].nodes[idx];
      buf.resize(nd.l0 + nd.l1 + 2);
      for (int m = 0; m < NUM_MOVES; ++m) {
        const Letter* a0 = A[k].w0(idx);
        const Letter* a1 = A[k].w1(idx);
        int n = apply_into(m, a0, nd.l0, a1, nd.l1, buf.data());
        const Letter *b0 = a0, *b1 = a1;
        int n0 = nd.l0, n1 = nd.l1;
        if (TARGET_REL[m] == 0) b0 = buf.data(), n0 = n;
        else b1 = buf.data(), n1 = n;
        uint64_t h = hash_state(b0, n0, b1, n1);
        uint32_t ni = (uint32_t)A[k].nodes.size();
        if (!H[k].insert(h, ni)) continue;
        A[k].add(b0, n0, b1, n1, (uint32_t)idx, m, depth[k]);
        const uint32_t* o = H[k ^ 1].find(h);
        if (o) {
          // forward part s->u, backward part u->t
          std::vector<int> pf = A[0].path_to(k == 0 ? ni : *o);
          std::vector<int> pb = A[1].path_to(k == 0 ? *o : ni);
          for (auto it = pb.rbegin(); it != pb.rend(); ++it) pf.push_back(INVERSE[*it]);
          return pf;
        }
      }
    }
    lb[k] = le[k];
    le[k] = A[k].nodes.size();
    if (lb[k] == le[k]) break;
  }
  return std::nullopt;
}

struct ShortenParams {
  int d1 = 4, d2 = 4;                  // ball radii
  long long ball_budget = 40000000;    // max total states stored in the j-balls map
  int max_rounds = 20;
  double time_limit = 60;
};

inline std::vector<State> states_along(const State& start, const std::vector<int>& path) {
  std::vector<State> st;
  st.reserve(path.size() + 1);
  st.push_back(start);
  State s = start;
  for (int m : path) {
    apply_move(s, m);
    st.push_back(s);
  }
  return st;
}

inline bool reaches_target(const State& start, const std::vector<int>& path) {
  State s = start;
  for (int m : path) apply_move(s, m);
  return is_target(s);
}

// Cycle cut + endgame truncation.
inline std::vector<int> cheap_shorten(const State& start, std::vector<int> path, const Endgame& eg,
                                      const Corridor* cor = nullptr, uint64_t self = 0) {
  path = cut_cycles(start, path);
  auto st = states_along(start, path);
  size_t best_i = path.size();
  size_t best_len = path.size();
  bool best_cor = false;
  for (size_t i = 0; i < st.size(); ++i) {
    int d = eg.dist(st[i]);
    if (d >= 0 && i + d < best_len) best_len = i + d, best_i = i, best_cor = false;
    if (cor) {
      const State& x = st[i];
      int c = cor->dist(x.r[0].data(), (int)x.r[0].size(), x.r[1].data(), (int)x.r[1].size(), self);
      if (c >= 0 && i + c < best_len) best_len = i + c, best_i = i, best_cor = true;
    }
  }
  if (best_len < path.size()) {
    auto fin = best_cor ? cor->finish(st[best_i], self) : eg.finish(st[best_i]);
    if (fin) {
      std::vector<int> np(path.begin(), path.begin() + best_i);
      np.insert(np.end(), fin->begin(), fin->end());
      if (reaches_target(start, np)) path = np;
    }
  }
  return path;
}

// One round of ball-shortcut DP.  Returns a strictly shorter path or the
// input unchanged.
inline std::vector<int> ball_round(const State& start, const std::vector<int>& path, const Endgame& eg,
                                   const ShortenParams& SP, Ctx& C) {
  auto st = states_along(start, path);
  const int n = (int)path.size();
  // pick radii that fit the budget (ball(r) ~ 12^r)
  int d2 = SP.d2;
  auto ballsz = [](int r) {
    long long s = 1, t = 1;
    for (int i = 0; i < r; ++i) t *= 12, s += t;
    return s;
  };
  while (d2 > 1 && ballsz(d2) * (long long)(n + 1) > SP.ball_budget) --d2;
  int d1 = SP.d1;
  while (d1 > 1 && ballsz(d1) * (long long)(n + 1) > SP.ball_budget * 4) --d1;

  HashMap M(1 << 16);  // u -> (j << 8 | b), maximizing j - b
  Arena A;
  HashMap H;
  for (int j = n; j >= 0; --j) {
    bfs_ball(st[j], d2, A, H);
    for (uint32_t k = 0; k < A.nodes.size(); ++k) {
      uint64_t h = hash_state(A.w0(k), A.nodes[k].l0, A.w1(k), A.nodes[k].l1);
      uint32_t v = ((uint32_t)j << 8) | A.nodes[k].depth;
      uint32_t* cur = M.findm(h);
      if (!cur) M.insert(h, v);
      else {
        int cj = *cur >> 8, cb = *cur & 0xff;
        if (j - (int)A.nodes[k].depth > cj - cb) *cur = v;
      }
    }
    if (C.elapsed() > SP.time_limit) return path;
  }
  // DP over path indices; edges i -> j (shortcut) and i -> END via endgame.
  const int INF = INT32_MAX / 2;
  std::vector<int> cost(n + 2, INF), from(n + 2, -1), wlen(n + 2, 0);
  const int END = n + 1;
  cost[0] = 0;
  for (int i = 0; i <= n; ++i) {
    if (cost[i] >= INF) continue;
    if (i < n && cost[i] + 1 < cost[i + 1]) cost[i + 1] = cost[i] + 1, from[i + 1] = i, wlen[i + 1] = -1;
    if (i == n) {
      if (cost[n] < cost[END]) cost[END] = cost[n], from[END] = n, wlen[END] = 0;
      continue;
    }
    bfs_ball(st[i], d1, A, H);
    for (uint32_t k = 0; k < A.nodes.size(); ++k) {
      int a = A.nodes[k].depth;
      const Letter* w0 = A.w0(k);
      const Letter* w1 = A.w1(k);
      int l0 = A.nodes[k].l0, l1 = A.nodes[k].l1;
      const uint32_t* v = M.find(hash_state(w0, l0, w1, l1));
      if (v) {
        int j = *v >> 8, b = *v & 0xff;
        int w = a + b;
        if (j > i && w < j - i && cost[i] + w < cost[j]) cost[j] = cost[i] + w, from[j] = i, wlen[j] = w;
      }
      int e = eg.dist(w0, l0, w1, l1);
      if (e >= 0 && cost[i] + a + e < cost[END]) cost[END] = cost[i] + a + e, from[END] = i, wlen[END] = a + e;
    }
    if (C.elapsed() > SP.time_limit) return path;
  }
  if (cost[END] >= n) return path;
  // reconstruct segments backwards
  std::vector<std::pair<int, int>> segs;  // (i, j) with j == END meaning finish
  for (int j = END; j != 0; j = from[j]) segs.push_back({from[j], j});
  std::reverse(segs.begin(), segs.end());
  std::vector<int> np;
  for (auto [i, j] : segs) {
    if (j == END) {
      if (i == n) continue;
      // reach a state with depth + dist == wlen, then finish exactly
      int target = wlen[END];
      bfs_ball(st[i], d1, A, H);
      bool ok = false;
      for (uint32_t k = 0; k < A.nodes.size() && !ok; ++k) {
        int e = eg.dist(A.w0(k), A.nodes[k].l0, A.w1(k), A.nodes[k].l1);
        if (e >= 0 && (int)A.nodes[k].depth + e == target) {
          auto fin = eg.finish(A.state(k));
          if (!fin) continue;
          auto p = A.path_to(k);
          np.insert(np.end(), p.begin(), p.end());
          np.insert(np.end(), fin->begin(), fin->end());
          ok = true;
        }
      }
      if (!ok) return path;
    } else if (wlen[j] == -1) {
      np.push_back(path[i]);
    } else {
      auto b = bridge(st[i], st[j], wlen[j]);
      if (!b) return path;
      np.insert(np.end(), b->begin(), b->end());
    }
  }
  if (np.size() < path.size() && reaches_target(start, np)) return np;
  return path;
}

// Shortening may splice onto any known path, including other paths of the
// same problem (self-exclusion only matters for search, where the problem's
// own stored path would be returned trivially); only strictly shorter
// results are ever accepted.
inline std::vector<int> shorten(const State& start, std::vector<int> path, const Endgame& eg,
                                const ShortenParams& SP, Ctx& C) {
  if (!reaches_target(start, path)) return path;
  path = cheap_shorten(start, path, eg, C.cor, 0);
  for (int round = 0; round < SP.max_rounds; ++round) {
    if (C.elapsed() > SP.time_limit) break;
    auto np = ball_round(start, path, eg, SP, C);
    if (np.size() >= path.size()) break;
    path = cheap_shorten(start, np, eg, C.cor, 0);
  }
  return path;
}

}  // namespace ac
