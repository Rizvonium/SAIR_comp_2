// Exact realization of a canonical class path as official moves.
//
// Each class step c_k -> c_{k+1} is matched on the *actual* exact state:
// peel r_t = h_t c_t h_t^-1, enumerate the generalized products of
// (c_0, c_1) whose class is c_{k+1} (so the B2 automorphisms and the
// relator order never need to be realized), and for each match
// r_i <- rot(c_i) w rot(c_j^e) w^-1 build the exact moves:
//   g_i: S_i = g_i a g_i^-1 (two choices), g_j likewise for b,
//   z = g_i w g_j^-1, split z = z1 z2 anywhere:
//   conjugate r_j by z2 and r_i by z1^-1 (single-letter moves 6..13,
//   innermost letter first), then one multiplication move (2..5),
//   optionally followed by cyclic reduction of both relators.
// The split chooses the common conjugator (the median split keeps it
// shortest); a beam over steps keeps the K cheapest exact states, scored
// by moves so far + lam * remaining conjugator length.  Every variant is
// simulated with apply_move and its class checked.
// The trivial class is finished by peeling and the endgame table (or the
// fixed 5-move relator swap); a corridor class is spliced onto the
// stored path transformed by the matching B2 automorphism / relator swap.
#pragma once
#include <optional>

#include "flood.hpp"

namespace ac {
namespace canon {

inline void emit_conj(int rel, const Word& z, std::vector<int>& mv) {
  for (int t = (int)z.size() - 1; t >= 0; --t) mv.push_back((rel == 0 ? 6 : 10) + code_of(z[t]));
}

inline void apply_all(State& s, const std::vector<int>& mv, size_t from = 0) {
  for (size_t q = from; q < mv.size(); ++q) apply_move(s, mv[q]);
}

struct RealizeParams {
  int beam = 8;
  double lam = 1.0;
};

struct BItem {
  State s;
  std::vector<int> mv;
  double score = 0;
};

inline int conj_len(const State& s) {
  int n = 0;
  for (int t = 0; t < 2; ++t) {
    const Word& r = s.r[t];
    int u = 0, m = (int)r.size();
    while (2 * u + 1 < m && r[u] == -r[m - 1 - u]) ++u;
    n += u;
  }
  return n;
}

// One class step for every beam item; returns the new beam (empty on failure).
inline std::vector<BItem> realize_step(const std::vector<BItem>& beam, const CKey& Kt, const RealizeParams& RP) {
  std::vector<BItem> cand;
  const int tot = Kt.total();
  for (const BItem& it : beam) {
    Word h[2], c[2];
    peel(it.s.r[0], h[0], c[0]);
    peel(it.s.r[1], h[1], c[1]);
    if (c[0].empty() || c[1].empty()) continue;
    std::vector<std::pair<EdgeInfo, Word>> edges;
    neighbours(c[0].data(), (int)c[0].size(), c[1].data(), (int)c[1].size(), tot - 1, tot, -1,
               [&](const CKey& k2, int, const EdgeInfo& e) {
                 if (k2 == Kt) edges.push_back({e, e.wl ? Word(e.w, e.w + e.wl) : Word()});
               });
    for (auto& [e, wv] : edges) {
      const int i = e.i, j = 1 - i;
      Word p(c[i].begin(), c[i].begin() + e.kr), q(c[i].begin() + e.kr, c[i].end());
      Word gi_opts[2] = {cat(h[i], p), cat(h[i], inv(q))};
      Word cj = e.s ? inv(c[j]) : c[j];
      Word p2(cj.begin(), cj.begin() + e.l), q2(cj.begin() + e.l, cj.end());
      Word gj_opts[2] = {cat(h[j], p2), cat(h[j], inv(q2))};
      for (auto& gi : gi_opts)
        for (auto& gj : gj_opts) {
          Word z = cat(cat(gi, wv), inv(gj));
          for (size_t k = 0; k <= z.size(); ++k) {
            Word z1(z.begin(), z.begin() + k), z2(z.begin() + k, z.end());
            std::vector<int> m;
            emit_conj(j, z2, m);
            emit_conj(i, inv(z1), m);
            m.push_back((i == 0 ? 2 : 4) + (e.s ? 1 : 0));
            State s2 = it.s;
            apply_all(s2, m);
            for (int red = 0; red < 2; ++red) {
              BItem b;
              b.s = s2;
              b.mv = it.mv;
              b.mv.insert(b.mv.end(), m.begin(), m.end());
              if (red) {
                size_t from = b.mv.size();
                for (int rel = 0; rel < 2; ++rel) {
                  Word hh, cc;
                  peel(b.s.r[rel], hh, cc);
                  emit_conj(rel, inv(hh), b.mv);
                }
                apply_all(b.s, b.mv, from);
                if (b.mv.size() == from) continue;  // same as red = 0
              }
              b.score = (double)b.mv.size() + RP.lam * conj_len(b.s);
              cand.push_back(std::move(b));
            }
          }
        }
    }
  }
  std::sort(cand.begin(), cand.end(), [](const BItem& a, const BItem& b) {
    return a.score != b.score ? a.score < b.score : a.mv.size() < b.mv.size();
  });
  std::vector<BItem> out;
  HashMap seen(1 << 8);
  for (auto& b : cand) {
    if ((int)out.size() >= RP.beam) break;
    if (!seen.insert(hash_state(b.s), 0)) continue;
    CKey k;
    if (!class_of(b.s, k) || !(k == Kt)) continue;  // sanity: never trust a variant blindly
    out.push_back(std::move(b));
  }
  return out;
}

// Shortest h (over the rotation matches) with reduce(h s h^-1) == t.
inline std::optional<Word> conj_word(const Word& s, const Word& t) {
  Word hs, cs, ht, ct;
  peel(s, hs, cs);
  peel(t, ht, ct);
  if (cs.size() != ct.size()) return std::nullopt;
  const size_t n = cs.size();
  std::optional<Word> best;
  for (size_t p = 0; p < std::max<size_t>(n, 1); ++p) {
    bool eq = true;
    for (size_t q = 0; q < n && eq; ++q) eq = cs[(p + q) % n] == ct[q];
    if (!eq) continue;
    Word d1 = inv(Word(cs.begin(), cs.begin() + p)), d2(cs.begin() + p, cs.end());
    for (const Word& d : {d1, d2}) {
      Word h = cat(cat(ht, d), inv(hs));
      if (best && h.size() >= best->size()) continue;
      if (cat(cat(h, s), inv(h)) == t) best = h;
    }
  }
  return best;
}

// Finish from a state of the trivial class: peel, then endgame (or the
// manual finish when no table is loaded).
inline std::optional<std::vector<int>> finish_trivial(const State& s0, const Endgame* eg) {
  State s = s0;
  std::vector<int> mv;
  for (int rel = 0; rel < 2; ++rel) {
    Word hh, cc;
    peel(s.r[rel], hh, cc);
    size_t from = mv.size();
    emit_conj(rel, inv(hh), mv);
    apply_all(s, mv, from);
  }
  if (eg && eg->loaded()) {
    auto f = eg->finish(s);
    if (f) {
      mv.insert(mv.end(), f->begin(), f->end());
      return mv;
    }
  }
  if (s.r[0].size() != 1 || s.r[1].size() != 1) return std::nullopt;
  if (s.r[0][0] < 0) mv.push_back(0);
  if (s.r[1][0] < 0) mv.push_back(1);
  if (std::abs(s.r[0][0]) == 2) {
    if (std::abs(s.r[1][0]) != 1) return std::nullopt;
    for (int m : {2, 5, 2, 9, 1}) mv.push_back(m);
  } else if (std::abs(s.r[1][0]) != 2)
    return std::nullopt;
  return mv;
}

// Image of move m under the automorphism k and relator relabelling sigma.
inline int transform_move(int m, int k, int sigma) {
  if (m <= 1) return m ^ sigma;
  if (m <= 5) {
    int i = TARGET_REL[m], invf = (m == 3 || m == 5);
    return ((i ^ sigma) == 0 ? 2 : 4) + invf;
  }
  int rel = m < 10 ? 0 : 1;
  Letter g = CONJ[(m - 6) & 3];
  return (((rel ^ sigma) == 0) ? 6 : 10) + code_of(phi(k, g));
}

// Splice exact state s (whose class equals the class of corridor state
// X = path p after idx moves) onto the transformed corridor path.
inline std::optional<std::vector<int>> splice_corridor(const State& s, const Corridor& cor, uint32_t p, uint32_t idx,
                                                       const Endgame* eg) {
  State X = cor.starts[p];
  const auto& path = cor.paths[p];
  for (uint32_t q = 0; q < idx; ++q) apply_move(X, path[q]);
  std::optional<std::vector<int>> best;
  for (int sigma = 0; sigma < 2; ++sigma)
    for (int k = 0; k < 8; ++k) {
      std::vector<int> mv;
      bool ok = true;
      for (int t = 0; t < 2 && ok; ++t) {
        Word target = X.r[t ^ sigma];
        for (auto& a : target) a = phi(k, a);
        std::optional<Word> h = conj_word(s.r[t], target);
        int invm = -1;
        if (!h) {
          h = conj_word(inv(s.r[t]), target);
          invm = t;
        }
        if (!h) {
          ok = false;
          break;
        }
        if (invm >= 0) mv.push_back(invm);
        emit_conj(t, *h, mv);
      }
      if (!ok) continue;
      if (best && mv.size() >= best->size()) continue;
      State s2 = s;
      apply_all(s2, mv);
      size_t from = mv.size();
      for (uint32_t q = idx; q < path.size(); ++q) mv.push_back(transform_move(path[q], k, sigma));
      apply_all(s2, mv, from);
      auto fin = finish_trivial(s2, eg);
      if (!fin) continue;
      mv.insert(mv.end(), fin->begin(), fin->end());
      if (!best || mv.size() < best->size()) best = mv;
    }
  return best;
}

// Realize a class path from the exact start.  The path ends at the trivial
// class, or (with ce) at a corridor class.
inline std::optional<std::vector<int>> realize_path(const State& start, const std::vector<CKey>& path,
                                                    const Endgame* eg, const Corridor* cor,
                                                    const CanonCorridor::Entry* ce, const RealizeParams& RP) {
  CKey k0;
  if (path.empty() || !class_of(start, k0) || !(k0 == path[0])) return std::nullopt;
  std::vector<BItem> beam(1);
  beam[0].s = start;
  for (size_t t = 1; t < path.size(); ++t) {
    beam = realize_step(beam, path[t], RP);
    if (beam.empty()) return std::nullopt;
  }
  std::optional<std::vector<int>> best;
  for (auto& b : beam) {
    std::optional<std::vector<int>> fin;
    if (ce) {
      if (!cor) return std::nullopt;
      fin = splice_corridor(b.s, *cor, ce->path, ce->idx, eg);
    } else
      fin = finish_trivial(b.s, eg);
    if (!fin) continue;
    std::vector<int> mv = b.mv;
    mv.insert(mv.end(), fin->begin(), fin->end());
    if (best && mv.size() >= best->size()) continue;
    auto rr = replay(start, mv);
    if (rr.ok_limits && is_target(rr.final)) best = mv;
  }
  return best;
}

}  // namespace canon
}  // namespace ac
