// Canonical classes of AC states and their neighbours ("AC'" moves).
//
// A class is an unordered pair of cyclic words taken up to rotation,
// inversion of each word, the relator order and the 8 signed permutations
// of {x, y} (the B2 automorphisms x <-> y, x -> x^-1, y -> y^-1).  Every
// exact state maps to the class of its cyclically reduced relators.
//
// Moves (generalized products): replace relator i by the cyclic reduction
// of rot(r_i) * w * rot(r_j^{+-1}) * w^-1.  With w empty this is the usual
// Havas-Ramsay AC' move; non-empty w are "irreducible insertions" (no
// cancellation at any junction; any cancelling w reduces to a shorter w),
// which add n_j + 2|w| letters.  Every exact move of ac.hpp is either
// class-preserving (inversion, conjugation) or such a product, so the
// class graph restricted to totals <= L contains the image of the exact
// graph restricted to totals <= L (exact length >= cyclic length).  This
// is what makes the barrier lower bounds of the flood rigorous.
//
// Keys: 2 bits per letter (x=0, X=1, y=2, Y=3), packed with the length of
// the first (shorter, or lexicographically smaller) word and the total, in
// 4 x 64 bits: totals up to MAXT = 120 letters.  Comparing keys compares
// (n0, total, letters) lexicographically.
#pragma once
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

#include "ac.hpp"

namespace ac {
namespace canon {

constexpr int MAXT = 120;  // largest representable class total

struct CKey {
  uint64_t w[4] = {0, 0, 0, 0};
  int n0() const { return (int)(w[0] >> 57); }
  int total() const { return (int)((w[0] >> 50) & 127); }
  int n1() const { return total() - n0(); }
  bool empty() const { return (w[0] | w[1] | w[2] | w[3]) == 0; }
  bool operator==(const CKey& o) const {
    return w[0] == o.w[0] && w[1] == o.w[1] && w[2] == o.w[2] && w[3] == o.w[3];
  }
  bool operator!=(const CKey& o) const { return !(*this == o); }
  bool operator<(const CKey& o) const {
    for (int k = 0; k < 4; ++k)
      if (w[k] != o.w[k]) return w[k] < o.w[k];
    return false;
  }
};
inline const CKey KMAX = [] {
  CKey k;
  for (auto& x : k.w) x = ~0ULL;
  return k;
}();

inline uint64_t chash(const CKey& k) {
  uint64_t h = mix64(k.w[0] ^ 0x243f6a8885a308d3ULL);
  h = mix64(h ^ k.w[1] ^ 0x13198a2e03707344ULL);
  h = mix64(h ^ k.w[2] ^ 0xa4093822299f31d0ULL);
  h = mix64(h ^ k.w[3]);
  return h ? h : 1;
}

inline int code_of(Letter a) { return a == 1 ? 0 : a == -1 ? 1 : a == 2 ? 2 : 3; }
constexpr Letter DECODE[4] = {1, -1, 2, -2};

// The 8 signed generator permutations.  Bit 0: swap x<->y, bit 1: invert
// the image of x, bit 2: invert the image of y.
struct Tables {
  Letter aut[8][5];      // aut[k][a + 2] = phi_k(a)
  uint8_t codek[8][5];   // code of phi_k(a)
  Tables() {
    for (int k = 0; k < 8; ++k) {
      int p = k & 1, sx = (k & 2) ? -1 : 1, sy = (k & 4) ? -1 : 1;
      Letter fx = (Letter)(sx * (p ? 2 : 1)), fy = (Letter)(sy * (p ? 1 : 2));
      aut[k][2] = 0;
      aut[k][3] = fx, aut[k][1] = (Letter)-fx, aut[k][4] = fy, aut[k][0] = (Letter)-fy;
      for (int a = -2; a <= 2; ++a)
        codek[k][a + 2] = a ? (uint8_t)code_of(aut[k][a + 2]) : 0;
    }
  }
};
inline const Tables TBL;
inline Letter phi(int k, Letter a) { return TBL.aut[k][a + 2]; }

// Start of the lexicographically least rotation of s2[0..n) (s2 holds the
// word twice).
inline const uint8_t* least_rot2(const uint8_t* s2, int n) {
  int i = 0, j = 1, k = 0;
  while (i < n && j < n && k < n) {
    uint8_t a = s2[i + k], b = s2[j + k];
    if (a == b)
      ++k;
    else {
      if (a > b)
        i += k + 1;
      else
        j += k + 1;
      if (i == j) ++j;
      k = 0;
    }
  }
  return s2 + (i < j ? i : j);
}

// Lazily computed canonical cyclic codes of one word under each of the 8
// automorphisms (min over rotations of phi(w) and phi(w)^-1).
struct Canon8 {
  uint8_t c[8][MAXT + 8];
  int n = 0;
  uint8_t done = 0;
  const Letter* w = nullptr;
  void init(const Letter* word, int len) {
    w = word, n = len, done = 0;
  }
  const uint8_t* get(int k) {
    if (!(done >> k & 1)) {
      uint8_t f[2 * MAXT + 16], g[2 * MAXT + 16];
      const uint8_t* ck = TBL.codek[k];
      for (int t = 0; t < n; ++t) {
        f[t] = f[t + n] = ck[w[t] + 2];
        g[t] = g[t + n] = ck[-w[n - 1 - t] + 2];
      }
      const uint8_t* r1 = least_rot2(f, n);
      const uint8_t* r2 = least_rot2(g, n);
      memcpy(c[k], memcmp(r2, r1, n) < 0 ? r2 : r1, n);
      done |= (uint8_t)(1u << k);
    }
    return c[k];
  }
};

inline void put_code(CKey& key, int pos, uint8_t c) {
  if (pos < 25)
    key.w[0] |= (uint64_t)c << (48 - 2 * pos);
  else {
    int q = pos - 25;
    key.w[1 + q / 32] |= (uint64_t)c << (62 - 2 * (q % 32));
  }
}
inline uint8_t get_code(const CKey& key, int pos) {
  if (pos < 25) return (uint8_t)((key.w[0] >> (48 - 2 * pos)) & 3);
  int q = pos - 25;
  return (uint8_t)((key.w[1 + q / 32] >> (62 - 2 * (q % 32))) & 3);
}

inline CKey pack(const uint8_t* a, int na, const uint8_t* b, int nb) {
  CKey key;
  key.w[0] = ((uint64_t)na << 57) | ((uint64_t)(na + nb) << 50);
  for (int t = 0; t < na; ++t) put_code(key, t, a[t]);
  for (int t = 0; t < nb; ++t) put_code(key, na + t, b[t]);
  return key;
}

inline void unpack(const CKey& key, Letter* w0, int& n0, Letter* w1, int& n1) {
  n0 = key.n0();
  n1 = key.total() - n0;
  for (int t = 0; t < n0; ++t) w0[t] = DECODE[get_code(key, t)];
  for (int t = 0; t < n1; ++t) w1[t] = DECODE[get_code(key, n0 + t)];
}

inline bool key_less(const CKey& a, const CKey& b) { return a < b; }

// Canonical key of the pair (R, B) of cyclically reduced words.
inline CKey combine(Canon8& R, Canon8& B) {
  Canon8* S = &R;
  Canon8* T = &B;
  if (B.n < R.n) std::swap(S, T);
  const int nS = S->n, nT = T->n;
  CKey best = KMAX;
  if (nS != nT) {
    int cand[8], nc = 0;
    const uint8_t* bc = nullptr;
    for (int k = 0; k < 8; ++k) {
      const uint8_t* c = S->get(k);
      int cmp = bc ? memcmp(c, bc, nS) : -1;
      if (cmp < 0)
        bc = c, nc = 0, cand[nc++] = k;
      else if (cmp == 0)
        cand[nc++] = k;
    }
    for (int q = 0; q < nc; ++q) {
      CKey k2 = pack(S->c[cand[q]], nS, T->get(cand[q]), nT);
      if (k2 < best) best = k2;
    }
    return best;
  }
  for (int k = 0; k < 8; ++k) {
    const uint8_t* c0 = R.get(k);
    const uint8_t* c1 = B.get(k);
    bool f0 = memcmp(c0, c1, nS) <= 0;
    CKey k2 = f0 ? pack(c0, nS, c1, nT) : pack(c1, nT, c0, nS);
    if (k2 < best) best = k2;
  }
  return best;
}

// Both words must be cyclically reduced and non-empty, total <= MAXT.
inline CKey canon_pair(const Letter* w0, int n0, const Letter* w1, int n1) {
  Canon8 A, B;
  A.init(w0, n0);
  B.init(w1, n1);
  return combine(A, B);
}

// ---------------------------------------------------------------------
// Word helpers on exact (freely reduced) words.
inline Word inv(const Word& w) {
  Word r(w.rbegin(), w.rend());
  for (auto& a : r) a = (Letter)-a;
  return r;
}
inline Word cat(const Word& a, const Word& b) {
  Word r = a;
  r.insert(r.end(), b.begin(), b.end());
  return free_reduce(r);
}
// r (freely reduced) = h c h^-1 with c cyclically reduced.
inline void peel(const Word& r, Word& h, Word& c) {
  int n = (int)r.size(), u = 0;
  while (2 * u + 1 < n && r[u] == -r[n - 1 - u]) ++u;
  h.assign(r.begin(), r.begin() + u);
  c.assign(r.begin() + u, r.end() - u);
}
inline Word cyc_core(const Word& r) {
  Word h, c;
  peel(r, h, c);
  return c;
}

// Class of an exact state (relators freely reduced).  Returns false if a
// relator is trivial or the total exceeds MAXT.
inline bool class_of(const State& s, CKey& out) {
  Word c0 = cyc_core(s.r[0]), c1 = cyc_core(s.r[1]);
  if (c0.empty() || c1.empty() || (int)(c0.size() + c1.size()) > MAXT) return false;
  out = canon_pair(c0.data(), (int)c0.size(), c1.data(), (int)c1.size());
  return true;
}

inline std::string key_str(const CKey& k) {
  static const char* L = "xXyY";
  std::string s;
  int n0 = k.n0(), t = k.total();
  for (int p = 0; p < t; ++p) {
    if (p == n0) s += '_';
    s += L[get_code(k, p)];
  }
  return s;
}

inline CKey trivial_key() {
  const Letter x = 1, y = 2;
  return canon_pair(&x, 1, &y, 1);
}

// Compact 64-bit form for totals <= 27 (the trivial component table).
// Injective on keys; never 0.
constexpr int COMPACT_MAXT = 27;
inline uint64_t compact64(const CKey& k) {
  int n0 = k.n0(), t = k.total();
  uint64_t c = ((uint64_t)n0 << 59) | ((uint64_t)t << 54);
  for (int p = 0; p < t; ++p) c |= (uint64_t)get_code(k, p) << (52 - 2 * p);
  return c;
}
inline CKey from_compact64(uint64_t c) {
  int n0 = (int)(c >> 59), t = (int)((c >> 54) & 31);
  uint8_t codes[COMPACT_MAXT];
  for (int p = 0; p < t; ++p) codes[p] = (uint8_t)((c >> (52 - 2 * p)) & 3);
  return pack(codes, n0, codes + n0, t - n0);
}

// ---------------------------------------------------------------------
// Neighbours.
struct EdgeInfo {
  int i;            // relator replaced
  int kr;           // a = rot_kr(c_i)
  int s;            // 1: multiply by the inverse of c_j
  int l;            // b = rot_l(c_j^{+-1})
  int wl;           // |w|
  const Letter* w;  // conjugator word (irreducible insertion), may be null
};

namespace detail {
struct WEnum {
  const Letter* a;
  const Letter* b;
  int nA, nB, lenlo, lenhi;
  Letter ws[MAXT];
  Letter red[2 * MAXT + 8];
};
template <class F>
inline void wrec(WEnum& E, int len, Canon8& CB, const EdgeInfo& base, F& emit) {
  if (len >= E.lenlo && len >= 1 && E.ws[len - 1] != -E.b[0] && E.ws[len - 1] != E.b[E.nB - 1]) {
    int mm = 0;
    for (int q = 0; q < E.nA; ++q) E.red[mm++] = E.a[q];
    for (int q = 0; q < len; ++q) E.red[mm++] = E.ws[q];
    for (int q = 0; q < E.nB; ++q) E.red[mm++] = E.b[q];
    for (int q = len - 1; q >= 0; --q) E.red[mm++] = (Letter)-E.ws[q];
    Canon8 CR;
    CR.init(E.red, mm);
    EdgeInfo e = base;
    e.wl = len;
    e.w = E.ws;
    emit(combine(CR, CB), mm + E.nB, e);
  }
  if (len == E.lenhi) return;
  static const Letter LET[4] = {1, -1, 2, -2};
  const Letter prev = E.ws[len > 0 ? len - 1 : 0];
  for (Letter c : LET) {
    if (len == 0 && (c == -E.a[E.nA - 1] || c == E.a[0])) continue;
    if (len > 0 && c == -prev) continue;
    E.ws[len] = c;
    wrec(E, len + 1, CB, base, emit);
  }
}
}  // namespace detail

// Emits emit(key, total, EdgeInfo) for every neighbour class with
// lo < total <= cap (duplicates possible).  W0/W1 must be cyclically
// reduced.  umax bounds |w| (-1: unbounded, as the cap allows).  If thr is
// given, it is lowered to a lower bound of the smallest child total > cap.
template <class F>
inline void neighbours(const Letter* W0, int N0, const Letter* W1, int N1, int lo, int cap, int umax, F&& emit,
                       int* thr = nullptr) {
  if (cap > MAXT) cap = MAXT;
  const Letter* w[2] = {W0, W1};
  int n[2] = {N0, N1};
  Letter red[2 * MAXT + 8];
  Letter AA[2 * MAXT + 8], BB[2][2 * MAXT + 8];
  for (int i = 0; i < 2; ++i) {
    const Letter* A = w[i];
    const Letter* B = w[1 - i];
    const int nA = n[i], nB = n[1 - i];
    Canon8 CB;
    CB.init(B, nB);
    for (int t = 0; t < 2 * nA; ++t) AA[t] = A[t % nA];
    for (int t = 0; t < 2 * nB; ++t) BB[0][t] = B[t % nB], BB[1][t] = (Letter)-B[nB - 1 - (t % nB)];
    int Wmax = (cap - nA - 2 * nB) >= 0 ? (cap - nA - 2 * nB) / 2 : -1;
    int Wtop = Wmax;
    if (umax >= 0 && Wtop > umax) Wtop = umax;
    if (thr) {
      // smallest insertion child above the cap (a lower bound)
      int nl = Wmax + 1 < 1 ? 1 : Wmax + 1;
      if (umax < 0 || nl <= umax) {
        int t2 = nA + 2 * nB + 2 * nl;
        if (t2 > cap && t2 < *thr) *thr = t2;
      }
    }
    // insertion lengths whose children are above lo
    int lenlo = 1;
    while (nA + 2 * nB + 2 * lenlo <= lo) ++lenlo;
    for (int kr = 0; kr < nA; ++kr) {
      const Letter* a = AA + kr;
      for (int s = 0; s < 2; ++s)
        for (int l = 0; l < nB; ++l) {
          const Letter* b = BB[s] + l;
          int t = 0;
          while (t < nA && t < nB && a[nA - 1 - t] == -b[t]) ++t;
          int m = nA + nB - 2 * t;
          if (m > 0) {
            int pa = nA - t;
            int u = 0;
            while (2 * u + 1 < m) {
              Letter f = u < pa ? a[u] : b[t + u - pa];
              int j = m - 1 - u;
              Letter e = j < pa ? a[j] : b[t + j - pa];
              if (f != -e) break;
              ++u;
            }
            int fm = m - 2 * u;
            int tot = fm + nB;
            if (tot <= cap) {
              if (tot > lo) {
                for (int q = 0; q < fm; ++q) {
                  int j = u + q;
                  red[q] = j < pa ? a[j] : b[t + j - pa];
                }
                Canon8 CR;
                CR.init(red, fm);
                EdgeInfo e{i, kr, s, l, 0, nullptr};
                emit(combine(CR, CB), tot, e);
              }
            } else if (thr && tot < *thr)
              *thr = tot;
          }
          if (Wtop >= 1 && lenlo <= Wtop) {
            detail::WEnum E;
            E.a = a, E.b = b, E.nA = nA, E.nB = nB, E.lenlo = lenlo, E.lenhi = Wtop;
            EdgeInfo base{i, kr, s, l, 0, nullptr};
            detail::wrec(E, 0, CB, base, emit);
          }
        }
    }
  }
}

template <class F>
inline void neighbours_key(const CKey& key, int lo, int cap, int umax, F&& emit, int* thr = nullptr) {
  Letter w0[MAXT], w1[MAXT];
  int n0, n1;
  unpack(key, w0, n0, w1, n1);
  neighbours(w0, n0, w1, n1, lo, cap, umax, emit, thr);
}

}  // namespace canon
}  // namespace ac
