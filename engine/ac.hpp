// Core Andrews–Curtis rank-2 engine: words, the 14 frozen moves of
// move_spec_version "ac-r2-v1", free reduction, hashing.
//
// Semantics are bit-for-bit those of the official verifier
// (external/Andrews-Curtis/competition/tools/verifier/core.py):
//   letters 1 = x, -1 = x^-1, 2 = y, -2 = y^-1;
//   after each move the modified relator is freely reduced by a single
//   left-to-right stack pass.
// The unmodified relator is copied unchanged.  `selftest` in main.cpp and
// tests/test_engine_crosscheck.py cross-check this against the verifier.
#pragma once
#include <algorithm>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

namespace ac {

using Letter = int8_t;
using Word = std::vector<Letter>;

constexpr int NUM_MOVES = 14;
// INVERSE[m] undoes m (official inverse column).
constexpr int INVERSE[NUM_MOVES] = {0, 1, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12};
// Which relator move m rewrites.
constexpr int TARGET_REL[NUM_MOVES] = {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1};
// Conjugator letters for moves 6..9 / 10..13.
constexpr Letter CONJ[4] = {1, -1, 2, -2};

struct State {
  Word r[2];
  size_t total() const { return r[0].size() + r[1].size(); }
  bool operator==(const State& o) const { return r[0] == o.r[0] && r[1] == o.r[1]; }
};

inline bool is_target(const Letter* a0, int n0, const Letter* a1, int n1) {
  return n0 == 1 && n1 == 1 && a0[0] == 1 && a1[0] == 2;
}
inline bool is_target(const State& s) {
  return is_target(s.r[0].data(), (int)s.r[0].size(), s.r[1].data(), (int)s.r[1].size());
}

// Stack-reduction push: identical to the verifier's left fold.
inline void push_red(Letter* out, int& n, Letter a) {
  if (n > 0 && out[n - 1] == -a)
    --n;
  else
    out[n++] = a;
}

// Apply move m to (a0,n0),(a1,n1).  Writes the rewritten relator
// (index TARGET_REL[m]) into `out`, which must have room for n0+n1+2
// letters, and returns its length.  The other relator is unchanged.
inline int apply_into(int m, const Letter* a0, int n0, const Letter* a1, int n1, Letter* out) {
  const int t = TARGET_REL[m];
  const Letter* src = t == 0 ? a0 : a1;
  const int ns = t == 0 ? n0 : n1;
  const Letter* oth = t == 0 ? a1 : a0;
  const int no = t == 0 ? n1 : n0;
  int n = 0;
  if (m <= 1) {  // inversion
    for (int i = ns - 1; i >= 0; --i) out[n++] = (Letter)-src[i];
    return n;
  }
  if (m <= 5) {  // right multiplication by other or its inverse
    const bool inv = (m == 3 || m == 5);
    for (int i = 0; i < ns; ++i) push_red(out, n, src[i]);
    if (!inv)
      for (int i = 0; i < no; ++i) push_red(out, n, oth[i]);
    else
      for (int i = no - 1; i >= 0; --i) push_red(out, n, (Letter)-oth[i]);
    return n;
  }
  // conjugation g r g^-1
  const Letter g = CONJ[(m - 6) & 3];
  push_red(out, n, g);
  for (int i = 0; i < ns; ++i) push_red(out, n, src[i]);
  push_red(out, n, (Letter)-g);
  return n;
}

inline void apply_move(State& s, int m) {
  const int t = TARGET_REL[m];
  std::vector<Letter> buf(s.r[0].size() + s.r[1].size() + 2);
  int n = apply_into(m, s.r[0].data(), (int)s.r[0].size(), s.r[1].data(), (int)s.r[1].size(), buf.data());
  buf.resize(n);
  s.r[t].swap(buf);
}

inline Word free_reduce(const Word& w) {
  Word out(w.size());
  int n = 0;
  for (Letter a : w) push_red(out.data(), n, a);
  out.resize(n);
  return out;
}

// ---------------------------------------------------------------------
// Hashing.  Letters are packed 2 bits each (x=0,X=1,y=2,Y=3), 32 per
// 64-bit chunk, then mixed.  Lengths are mixed in so (r0,r1) boundaries
// are unambiguous.  64-bit hashes are used as state identities inside
// searches; every emitted path is replayed exactly before output, and
// the official verifier re-checks it, so a collision can only cost a
// missed state, never a wrong result.
inline uint64_t mix64(uint64_t z) {
  z ^= z >> 30;
  z *= 0xbf58476d1ce4e5b9ULL;
  z ^= z >> 27;
  z *= 0x94d049bb133111ebULL;
  z ^= z >> 31;
  return z;
}
inline uint64_t code2(Letter a) { return a == 1 ? 0 : a == -1 ? 1 : a == 2 ? 2 : 3; }

inline uint64_t hash_word(uint64_t h, const Letter* a, int n) {
  h = mix64(h ^ (0x9e3779b97f4a7c15ULL * (uint64_t)(n + 1)));
  int i = 0;
  while (i < n) {
    uint64_t chunk = 0;
    int e = std::min(n, i + 32);
    for (int k = i; k < e; ++k) chunk = (chunk << 2) | code2(a[k]);
    h = mix64(h ^ chunk ^ 0x632be59bd9b4e019ULL) + 0x9e3779b97f4a7c15ULL;
    i = e;
  }
  return h;
}
inline uint64_t hash_state(const Letter* a0, int n0, const Letter* a1, int n1) {
  uint64_t h = hash_word(0x243f6a8885a308d3ULL, a0, n0);
  h = hash_word(h ^ 0x13198a2e03707344ULL, a1, n1);
  return h ? h : 1;  // 0 is reserved as the empty-slot marker
}
inline uint64_t hash_state(const State& s) {
  return hash_state(s.r[0].data(), (int)s.r[0].size(), s.r[1].data(), (int)s.r[1].size());
}

// ---------------------------------------------------------------------
// Open-addressing hash map: uint64 key (nonzero) -> uint32 value.
struct HashMap {
  std::vector<uint64_t> keys;
  std::vector<uint32_t> vals;
  size_t mask = 0, count = 0;
  explicit HashMap(size_t cap_pow2 = 1 << 16) { reset(cap_pow2); }
  void reset(size_t cap) {
    size_t c = 16;
    while (c < cap) c <<= 1;
    keys.assign(c, 0);
    vals.assign(c, 0);
    mask = c - 1;
    count = 0;
  }
  void clear() { reset(16); }
  size_t size() const { return count; }
  size_t bytes() const { return keys.size() * 12; }
  // returns pointer to value or nullptr
  const uint32_t* find(uint64_t k) const {
    size_t i = k & mask;
    while (true) {
      uint64_t kk = keys[i];
      if (kk == k) return &vals[i];
      if (kk == 0) return nullptr;
      i = (i + 1) & mask;
    }
  }
  uint32_t* findm(uint64_t k) { return const_cast<uint32_t*>(static_cast<const HashMap*>(this)->find(k)); }
  // inserts if absent; returns true if inserted
  bool insert(uint64_t k, uint32_t v) {
    if ((count + 1) * 2 > keys.size()) grow();
    size_t i = k & mask;
    while (true) {
      uint64_t kk = keys[i];
      if (kk == k) return false;
      if (kk == 0) {
        keys[i] = k;
        vals[i] = v;
        ++count;
        return true;
      }
      i = (i + 1) & mask;
    }
  }
  void grow() {
    std::vector<uint64_t> ok;
    std::vector<uint32_t> ov;
    ok.swap(keys);
    ov.swap(vals);
    reset(ok.size() * 2);
    for (size_t i = 0; i < ok.size(); ++i)
      if (ok[i]) insert(ok[i], ov[i]);
  }
};

// ---------------------------------------------------------------------
// Node arena used by every search: words are stored contiguously, each
// node remembers its parent and the move that produced it.
struct Node {
  uint64_t off;
  uint32_t parent;  // UINT32_MAX for a root
  uint16_t l0, l1;
  uint16_t depth;
  uint8_t move;
};

struct Arena {
  std::vector<Letter> letters;
  std::vector<Node> nodes;
  void clear() {
    letters.clear();
    nodes.clear();
  }
  uint32_t add(const Letter* a0, int n0, const Letter* a1, int n1, uint32_t parent, int move, int depth) {
    Node nd;
    nd.off = letters.size();
    nd.l0 = (uint16_t)n0;
    nd.l1 = (uint16_t)n1;
    nd.parent = parent;
    nd.move = (uint8_t)move;
    nd.depth = (uint16_t)depth;
    // a0/a1 may point into `letters` itself (an unchanged relator of the
    // parent); make room first, then copy with memmove-safe offsets.
    const Letter* base = letters.data();
    const bool alias0 = n0 && a0 >= base && a0 < base + letters.size();
    const bool alias1 = n1 && a1 >= base && a1 < base + letters.size();
    const size_t o0 = alias0 ? a0 - base : 0, o1 = alias1 ? a1 - base : 0;
    size_t at = letters.size();
    letters.resize(at + n0 + n1);
    const Letter* nb = letters.data();
    if (n0) memmove(letters.data() + at, alias0 ? nb + o0 : a0, n0);
    if (n1) memmove(letters.data() + at + n0, alias1 ? nb + o1 : a1, n1);
    nodes.push_back(nd);
    return (uint32_t)(nodes.size() - 1);
  }
  const Letter* w0(uint32_t i) const { return letters.data() + nodes[i].off; }
  const Letter* w1(uint32_t i) const { return letters.data() + nodes[i].off + nodes[i].l0; }
  State state(uint32_t i) const {
    State s;
    s.r[0].assign(w0(i), w0(i) + nodes[i].l0);
    s.r[1].assign(w1(i), w1(i) + nodes[i].l1);
    return s;
  }
  // moves from the root to node i
  std::vector<int> path_to(uint32_t i) const {
    std::vector<int> p;
    while (nodes[i].parent != UINT32_MAX) {
      p.push_back(nodes[i].move);
      i = nodes[i].parent;
    }
    std::reverse(p.begin(), p.end());
    return p;
  }
  size_t bytes() const { return letters.capacity() + nodes.capacity() * sizeof(Node); }
};

// Replay a path; returns false (and leaves s at failure point) if a total
// length limit is exceeded.  Tracks work like the verifier.
struct ReplayResult {
  State final;
  long long work = 0;
  int peak = 0;
  bool ok_limits = true;
};
inline ReplayResult replay(const State& start, const std::vector<int>& path, int max_total = 10000,
                           long long max_work = 5000000) {
  ReplayResult r;
  r.final = start;
  int tot = (int)start.total();
  r.work = tot;
  r.peak = tot;
  for (int m : path) {
    apply_move(r.final, m);
    tot = (int)r.final.total();
    r.peak = std::max(r.peak, tot);
    r.work += tot;
    if (tot > max_total || r.work > max_work) {
      r.ok_limits = false;  // the verifier stops here too (E_LENGTH_LIMIT / E_WORK_BUDGET)
      break;
    }
  }
  return r;
}

std::string word_str(const Word& w);

}  // namespace ac
