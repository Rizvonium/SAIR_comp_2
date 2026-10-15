// Endgame table: exact distance-to-target for every state within radius B
// of the target (x, y).  Built once by BFS from the target (the move set
// is closed under inversion, so forward BFS from T gives distances *to* T)
// and shared read-only by all searches and threads.
//
// Each entry stores dist (low byte) and the move that discovered the state
// from its BFS parent (next byte).  The finishing path from u is obtained
// by repeatedly applying INVERSE[move(u)], which steps to a state one
// closer to the target.
#pragma once
#include <cstdio>
#include <optional>
#include <stdexcept>

#include "ac.hpp"

namespace ac {

struct Endgame {
  HashMap map;
  int radius = -1;
  std::vector<size_t> level_sizes;

  bool loaded() const { return radius >= 0; }

  // dist or -1
  int dist(const Letter* a0, int n0, const Letter* a1, int n1) const {
    if (radius < 0) return (is_target(a0, n0, a1, n1) ? 0 : -1);
    const uint32_t* v = map.find(hash_state(a0, n0, a1, n1));
    return v ? (int)(*v & 0xff) : -1;
  }
  int dist(const State& s) const {
    return dist(s.r[0].data(), (int)s.r[0].size(), s.r[1].data(), (int)s.r[1].size());
  }

  // Shortest finishing moves from s to the target.  Returns nullopt if s
  // is not in the table or (hash collision) the reconstruction fails.
  std::optional<std::vector<int>> finish(const State& s0) const {
    State s = s0;
    std::vector<int> moves;
    if (is_target(s)) return moves;
    if (radius < 0) return std::nullopt;
    const uint32_t* v = map.find(hash_state(s));
    if (!v) return std::nullopt;
    int d = *v & 0xff;
    for (int step = 0; step < d; ++step) {
      v = map.find(hash_state(s));
      if (!v) return std::nullopt;
      int m = INVERSE[(*v >> 8) & 0xff];
      apply_move(s, m);
      moves.push_back(m);
    }
    if (!is_target(s)) return std::nullopt;
    return moves;
  }

  void build(int B, bool verbose = true) {
    radius = B;
    map.reset(1 << 20);
    level_sizes.clear();
    Arena cur, nxt;
    const Letter x = 1, y = 2;
    cur.add(&x, 1, &y, 1, UINT32_MAX, 0, 0);
    map.insert(hash_state(&x, 1, &y, 1), 0);
    level_sizes.push_back(1);
    std::vector<Letter> buf;
    for (int d = 1; d <= B; ++d) {
      nxt.clear();
      for (uint32_t i = 0; i < cur.nodes.size(); ++i) {
        const Node& nd = cur.nodes[i];
        const Letter* a0 = cur.w0(i);
        const Letter* a1 = cur.w1(i);
        buf.resize(nd.l0 + nd.l1 + 2);
        for (int m = 0; m < NUM_MOVES; ++m) {
          int n = apply_into(m, a0, nd.l0, a1, nd.l1, buf.data());
          const Letter *b0 = a0, *b1 = a1;
          int n0 = nd.l0, n1 = nd.l1;
          if (TARGET_REL[m] == 0) {
            b0 = buf.data();
            n0 = n;
          } else {
            b1 = buf.data();
            n1 = n;
          }
          uint64_t h = hash_state(b0, n0, b1, n1);
          if (map.insert(h, (uint32_t)d | ((uint32_t)m << 8))) nxt.add(b0, n0, b1, n1, 0, m, d);
        }
      }
      std::swap(cur, nxt);
      level_sizes.push_back(cur.nodes.size());
      if (verbose) fprintf(stderr, "endgame level %d: %zu states (total %zu)\n", d, cur.nodes.size(), map.size());
    }
  }

  void save(const std::string& path) const {
    FILE* f = fopen(path.c_str(), "wb");
    if (!f) throw std::runtime_error("cannot write " + path);
    uint64_t magic = 0x4143454e44474d31ULL, r = radius, n = map.size();
    fwrite(&magic, 8, 1, f);
    fwrite(&r, 8, 1, f);
    fwrite(&n, 8, 1, f);
    for (size_t i = 0; i < map.keys.size(); ++i)
      if (map.keys[i]) {
        fwrite(&map.keys[i], 8, 1, f);
        fwrite(&map.vals[i], 4, 1, f);
      }
    fclose(f);
  }

  bool load(const std::string& path) {
    FILE* f = fopen(path.c_str(), "rb");
    if (!f) return false;
    uint64_t magic, r, n;
    if (fread(&magic, 8, 1, f) != 1 || magic != 0x4143454e44474d31ULL || fread(&r, 8, 1, f) != 1 ||
        fread(&n, 8, 1, f) != 1) {
      fclose(f);
      return false;
    }
    map.reset(n * 2 + 16);
    const size_t CH = 1 << 16;
    std::vector<char> buf(CH * 12);
    size_t left = n;
    while (left) {
      size_t k = std::min(left, CH);
      if (fread(buf.data(), 12, k, f) != k) {
        fclose(f);
        return false;
      }
      for (size_t i = 0; i < k; ++i) {
        uint64_t key;
        uint32_t v;
        memcpy(&key, buf.data() + 12 * i, 8);
        memcpy(&v, buf.data() + 12 * i + 8, 4);
        map.insert(key, v);
      }
      left -= k;
    }
    fclose(f);
    radius = (int)r;
    return true;
  }
};

}  // namespace ac
