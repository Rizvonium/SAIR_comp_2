// Corridor table: every state on every known solution path (of any
// problem), mapped to the number of moves that path still needs.  Problems
// in the pool are AC-related to each other, so a search for one problem
// often walks into another problem's solution corridor; it can then finish
// by following that path.  The finish is not shortest — path shortening
// cleans up the splice afterwards.
#pragma once
#include <fstream>

#include "endgame.hpp"
#include "json.hpp"

namespace ac {

inline uint64_t owner_hash(const std::string& id) {
  uint64_t h = 1469598103934665603ULL;
  for (char ch : id) h = (h ^ (uint8_t)ch) * 1099511628211ULL;
  return mix64(h) | 1;
}

struct Corridor {
  HashMap map;  // state hash -> entry index
  struct Entry {
    uint32_t path, idx;
  };
  std::vector<Entry> entries;
  std::vector<std::vector<int>> paths;
  std::vector<uint64_t> owner;  // hash of the problem id each path solves
  std::vector<State> starts;    // start state of each path
  bool loaded() const { return !paths.empty(); }

  void add_path(const State& start, const std::vector<int>& path, uint64_t own = 0) {
    State s = start;
    uint32_t pid = (uint32_t)paths.size();
    std::vector<uint64_t> hs;
    hs.push_back(hash_state(s));
    for (int m : path) {
      apply_move(s, m);
      hs.push_back(hash_state(s));
    }
    if (!is_target(s)) return;  // not a solution: ignore
    paths.push_back(path);
    owner.push_back(own);
    starts.push_back(start);
    for (size_t i = 0; i + 1 < hs.size(); ++i) {
      uint32_t rem = (uint32_t)(path.size() - i);
      uint32_t* e = map.findm(hs[i]);
      if (!e) {
        map.insert(hs[i], (uint32_t)entries.size());
        entries.push_back({pid, (uint32_t)i});
      } else {
        Entry& old = entries[*e];
        if (paths[old.path].size() - old.idx > rem) old = {pid, (uint32_t)i};
      }
    }
  }

  // remaining moves along the corridor, or -1.  Paths owned by `exclude`
  // (the problem being searched) are ignored.
  int dist(const Letter* a0, int n0, const Letter* a1, int n1, uint64_t exclude = 0) const {
    if (paths.empty()) return -1;
    const uint32_t* e = map.find(hash_state(a0, n0, a1, n1));
    if (!e) return -1;
    const Entry& en = entries[*e];
    if (exclude && owner[en.path] == exclude) return -1;
    return (int)(paths[en.path].size() - en.idx);
  }

  std::optional<std::vector<int>> finish(const State& s0, uint64_t exclude = 0) const {
    if (paths.empty()) return std::nullopt;
    const uint32_t* e = map.find(hash_state(s0));
    if (!e) return std::nullopt;
    const Entry& en = entries[*e];
    if (exclude && owner[en.path] == exclude) return std::nullopt;
    std::vector<int> fin(paths[en.path].begin() + en.idx, paths[en.path].end());
    State s = s0;
    for (int m : fin) apply_move(s, m);
    if (!is_target(s)) return std::nullopt;  // hash collision
    return fin;
  }

  size_t load(const std::string& file) {
    std::ifstream f(file);
    if (!f) throw std::runtime_error("cannot open corridors " + file);
    std::string l;
    while (std::getline(f, l)) {
      if (l.find_first_not_of(" \t\r") == std::string::npos) continue;
      auto v = mj::parse(l);
      State s;
      for (int x : v["r0"].as_ints()) s.r[0].push_back((Letter)x);
      for (int x : v["r1"].as_ints()) s.r[1].push_back((Letter)x);
      add_path(s, v["path"].as_ints(), owner_hash(v["id"].as_str()));
    }
    return entries.size();
  }
};

}  // namespace ac
