// State features (shared by the value model at search time and by the
// `features` CLI command used to build training data — one source of truth)
// and a tiny MLP evaluator whose weights are trained in Python
// (acsolver/model.py) and loaded from a text file.
#pragma once
#include <cmath>
#include <fstream>
#include <stdexcept>

#include "endgame.hpp"

namespace ac {

constexpr int NFEAT = 18;

inline int syllables(const Letter* a, int n) {
  int s = 0;
  for (int i = 0; i < n; ++i)
    if (i == 0 || std::abs(a[i]) != std::abs(a[i - 1])) ++s;
  // cyclic merge
  if (n > 1 && s > 1 && std::abs(a[0]) == std::abs(a[n - 1])) --s;
  return s;
}
inline int cyc_slack(const Letter* a, int n) {
  int i = 0, j = n - 1, k = 0;
  while (i < j && a[i] == -a[j]) ++i, --j, k += 2;
  return k;
}
inline int longest_run(const Letter* a, int n) {
  int best = 0, cur = 0;
  for (int i = 0; i < n; ++i) {
    cur = (i > 0 && a[i] == a[i - 1]) ? cur + 1 : 1;
    best = std::max(best, cur);
  }
  return best;
}

inline void compute_features(const Letter* a0, int n0, const Letter* a1, int n1, const Endgame* eg,
                             float* f) {
  int ex[2] = {0, 0}, ey[2] = {0, 0}, cx = 0, cy = 0;
  const Letter* w[2] = {a0, a1};
  int n[2] = {n0, n1};
  for (int r = 0; r < 2; ++r)
    for (int i = 0; i < n[r]; ++i) {
      Letter c = w[r][i];
      if (c == 1) ++ex[r], ++cx;
      else if (c == -1) --ex[r], ++cx;
      else if (c == 2) ++ey[r], ++cy;
      else --ey[r], ++cy;
    }
  int cs0 = cyc_slack(a0, n0), cs1 = cyc_slack(a1, n1);
  int d = eg ? eg->dist(a0, n0, a1, n1) : -1;
  int er = eg && eg->loaded() ? eg->radius + 1 : 1;
  f[0] = n0 + n1;
  f[1] = std::min(n0, n1);
  f[2] = std::max(n0, n1);
  f[3] = std::abs(ex[0]);
  f[4] = std::abs(ey[0]);
  f[5] = std::abs(ex[1]);
  f[6] = std::abs(ey[1]);
  f[7] = syllables(a0, n0);
  f[8] = syllables(a1, n1);
  f[9] = cs0;
  f[10] = cs1;
  f[11] = d >= 0 ? d : er;
  f[12] = cx;
  f[13] = cy;
  f[14] = std::max(longest_run(a0, n0), longest_run(a1, n1));
  f[15] = std::min(n0 - cs0, n1 - cs1);
  f[16] = (n0 - cs0) + (n1 - cs1);
  f[17] = d >= 0 ? 1 : 0;
}

struct MLP {
  int nin = 0;
  std::vector<float> mean, sd;
  struct Layer {
    int in, out;
    std::vector<float> W, b;
  };
  std::vector<Layer> layers;
  bool loaded() const { return !layers.empty(); }

  void load(const std::string& path) {
    std::ifstream f(path);
    if (!f) throw std::runtime_error("cannot open model " + path);
    std::string tag;
    f >> tag;
    if (tag != "mlp") throw std::runtime_error("bad model file");
    f >> tag >> nin;  // "nfeat F"
    if (nin != NFEAT) throw std::runtime_error("model feature count mismatch");
    mean.resize(nin);
    sd.resize(nin);
    f >> tag;
    for (auto& v : mean) f >> v;
    f >> tag;
    for (auto& v : sd) f >> v;
    int L;
    f >> tag >> L;
    layers.resize(L);
    for (auto& l : layers) {
      f >> tag >> l.in >> l.out;
      l.W.resize((size_t)l.in * l.out);
      l.b.resize(l.out);
      for (auto& v : l.W) f >> v;
      for (auto& v : l.b) f >> v;
    }
  }

  float eval(const float* feat) const {
    float buf[2][256];
    int n = nin;
    for (int i = 0; i < n; ++i) buf[0][i] = (feat[i] - mean[i]) / sd[i];
    int cur = 0;
    for (size_t li = 0; li < layers.size(); ++li) {
      const Layer& l = layers[li];
      float* in = buf[cur];
      float* out = buf[cur ^ 1];
      for (int o = 0; o < l.out; ++o) {
        float s = l.b[o];
        const float* w = &l.W[(size_t)o * l.in];
        for (int i = 0; i < l.in; ++i) s += w[i] * in[i];
        out[o] = (li + 1 < layers.size()) ? std::max(0.0f, s) : s;
      }
      cur ^= 1;
      n = l.out;
    }
    return buf[cur][0];
  }
};

}  // namespace ac
