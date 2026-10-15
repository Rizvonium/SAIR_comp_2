"""Value model: predicts distance-to-goal from state features.

Training data are the states along every verified best path, labelled with
the number of moves remaining on that path (an upper bound on the true
distance; best paths are heavily shortened, so it is a tight one).
Features come from the engine itself (``acengine features``) so training
and search-time features are computed by the same code.

The model is a small MLP (18 -> 64 -> 32 -> 1, ReLU) trained with Adam in
numpy and written to data/value_model.txt in the format engine/features.hpp
reads.  Retrain as solutions accumulate (``python3 -m acsolver train``).
"""
from __future__ import annotations

import json
import random

import numpy as np

from . import db, engine, official, problems

MODEL_PATH = official.ROOT / "data" / "value_model.txt"
NFEAT = 18


def dataset(con, max_paths=None, seed=0, siblings=True):
    rows = con.execute("SELECT problem_id, path FROM best_solutions").fetchall()
    random.Random(seed).shuffle(rows)
    if max_paths:
        rows = rows[:max_paths]
    allp = {**problems.ac_problems(), **problems.training_problems()}
    recs = [{"id": r["problem_id"], "r0": allp[r["problem_id"]]["r0"], "r1": allp[r["problem_id"]]["r1"],
             "path": json.loads(r["path"]), "siblings": siblings} for r in rows if r["problem_id"] in allp]
    X, y, groups = [], [], []
    for out in engine.stream("features", recs):
        X.extend(out["X"])
        y.extend(out["y"])
        groups.extend([out["id"]] * len(out["y"]))
    return np.array(X, dtype=np.float32), np.array(y, dtype=np.float32), np.array(groups)


class MLP:
    def __init__(self, sizes, seed=0):
        rng = np.random.default_rng(seed)
        self.W = [rng.normal(0, np.sqrt(2 / a), (b, a)).astype(np.float32) for a, b in zip(sizes, sizes[1:])]
        self.b = [np.zeros(b, np.float32) for b in sizes[1:]]

    def forward(self, X):
        acts = [X]
        h = X
        for i, (W, b) in enumerate(zip(self.W, self.b)):
            h = h @ W.T + b
            if i < len(self.W) - 1:
                h = np.maximum(h, 0)
            acts.append(h)
        return acts

    def predict(self, X):
        return self.forward(X)[-1][:, 0]

    def train(self, X, y, epochs=30, lr=2e-3, batch=512, seed=0, Xv=None, yv=None, verbose=False):
        rng = np.random.default_rng(seed)
        params = self.W + self.b
        m = [np.zeros_like(p) for p in params]
        v = [np.zeros_like(p) for p in params]
        t = 0
        for ep in range(epochs):
            idx = rng.permutation(len(X))
            for s in range(0, len(X), batch):
                bi = idx[s:s + batch]
                acts = self.forward(X[bi])
                # Huber-ish: plain MSE on residuals
                g = (acts[-1][:, 0] - y[bi])[:, None] * (2 / len(bi))
                gW, gb = [None] * len(self.W), [None] * len(self.b)
                for L in range(len(self.W) - 1, -1, -1):
                    gW[L] = g.T @ acts[L]
                    gb[L] = g.sum(0)
                    if L:
                        g = (g @ self.W[L]) * (acts[L] > 0)
                grads = gW + gb
                t += 1
                for k, (p, gr) in enumerate(zip(params, grads)):
                    m[k] = 0.9 * m[k] + 0.1 * gr
                    v[k] = 0.999 * v[k] + 0.001 * gr * gr
                    p -= lr * (m[k] / (1 - 0.9 ** t)) / (np.sqrt(v[k] / (1 - 0.999 ** t)) + 1e-8)
            lr *= 0.93
            if verbose and Xv is not None and (ep % 5 == 4 or ep == epochs - 1):
                print(f"  epoch {ep + 1}: val MAE {np.abs(self.predict(Xv) - yv).mean():.3f}", flush=True)


def save(model: MLP, mean, sd, path=MODEL_PATH):
    with open(path, "w") as f:
        f.write(f"mlp\nnfeat {NFEAT}\nmean " + " ".join(f"{x:.6g}" for x in mean) + "\n")
        f.write("std " + " ".join(f"{x:.6g}" for x in sd) + "\n")
        f.write(f"layers {len(model.W)}\n")
        for W, b in zip(model.W, model.b):
            f.write(f"layer {W.shape[1]} {W.shape[0]}\n")
            f.write(" ".join(f"{x:.7g}" for x in W.ravel()) + "\n")
            f.write(" ".join(f"{x:.7g}" for x in b) + "\n")


def train(con, verbose=False, epochs=30, seed=0) -> dict:
    X, y, groups = dataset(con, seed=seed)
    if len(X) < 1000:
        raise RuntimeError("not enough training states (%d)" % len(X))
    # split by problem so validation states come from unseen paths
    ids = np.unique(groups)
    rng = np.random.default_rng(seed)
    val_ids = set(rng.choice(ids, size=max(1, len(ids) // 10), replace=False))
    vm = np.array([g in val_ids for g in groups])
    mean = X[~vm].mean(0)
    sd = X[~vm].std(0) + 1e-3
    Xn = (X - mean) / sd
    model = MLP([NFEAT, 64, 32, 1], seed)
    base_mae = float(np.abs(y[vm] - y[~vm].mean()).mean())
    model.train(Xn[~vm], y[~vm], epochs=epochs, Xv=Xn[vm], yv=y[vm], verbose=verbose, seed=seed)
    mae = float(np.abs(model.predict(Xn[vm]) - y[vm]).mean())
    # correlation of prediction with true remaining distance
    corr = float(np.corrcoef(model.predict(Xn[vm]), y[vm])[0, 1])
    MODEL_PATH.parent.mkdir(exist_ok=True)
    save(model, mean, sd)
    res = {"states": int(len(X)), "paths": int(len(ids)), "val_mae": mae, "baseline_mae": base_mae, "val_corr": corr,
           "path": str(MODEL_PATH)}
    db.add_insight(con, "model", "model", "value model retrained", res)
    if verbose:
        print(json.dumps(res, indent=1))
    return res
