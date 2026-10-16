# Expand ACSolverX solved supermove paths (public, CC BY 4.0) into exact ac-r2-v1 move paths
# for the engine's corridor table: {"id": "pub-<line>", "r0", "r1", "path"} per line.
import json, sys, time
sys.path.insert(0, sys.argv[1])
import acsx_expand as X
src, out, lim = sys.argv[2], sys.argv[3], int(sys.argv[4])
t0 = time.time(); n = ok = 0; tot = 0
with open(src) as f, open(out, "w") as g:
    for line in f:
        if n >= lim: break
        r = json.loads(line); n += 1
        try:
            mv, ns, good = X.run(r["relators"], r["packed_supermoves"])
        except Exception:
            continue
        if good:
            ok += 1; tot += len(mv)
            g.write(json.dumps({"id": "pub-%d" % r["line"], "r0": r["relators"][0], "r1": r["relators"][1], "path": mv}) + "\n")
print(n, ok, "mean len", tot / max(ok, 1), "secs", round(time.time() - t0, 1))
