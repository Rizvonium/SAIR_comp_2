================= canonical-bfs canonical-bfs: minimax-peak search over AC' classes (cyclic words mod rotation, inversion, relator order and the 8 signed generator permutations), with realization into official moves
## summary
The search runs over classes instead of exact states. A class is an unordered pair of cyclic words, taken up to rotation, inversion and the 8 signed permutations of {x,y}. The move set is Havas-Ramsay AC': replace r_i by the cyclic reduction of rot(r_i)*rot(r_j^±1). Classes are expanded in minimax-peak order: everything reachable with peak <= P is visited before anything that needs P+1. That is the same as raising the length cap L step by step, without re-expanding. I checked against exact BFS that a class component equals the projection of the exact component (it held at every cap tested, up to 23). The class component is 1,360 to 13,700 times smaller, which is why it can climb where exact greedy search cannot. In small experiments it solved 25/80 of bench80 at 2 s per problem (exact GBFS: 19/80 at 15M nodes), and 16/20 of the sampled MS-1190 'uncertified' instances in 17 s or less each, with climbs of 0 to 6 letters. It solved 0/10 of the sampled MS-1190 'open' instances and 0/30 of greedy_failed_short. Seven of those 30 turn out to be AK(3) or AK(4) in disguise. The other 23 fall into 6 MS(2)-type cores that have no AC' path with peak <= 29 or 30. Seven solutions were realized into official moves and all passed the official verifier. After the existing shortener, six of them are 45 to 164 moves long and the seventh (ac-00677) is 130.
## why_it_climbs
1) It explores the minimax order exactly. A popped class's key is max(parent key, child total). The search always pops the smallest (key, total) first, so no class needing peak P+1 is expanded before every class reachable with peak <= P has been expanded. This is the same as raising L by 1 each time without re-expanding. Greedy descent only ever searches the sublevel set at the start length. This search searches that set first and then climbs one level at a time. Every greedy_failed_short start showed the barrier: at peak = start, the component of ac-00008 holds just 1 class; the start is a strict local minimum.
2) Climbing is affordable only because of the quotient. With ac-hpp exact moves, I ran exact BFS with cap L, projected every state to its class, and compared with the class search (xcheck.cpp). The class sets were identical: ac-00008 at L=18, 20, 21, 22, 23; ac-00066 at L=18, 20, 21; ac-00413 at L=22. The exact component is far larger: 54,336 exact states vs 40 classes (L=20), 384,384 vs 209 (L=22), and 37,464,032 vs 2,738 for ac-00413 at L=22. That is a 1,360 to 13,700 times compression. Exact GBFS at 15M nodes therefore cannot even finish the sublevel set of a 30-letter start, or climb 2 levels. The class search does both in seconds.
3) Completeness. A multiplication in exact space corresponds to a class move r_i <- a u b u^-1, where u = g_i^-1 g_j. I proved that a 'u-move' either equals a u=empty move or has no cancellation at all, so it is a pure growth move adding n_j + 2|u| letters. With U=0, exhaustion is near-complete: U=2 adds 1.5% to 3% more classes at L=26. With u-moves of length up to (L - T - n_j)/2 enabled, exhausting a cap L proves that no AC path with peak <= L exists, up to 64-bit hash collisions. The controller can use such a proof as a lower bound.
## state_and_move_realization
The search stores classes only (packed canonical words plus a parent pointer). The realizer turns the class path c0..ck into official moves. It does this by matching, not by replaying stored move descriptors, so the B2 automorphisms and the relator order never need to be tracked.

Each step keeps the actual exact state (s0, s1) and peels each relator as s = g c g^-1, with c cyclically reduced. It enumerates (i, e, p, q) on the actual peeled words: a = rot_p(c_i), b' = rot_q(c_j^e), child = cyc_reduce(a b'). It first filters by length, then compares canon(child, c_j) with the key of c_{k+1}.

For each match it computes the realization cost in closed form, using the Cayley-tree median.
- Write a = Da c_i Da^-1 with Da in {c_i[:p]^-1, c_i[p:]}.
- Let B = b' if e = +1, or b'^-1 if e = -1. B is a rotation of c_j, so B = Db c_j Db^-1.
- Put U = Da g_i^-1 and V = Db g_j^-1. Choose the common conjugator x with x^-1 = P = lcp(U, V).
- Conjugate s_i by h_i = P^-1 U and s_j by h_j = P^-1 V, one letter at a time, innermost letter first, using moves 6..9 for r0 and 10..13 for r1. Each single-letter conjugation is freely reduced, so the result is exactly x a x^-1 and x B x^-1.
- Then apply one multiplication: move 2 or 3 for i = 0 (e = +1 or -1), move 4 or 5 for i = 1.
- Cost = |h_i| + |h_j| + 1 = d_tree(U, V) + 1. This is optimal for one-multiplication steps among common conjugators, and it keeps the leftover conjugator x as short as possible.
- A first attempt that conjugated only one relator (x = U^-1) let x accumulate: raw paths of 353 to 3,267 moves. The median choice gave 59 to 242.

The search may stop at a class with a 1-letter relator. The realizer then descends greedily: at every step there is an AC' move that lowers the total by 1.

Finish: peel both relators (|g| conjugations each), then 0 to 2 inversions (moves 0 and 1). If the result is (y^±1, x^±1), the relator swap is NOT a free official move: it costs the fixed 5 moves [2,5,2,9,1], i.e. (y,x) -> (yx,x) -> (yx,Y) -> (yxY,Y) -> (x,Y) -> (x,y), after first fixing signs. In production, use the endgame table (radius 8) or bidir for the final step instead.

Measured cost: about 4.9 to 9.1 raw official moves per canonical step (59/12, 88/14, 151/23, 242/29, 200/22). Peaks of the exact paths were 29 to 46, higher than the class peaks because of the conjugated forms; this is irrelevant against the 10,000 limit. Every realized path (12 in total across variants) was accepted by the official verifier. Realization CPU is negligible next to the search in C++; the Python prototype takes under 1 s per path once the length prefilter is in.
## complexity
Speed (single thread, prototype cbfs2):
- About 1.4 µs per canonicalized child with the B2 quotient (0.64 µs without it).
- 20k to 65k class expansions per second at words of length 7 to 13, about 13k/s at length 25 or more (L = 52).
- AK(3) at cap 24: 197,870 classes in 6.3 s with B2. Without B2: 1,580,780 classes in 22.5 s, exactly 8 times as many, because that component is closed under B2.
- B2 does not always shrink the state count: the ac-00392 component is identical with and without it (90,770 classes), so B2 costs 2.2 times the CPU there but saves up to 8 times the memory elsewhere.

Memory: about 50 B per class now (37 B packed node + hash set). The packed design target is about 32 B, so 1e7 classes is about 0.3 to 0.5 GB and 1e8 is about 3 to 5 GB.

Number of classes in the whole space (all pairs, up to rotation, inversion, swap and B2): about 6.2e4 (L<=14), 5.0e5 (16), 4.1e6 (18), 3.4e7 (20), 2.9e8 (22), 2.4e9 (24), 2.0e10 (26), 1.7e11 (28), 1.5e12 (30). The reachable components are tiny fractions of this.

Measured component sizes (exhausted, U=0), by cap L:

| Problem | Cap and classes |
|---|---|
| AK(3) | 22: 32,295 · 23: 111,069 · 24: 197,870 · 25: 691,947 · 26: 1,284,411 (49.9 s) |
| MS(2) core A (ac-00392 and 7 others) | 24: 15,583 · 25: 39,791 · 26: 90,770 · 27: 285,971 · 28: 660,826 · 29: 1,808,290 |
| ac-00008 | 29: 120,432 · 30: 416,534, closed, never below 16 |
| ac-00413 core | 26: 108,123 |
| MS(8) start ac-01960 (total 30) | 44: 904 · 52: 205,697, never below 30 |

Growth is about 2 to 3.5 times per level, with an odd/even alternation.

Time per problem:
- Total 15 (core-sized): solved within 1 s if the climb is <= about 4. Otherwise, a total-15 core reaches peak 32 at about 3e7 classes (about 25 to 40 min, 1.5 GB), and peak 35 at about 5e8 (infeasible).
- Total 21 to 25 (MS-1190 uncertified): peak start+3 to start+6, 0.7M to 4M classes, 2 to 17 s.
- Total 31 to 35: the sublevel set at peak = start held 0.5M to 4M classes before success (10 to 33 s).

Pool sweep cost: 10,115 problems at 20 to 30 s each is 56 to 84 CPU-hours, i.e. 14 to 21 h on 4 cores.
## experiments
All files are in /tmp/claude-0/-home-user-SAIR-comp-2/5af7ac6c-728a-515a-9a31-33a98dd3e07f/scratchpad/design_canonical-bfs/. Code: cbfs.cpp (v1), cbfs2.cpp (minimax, BFS mode, corridor), canon_common.hpp, xcheck.cpp, realize.py, realize_opt.py.

E1 Exactness (xcheck.cpp). Exact-move BFS with cap L, projected to classes, matched the class component exactly in every case:

| Problem | L | Exact states | Classes |
|---|---|---|---|
| ac-00008 | 18 | 2,716 | 6 |
| ac-00008 | 20 | 54,336 | 40 |
| ac-00008 | 21 | 158,128 | 91 |
| ac-00008 | 22 | 384,384 | 209 |
| ac-00008 | 23 | 1,114,728 | 517 |
| ac-00066 | 20 | 104,368 | 37 |
| ac-00066 | 21 | 411,432 | 134 |
| ac-00413 | 22 | 37,464,032 | 2,738 |

U=0 and U=3 gave the same sets at L <= 21. At L=26, U=2 adds 2% to 3%: 5,362->5,537; 90,770->92,212; 108,123->109,746.

E2 Training sanity: 8 training problems all found, peak start+0 or +1, at most 0.01 s.

E3 greedy_failed_short (30): no solutions at L=24 or 26.
- Signatures (minimal class at L=24): 5 problems -> the AK(3) class (ac-00137, ac-01083, ac-03301, ac-06556, ac-06672; ac-00137 reaches (xyxYXY, xxxxYYY) via peak 19). 2 problems -> AK(4) (ac-00472, ac-01440).
- The other 23 fall into 6 MS(2)-type cores. The main one is 'xxxyXXY_xxyyXYYY' with 8 problems; another core holds 4 problems.
- Core A has no AC' path with peak <= 29 (at least 1.8M classes, 150 s). ac-00008 is closed at L=30.

E4 bench80, 2 s per problem, cap 60: 25/80 or 26/80 found, 24 of them with peak = start.
- 5 unsolved whose sublevel set was not exhausted, at 33 s: 4/5 found (ac-08903, ac-07979, ac-07718, ac-08014; 0.6M to 4M classes, no climb).
- 5 that needed climbing, at 33 s: 1/5 (ac-05155, peak 23 from 20).
- 15 others at 10 s: 3/15 (peaks +1, 0, +4).
- By family: 'other' (AC-transformed) 24/54 at 2 s; explicit MS(n) 4/26.

E5 MS-1190 uncertified (20): 10/20 at L=24 (at most a few seconds each), 6 more at 17 s (peaks start+3 to +6). That is 16/20, none of them in the DB before.

E6 MS-1190 open (10): 0/10 at 16 s (reached keys 24 to 35). ac-02710 lies in the AK(4) class.

E7 Realization plus official verifier:

| Problem | Raw path (per-step min-cost realization) | Final after shorten (r7, 30 s) |
|---|---|---|
| ac-00083 | 59 | 45 |
| ac-00345 | 88 | 72 |
| ac-01025 | 151 | 113 |
| ac-00016 | 242 | 164 |
| ac-00869 | 200 | 141 |
| ac-00677 (GBFS class path) | 212 | 130 |

All accepted by the official verifier. Path compaction matters: from GBFS class paths, ac-00083 finished at 185 and ac-01025 at 362.

E8 Canonical corridor: the 497 stored solution paths give 3,649 peeled states, of which 477 classes have total >= 10. On 55 unsolved bench80 at 2.5 s: 3 corridor hits; 1 of those (ac-08562) was not solved otherwise.

E9 Universe counts (formula): see the complexity section.
## expected_coverage
- bench80 (random scored sample): measured 25/80 at 2 s per problem. Projected about 40% to 50% at about 30 s per problem (extrapolated from 8/25 extra solves among sampled unsolved). Exact GBFS got 19/80 at 15M nodes. Most of the gain is on the 'other' (AC-transformed) family, where the solution lies in the sublevel set but that set is about 1e3 times too big in exact space. Scaled to the pool: about 3,000 problems at 2 s, about 4,000 to 5,000 at 30 s, before corridor snowballing. Today about 73 scored problems are solved.
- ms1190_uncertified: measured 16/20 within 17 s each. Expect about 70% to 80% of the 183 uncertified. These are high value, because no public path exists.
- greedy_failed_short: expect 0 to 3 of 30.
  - 7 are AK(3) or AK(4) equivalents, famous open problems; mark and skip them.
  - The other 23 share 6 MS(2)-type cores that need peak >= 30 or 31.
  - A one-off deep run per core (L up to 32 or 33, 1e7 to 1e8 classes, 1 to 3 h, 3 to 6 GB) is the only chance here. If a core falls, all of its members are solved at once through cluster splicing.
- ms1190_open: expect about 0. Their components climb from start+10 to start+12 without descending.
- Explicit MS(n>=8) starts (for example ac-01960) are isolated local minima: closed at +22, 205k classes at L=52. Out of reach for this method.
- Side benefit: the signature and clustering pass maps problems to shared cores. On greedy_failed_short, 30 problems map to 9 classes. This stops wasted compute on AK-equivalents and multiplies every core solution.
## path_length_quality
Raw length is the sum over canonical steps of (1 + conjugation cost). Measured: 4.9 to 9.1 moves per step at words of length 7 to 13. Shortness levers, roughly in order of payoff:
1) Fewer class steps. The GBFS-LIFO class path wanders (49, 75, 96, 779 steps). Compact it with BFS at the found peak P*, or with a DP over 1- and 2-step class shortcuts. Measured 49->12, 30->14, 75->23, 96->29, 47->22. Final lengths went 185->45 (ac-00083) and 362->113 (ac-01025).
2) Median common conjugator per step (closed form d_tree(U, V) + 1). Measured: 82->59, 142->88, 183->151, 254->242, 251->200 raw.
3) Beam or DP realization across steps: keep K = 4 to 16 actual states per class step, since the choice of rotation affects later costs. Add Dijkstra on classes with an estimated cost per step (1 + rotation estimate) instead of unit steps.
4) Existing shorten pipeline (cycle cut, commutation, endgame truncation, ball DP 4+4): another 15% to 35%, for example 242->164 and 200->141.
5) Run the existing 'guided' exact re-search with the realized path as a self-corridor, and polish later.

Expected final lengths: about 40 to 170 moves for total 17 to 25 problems. That wins outright where we are the only solver (uncertified, climb-needing). For no-climb problems that other teams may also solve, polishing will be needed to stay competitive.
## implementation_plan
1) engine/canon.hpp (new, about 600 LOC):
   - Canonical key: packed u64/u128 words, cyc_canon, B2 table, pair canonicalization, hash.
   - Move generator with junction-table prefilter; u-moves optional.
   - Packed NodeStore (about 24 B per node) and visited HashSet (reuse search.hpp HashSet).
   - CanonSearch: bucket queue over (key, total), iterative cap with per-node thr, stop tests (target, 1-letter relator, corridor, core set), budgets.
   - extract_class_path and compact_class_path (shortcut DP).
   - Realizer: peel, median conjugator, beam K, finish via greedy descent plus endgame or SWAP.
   - Every emitted path is replayed with ac::replay.
2) engine/search.hpp (+40 LOC):
   - run_search strategy 'canon' -> search_canon(start, P, C). Fill SearchResult (path, nodes, note).
   - New Params: canon_L (max cap, default start+14), canon_U = 0, canon_auto = 1, canon_max_states = 2e7, canon_compact = 1, canon_beam = 8.
3) engine/main.cpp (+60 LOC):
   - Parse the new flags.
   - New command 'canon-sig' (JSONL in, out: {id, peak_reached, exhausted_cap, min_total, min_class, low_classes[64], comp_sizes}).
   - Optional --core-set file with classes of known-hard cores.
4) engine/corridor.hpp (+120 LOC): CanonCorridor mapping class hash -> (path id, index), with splice and bridge (conjugations, inversion, B2 and sigma move transform), then finish.
5) acsolver (about 250 LOC):
   - Presets in loop.py: 'canon' (30 s, 2e7 states, 1 thread each) and 'canon_deep' (cap start+18, 3 h, 1e8 states, 1 thread, 6 GB, for cores only).
   - db.py: table canon_signature(problem_id, cap, exhausted, peak, min_total, min_class, low_classes, core_label).
   - clusters.py: union-find, core labels (AK(n) via ms1190 and family helpers), splice jobs.
   - controller.py: when U-mode exhaustion proves no path below peak P, the controller should not request smaller caps.
6) tests/test_canon.py (about 150 LOC):
   - Key invariance under random rotation, inversion, swap and B2.
   - xcheck: exact-projection equality at L <= 21 on 3 problems.
   - Realize-and-official-verify on 10 problems.
   - B2/sigma move-transform property.
Total about 1,200 LOC. The scratch prototypes are ready to port: cbfs2.cpp (search) and realize_opt.py (realizer).
## risks
- Hard cores grow 2 to 3.5 times per level, so peaks above about 32 for 15-letter cores (or above start+15 for long words) are infeasible on 15 GB. AK(3) and AK(4) equivalents, the MS-1190 open set and explicit MS(n>=8) starts will mostly stay unsolved. Measured: 0/10 open, 0/30 greedy_failed_short, ac-01960 closed through +22.
- U=0 is not complete. U-moves add 1.5% to 3% more classes, and their branching grows like 3^|u|. Use them only in proof or deep mode.
- Speed is about 25k to 65k classes per second. The fixed-cap prototype stores the fringe: it hit 70 times the true component for AK(3) at a cap of 60. The threshold-based iterative cap is required before production.
- The B2 quotient costs up to 2.2 times the CPU on components that are not B2-closed (ac-00392), but saves 8 times on closed ones. Keep it on, with a per-run flag.
- Realized paths are long (45 to 164 moves after shortening). For problems that other teams also solve, we may lose on length unless compaction, beam realization and polishing are done.
- 64-bit hash collisions can only drop states (a negligible probability at 1e8 states). They can never produce a wrong path, because the realizer re-derives every step from words and the official verifier checks the result.
- The Python realizer is slow without the length prefilter; it must be ported to C++.
- The projected 40% to 50% bench80 rate is an extrapolation from about 25 sampled problems at 10 to 33 s. The full sweep has not been run.
================= global-trivial-component GTC-canon: global trivial component in cyclic-word space, plus a per-problem minimax flood with rigorous barrier bounds
## summary
Precomputing the length-capped trivial component over EXACT states is not workable. It holds 14.4M states at L=14 and grows about 3x per letter, while the hard problems need peaks of L >= 19-33. It becomes workable in a quotient: pairs of cyclically reduced words, modulo rotation, inversion, relator swap and the 8 signed generator permutations, with generalized product edges r_i <- CR(rot(r_i) * w * rot(r_j)^{+-1} * w^-1). That space is about 2000x smaller (T_20 = 2.88M states, built in 58 s single-threaded) and is a proven, exactly cross-checked image of the exact move graph. Per problem, a level-synchronous minimax flood (always expand the lowest canonical total length; raise the cap by one letter only when everything below is exhausted) runs until it touches the stored T_Ls or a store of already-solved canonical states. Each canonical step is then turned into roughly 4-6 official moves. Measured: 18/20 MS-1190 "uncertified" instances solved in 20 s total, bench80 21/80 at a 150K-state budget (vs exact GBFS 19/80 at 15M nodes), and 27/120 random unsolved pool problems at a 50K budget. That gives 71 new paths, all accepted by the official verifier and none already in the DB. Honest limits: the 30 greedy-failed short problems, the MS-1190 open instances and AK(3) are NOT solved. The flood instead proves barrier lower bounds of 25-41 for them and shows that some of them lie in the same component as AK(3) and as an open MS-1190 instance.
## why_it_climbs
Greedy descent explores only the sublevel set below the start. Every hard problem sits in a "pocket": the connected component C_c(P) of the graph restricted to states of total length <= c that does not contain the trivial presentation until c reaches the barrier B(P), the saddle height. The flood takes this on directly:
(1) Prim/minimax order. It pops the lowest-length frontier state, and raises the water level c -> c+1 only when C_c(P) is fully exhausted. So it climbs exactly as high as necessary and never higher; the max length along the path it finds equals B(P), which is optimal for the minimax objective. Right after it spills over the saddle, the lowest states are on the far side, so it immediately descends toward T.
(2) The pocket below the saddle must be exhausted no matter what, and in exact space that is hopeless (each canonical state expands into ~4*n0*n1 rotations/inversions times conjugate paddings; e.g. 54,336 exact states = 40 canonical states for ac-00008 at cap 20). In canonical space the pockets are small: 1K-300K states at cap 27 for the greedy-failed short problems, and <= 1M for most MS-1190 uncertified ones (water 19-31). So exhausting them is cheap.
(3) The stored component T_Ls (BFS distances to [x,y] within cap Ls) turns "reach (x,y)" into "touch any trivial low state". Ablation on the uncertified set: visited states fall 3-10x from Ls=2 to Ls=16 (ac-00251: 1.35M -> 154K; ac-00869: 1.25M -> 81K) and the required water level is unchanged. On long problems a larger Ls also adds solves: T_20 rescued 6 of 77 long failures that T_18 missed at the same budget.
(4) Exhaustion is a proof. Every exact AC path with exact lengths <= c maps to a canonical path with canonical lengths <= c (exact length >= canonical length, and each exact move is either class-preserving or one generalized product). So "exhausted at level c without a hit" proves no exact solution peaks at <= c. This gives rigorous barrier lower bounds and tells us which problems not to waste compute on.
## state_and_move_realization
Exact state S = (r0,r1), arbitrary reduced words. Each canonical step S -> class K' is realized as follows (implemented and verified in the prototype, realize_step in gtc2.cpp):
1. Decompose r = h c h^-1, with c cyclically reduced, for both relators.
2. Enumerate the neighbour edges of (c0,c1) with cap = total(K'). Keep edges e = (i, a = rot_k(c_i), b = rot_l(c_j^s), w) whose canonical key equals K'. Since keys come from the actual words, the 8 automorphisms and the swap never need to be realized.
3. For the edge, g_i is in {h_i p, h_i q^-1}, where c_i = p q and a = q p = p^-1 c_i p. Likewise g_j is one of two options. Let z = reduce(g_i w g_j^-1).
   Mode A: conjugate r_j by z, i.e. moves 10..13 or 6..9 applied innermost letter first, |z| moves.
   Mode B: conjugate r_i by z^-1.
   Then one multiplication move: 2/3 when i=0, 4/5 when i=1, with +1 when s means the inverse.
   Then cyclically reduce both relators by conjugating with the inverse of each outer letter (|h| moves each).
   The product's cyclic class is class(a w b w^-1) = K' exactly, by group identities.
4. Of the <= 8 variants, simulate each with apply_move and keep the fewest moves. Assert canon(new state) == K'.
5. After the last step the state is (x^+-1, y^+-1) or swapped. Cyclically reduce it, then finish with the endgame table, which needs <= ~4 moves from any orbit element.
6. Replay with ac::replay, then the official verifier.
Cost: measured 4.1-5.7 exact moves per canonical step (ac-00083: 18 steps -> 76 moves; ac-01032: 21 -> 98; ac-00676: 493 -> 2045). Exact peak length = canonical peak + 2|z| + small, measured 21-39. The realization itself takes milliseconds. A naive version without per-step cyclic reduction let conjugators accumulate (1072 moves, peak 193 for ac-01032 vs 98 and 25 now).
## complexity
Canonical T_L (with generalized edges), single thread:
| L | states | BFS depth | time |
|---|---|---|---|
| 12 | 1,105 | | |
| 14 | 7,374 | | |
| 16 | 52,486 | 33 | 0.6 s |
| 17 | 171,684 | 42 | |
| 18 | 384,273 | 57 | 6 s |
| 19 | 1,273,601 | 86 | 23 s |
| 20 | 2,881,349 | 101 | 58 s; 42 MB as 64-bit hash, ~26 MB as sorted keys+2-bit dist |
Growth is x7.5 per 2 letters. Projected (8.25 B/state):
- T_22 ~22M: ~10 min single thread / ~3 min on 4 threads, 180 MB.
- T_24 ~160M: ~1.5 h / ~25 min, 1.3 GB on disk, ~3.7 GB RAM hash during the build.
- T_26 ~1.2B: ~12-15 h single thread, 10 GB on disk. Needs external BFS: Korf-style delayed duplicate detection with hash-bucketed layer files, sort-unique per bucket, subtracting layers d and d-1 (enough because the graph is undirected).
- T_27 ~4B / 33 GB exceeds the 30 GB of free disk.
Exact-state comparison: T_12 = 1.58M, T_13 = 6.48M, T_14 = 14.4M (21 s, depth 49), i.e. ~1950x the canonical T_14. Exact T_16 ~130M and T_18 ~1.2B, so exact storage tops out around L=17, which covers none of the hard problems.
Flood: 15-20 us per visited state at water 25-30 (500K visited in 7-12 s; 2M in 35 s); ~65 B/state in the prototype (128-bit key map + parent + PQ), so 1e8 states = 6.5 GB.
Pocket growth: ~x3 per water level (ac-00008: 1,097 at 24 -> 13,325 at 27 -> 1.58M at 31), so barriers of 32-33 are the practical in-RAM limit.
Lookup cost: an O(1) hash probe or ~0.3 us mmap binary search.
## experiments
All code is in /tmp/claude-0/-home-user-SAIR-comp-2/5af7ac6c-728a-515a-9a31-33a98dd3e07f/scratchpad/design_global-trivial-component/ (gtc.cpp, gtc2.cpp, xcheck.cpp, dbg.cpp).
1. Exact capped BFS from (x,y): L = 10/11/12/13/14 gives 170K / 701K / 1.58M / 6.48M / 14.4M states, BFS depth 13/17/23/31/49.
2. Canonical T_L sizes as in complexity. Generalized w-edges add ~1% of states. Pool problems inside T_L: 100 (L=17), 147 (18), 230 (19), 292 (20); 212 of the 292 were unsolved in the DB. MS-1190 uncertified inside T_20: 5/8 eligible.
3. Soundness:
   - All 47 DB-solved problems whose path keeps CR length <= 17 are in T_17, 0 missing.
   - Exact BFS vs canonical BFS from the same problem gives identical class sets at caps 17/18/19/20 (ac-00008: 812/2716/19040/54336 exact = 3/6/16/40 classes) and at 34/36 (ac-01941).
4. Flood vs T_18, with realization and official verification:
   - MS-1190 uncertified: 18/20 HIT in 20 s total (water 17-31; canonical paths 13-493 steps; 76-2107 moves).
   - bench80: 21/80 at a 150K budget (~136 s total). With a 1M budget, 5 of the first 12 failures also solved.
   - Random 120 unsolved pool problems: 27/120 at 50K (0.39 s each). By initial length: 15-19: 4/13; 20-24: 11/19; 25-29: 9/40; 30-34: 2/42; 35+: 1/6.
   - T_20 rescued 6 of 77 long failures.
   - 71 new solutions in new_solutions.txt: 71/71 officially ok, none in the DB.
5. Ls ablation on the uncertified set: Ls=2: 17/20 (33 s); Ls=12: 17/20 (23 s); Ls=16: 18/20 (21 s); Ls=18: 18/20 (20 s). Water levels are identical.
6. Hard sets:
   - Greedy-failed short: 0/30. Pockets at cap 27 range from 13K to 297K states. Barrier lower bounds from budget runs: ac-00008 >= 31, ac-00066 >= 33, ac-00254 >= 30, ac-00392/00568/02698/02883/00413/00927 >= 28, ac-00137 >= 27 (4.3M states), ac-01083 >= 25.
   - ms1190_open: 0/10 at 500K, water 27-39; ac-01026 >= 41.
   - AK(3) (ac-00399): >= 27 with 2M states.
   - Shared fingerprints prove ac-00137 and ac-01083 are in AK(3)'s component, ac-00472 and ac-01440 are in open ac-02710's component, and ac-00392/00568/02698/02883 share one pocket.
   - In the random long failures, 70 distinct fingerprints among 77, and 53/77 descend to canonical length 14-18 before stalling.
7. Path quality on 40 DB-solved problems: flood solved 40/40 in 0.3 s. After a 3 s shorten (radius 3+3), paths were <= the DB best in 37/40 (median ratio 0.83). Shortening the 21 bench80 paths took 5485 -> 4974 moves.
## expected_coverage
- ms1190_uncertified: high. 18/20 measured, so ~150-170 of the 183 in the pool; the rest may need 10M budgets.
- bench80: 21/80 at 150K, and an estimated ~30-40/80 at 1M (5/12 failures solved at 1M). GBFS gets 19/80 at 15M nodes. The gain is in problems that need modest climbs (water up to +9 above the start) and in long problems whose descent ends in a mid-level trivial basin. A larger Ls (22-24) adds some more.
- Pool-wide: ~22-27% of the currently unsolved at 50K (~2,000-2,500 problems in ~1 CPU-hour), more with the budget ladder and T* sharing.
- greedy_failed_short: essentially 0. Measured barrier lower bounds are 25-33, pockets grow x3/level, and several of them are provably in AK(3)'s component or in an open MS-1190 component. Value: certified hardness, so no wasted compute.
- ms1190_open: 0 expected (open in the literature; water 27-41 without a hit).
- Problems of length >= 30 at small budgets: low (2/42), because most descend to a non-trivial low pocket at 14-18. They become solvable only when that pocket is solved and enters T*, which is why pocket fingerprint grouping matters.
## path_length_quality
Raw paths are already competitive, because T supplies BFS-shortest canonical descents. On 40 DB-solved problems, the flood plus a 3 s shorten beat or matched the DB best in 37/40 (median 0.83x). Weak spot: the flood part follows the Prim tree, which is not shortest (e.g. 442 flood steps for ac-00676 -> 2045 moves).
Plan:
(1) Once the barrier W* is known, rerun a plain BFS from P inside cap W* (and also W*+1, W*+2, since a higher cap can give much shorter paths). The objective is depth + T_dist; stop when depth exceeds best - min T_dist.
(2) Dijkstra on canonical states with edge weight = estimated realized cost (1 + |z| + CR moves, computed on canonical reps), so the canonical path is chosen by exact length.
(3) The realization already picks the cheapest of 8 variants per step. Extend this to a beam/DP over steps, because conjugator choices carry over to the next step.
(4) Run the existing shorten.hpp (cycle cut, commute_reduce, endgame/corridor truncation, ball-shortcut DP) with larger balls and more time for the final exact polish.
(5) Give T* the best-known remaining distance per canonical state, so later finishes reuse short tails.
Realization overhead is ~4-6 moves per canonical step; exact peaks stay within canonical peak + ~10.
## implementation_plan
Port the prototype gtc2.cpp (~640 lines, already working) into the engine.
- engine/canon.hpp (~450 lines): Key64/Key128, CODEK tables, least_rot2, Canon8 with lazy combine, canon_pair, pack/unpack, Edge, neighbours_w (cases i and ii), Map128.
- engine/trivial.hpp (~250 lines): build_trivial(L, threads), with a partitioned frontier and per-thread buffers merged per layer; save/load data/trivial_c{L}.bin as sorted keys + 2-bit dist + prefix index via mmap; lookup; descend(key) -> canonical path. Optional external-memory builder for L >= 25.
- engine/flood.hpp (~300 lines): the level-synchronous flood with budget, capmax, hit test against T and T*; returns path, water, barrier LB and fingerprint. Optimizations: per-state "smallest neighbour length above c" so re-expansion only touches states that have neighbours at the new level; 64-bit keys while total <= 27.
- engine/realize.hpp (~200 lines): realize_step, final cyclic reduction, endgame finish, replay check.
- engine/main.cpp (+120 lines): `build-trivial --cap L --out FILE`; `strategy=cflood` in run_search (Params.max_nodes = budget, maxlen = capmax), so the batch loop, shortening and official verification work unchanged; output fields water/barrier_lb/fingerprint.
- engine/corridor.hpp: an optional canonical T* loader from data/canon_corridors.bin (keys + remaining distance), appended by the Python side after each verified solve.
- acsolver/loop.py + controller.py (~150 lines): a "cflood" preset ladder (50K, 300K, 1M, 10M); store barrier_lb and fingerprint in problem_status; group problems by fingerprint; deprioritize AK(3)/open pockets.
- tests/test_canon.py (~100 lines).
Total ~1,500 lines. Order: canon + flood + realize (1 day), wire into solve/loop, build T_20 then T_22, run Phase 0-1 over the pool, then T* and the ladder.
## risks
- The hardest targets stay out of reach. Greedy-failed short problems, open MS-1190 and AK(3)-equivalents have proven barriers of 25-41, and pockets grow ~x3/level, so going past ~33 means 1e8-1e9+ canonical states per pocket. Treat these as certified-hard, not solvable.
- Long problems (>= 30, about 40% of the pool) solve poorly at small budgets, because they fall into those same hard low pockets. The gain there depends on T* sharing and larger budgets.
- A larger T helps only in the mid-level regime (+6/77 for T_20 vs T_18). T_24+ may give modest returns for hours of build time, so ablate before building.
- Memory: ~65 B per flood state in the prototype; floods above 1e8 states need compact keys or disk.
- The 128-bit key caps totals at 58; widen it if the climbs on long problems exceed that.
- Path lengths from deep floods can be long (up to 2107 moves) until the shortest-path rerun at W* is implemented.
- Canonical-graph degree is high (hundreds per state, plus conjugator words when there is slack under the cap), so each expansion is about 20 us.
- Equal fingerprints prove equivalence, but different fingerprints do not prove distinct pockets, so grouping is incomplete.
- Other designers are using the DB concurrently: the 71 new solutions are only in the scratch file and must be imported through the normal verified pipeline.
