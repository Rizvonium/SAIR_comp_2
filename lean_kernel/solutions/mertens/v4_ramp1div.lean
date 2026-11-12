import Spec

/-!
# Mertens function via packed (SWAR) sieves

For `n ≤ 528 = 23² - 1` the Möbius values of all `k ≤ L` (`L = 48, 120` or `528`, the
smallest tier containing `n`) are computed at once in one big natural number with 12-bit
fields (the field at position `L - k` describes `k`), using a few dozen kernel-accelerated
big-number operations; larger `n` fall back to a direct sum.

Per field we accumulate, with one geometric-series division per comb
(`v * X^L / (X^m - 1)` puts `v` into the fields of all multiples `k ≤ L` of `m`, `X = 2^12`;
for `m = 2, 3` the combs of `m` and `m²` share one division, and a comb with a single
tooth is a plain shift):
* for each sieving prime `p` (all primes `≤ √L`): `2^6 - w p`, where `w p ≈ c·log₂ p`;
* for each sieving prime with `p² ≤ L`: `2^9` if `p² ∣ k`;
* a constant `3·2^9 + a₀`, plus a ramp step `2^6` for `k ≥` the first non-sieving prime.
Since `k ≤ L` has at most one prime factor `q` outside the sieving primes, the approximate
logarithm of `k / (product of its sieving prime factors)` (ramp minus the `w p`) is
`≥ 2^6` exactly when such a `q` exists; adding `2^6 · #(sieving prime factors)` makes bit 6
the parity of the number of distinct prime factors, and bit 11 is set exactly when `k` is
not squarefree.  Then `M(n) = #{k ≤ n squarefree} - 2·#{k ≤ n squarefree, odd}`, both
counts read off with one shift and one `mod (2^12 - 1)` (the sum of the fields).
The constants were chosen so that this is exact for all `k ≤ L`; the proof checks the
fast path against the definition of `μ` for every `n ≤ 528` by kernel evaluation.
-/

namespace Submission

/-- `moebius` via prime factor lists (only used for the fallback and in proofs). -/
def moebiusByFactors (n : Nat) : Int :=
  if n = 0 then 0
  else if n.primeFactorsList.Nodup then (-1 : Int) ^ n.primeFactorsList.length else 0

theorem moebiusByFactors_eq (n : Nat) : moebiusByFactors n = ArithmeticFunction.moebius n := by
  by_cases hn : n = 0
  · subst n
    simp [moebiusByFactors]
  · simp only [moebiusByFactors, if_neg hn, ArithmeticFunction.moebius, ArithmeticFunction.coe_mk,
      ← Nat.squarefree_iff_nodup_primeFactorsList hn, ArithmeticFunction.cardFactors_apply]

/-- `a - b` as an integer. -/
def ofDiff (a b : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.negSucc (Nat.sub (Nat.sub b a) (nat_lit 1)))
    (Int.ofNat (Nat.sub a b)) (Nat.ble b a)

/-- Packed per-field sums for `k ≤ 48` (sieving primes [2, 3, 5]). -/
def packed48 : Nat :=
  (Nat.add (Nat.add (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x610000000000000000040) (nat_lit 504)) (nat_lit 4095)) (Nat.div (Nat.shiftLeft (nat_lit 0x3a00023a) (nat_lit 576)) (nat_lit 0xffffffffffff))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x36000000036000000236) (nat_lit 576)) (nat_lit 0xfffffffffffffffffffffffffff)) (Nat.div (Nat.shiftLeft (nat_lit 50) (nat_lit 576)) (nat_lit 0xfffffffffffffff)))) (Nat.shiftLeft (nat_lit 512) (nat_lit 276)))

/-- `1 + μ k` in the field of each `k ≤ 48`: bit 11 of `packed48` marks non-squarefree `k`,
bit 6 the parity of the number of prime factors. -/
def mu1_48 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 576)) (nat_lit 4095)
  let sqf := Nat.xor (Nat.land (Nat.shiftRight packed48 (nat_lit 11)) ones) ones
  Nat.sub (Nat.add ones sqf) (Nat.shiftLeft (Nat.land (Nat.shiftRight packed48 (nat_lit 6)) sqf) (nat_lit 1))

/-- `M(n)` for `n ≤ 48`: the fields of `k ≤ n` sum to `n + M(n)`. -/
def fast48 (n : Nat) : Int :=
  ofDiff (Nat.mod (Nat.shiftRight mu1_48 (Nat.mul (nat_lit 12) (Nat.sub (nat_lit 48) n))) (nat_lit 4095)) n


/-- Packed per-field sums for `k ≤ 120` (sieving primes [2, 3, 5, 7]). -/
def packed120 : Nat :=
  let sq := Nat.shiftLeft (nat_lit 512) (nat_lit 1440)
  (Nat.add (Nat.add (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x614000000000000000000000000000040) (nat_lit 1320)) (nat_lit 4095)) (Nat.div (Nat.shiftLeft (nat_lit 0x3a00023a) (nat_lit 1440)) (nat_lit 0xffffffffffff))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x36000000036000000236) (nat_lit 1440)) (nat_lit 0xfffffffffffffffffffffffffff)) (Nat.div (Nat.shiftLeft (nat_lit 50) (nat_lit 1440)) (nat_lit 0xfffffffffffffff)))) (Nat.add (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 300)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 47) (nat_lit 1440)) (nat_lit 0xfffffffffffffffffffff))) (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 588)) (nat_lit 1)))))

/-- `1 + μ k` in the field of each `k ≤ 120`: bit 11 of `packed120` marks non-squarefree `k`,
bit 6 the parity of the number of prime factors. -/
def mu1_120 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 1440)) (nat_lit 4095)
  let sqf := Nat.xor (Nat.land (Nat.shiftRight packed120 (nat_lit 11)) ones) ones
  Nat.sub (Nat.add ones sqf) (Nat.shiftLeft (Nat.land (Nat.shiftRight packed120 (nat_lit 6)) sqf) (nat_lit 1))

/-- `M(n)` for `n ≤ 120`: the fields of `k ≤ n` sum to `n + M(n)`. -/
def fast120 (n : Nat) : Int :=
  ofDiff (Nat.mod (Nat.shiftRight mu1_120 (Nat.mul (nat_lit 12) (Nat.sub (nat_lit 120) n))) (nat_lit 4095)) n


/-- Packed per-field sums for `k ≤ 168` (sieving primes [2, 3, 5, 7, 11]). -/
def packed168 : Nat :=
  let sq := Nat.shiftLeft (nat_lit 512) (nat_lit 2016)
  (Nat.add (Nat.add (Nat.add (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x616000000000000000000000000000000000040) (nat_lit 1872)) (nat_lit 4095)) (Nat.div (Nat.shiftLeft (nat_lit 0x3a00023a) (nat_lit 2016)) (nat_lit 0xffffffffffff))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x36000000036000000236) (nat_lit 2016)) (nat_lit 0xfffffffffffffffffffffffffff)) (Nat.div (Nat.shiftLeft (nat_lit 50) (nat_lit 2016)) (nat_lit 0xfffffffffffffff)))) (Nat.add (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 300)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 47) (nat_lit 2016)) (nat_lit 0xfffffffffffffffffffff))) (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 588)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 43) (nat_lit 2016)) (nat_lit 0xfffffffffffffffffffffffffffffffff))))) (Nat.shiftLeft (nat_lit 512) (nat_lit 564)))

/-- `1 + μ k` in the field of each `k ≤ 168`: bit 11 of `packed168` marks non-squarefree `k`,
bit 6 the parity of the number of prime factors. -/
def mu1_168 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 2016)) (nat_lit 4095)
  let sqf := Nat.xor (Nat.land (Nat.shiftRight packed168 (nat_lit 11)) ones) ones
  Nat.sub (Nat.add ones sqf) (Nat.shiftLeft (Nat.land (Nat.shiftRight packed168 (nat_lit 6)) sqf) (nat_lit 1))

/-- `M(n)` for `n ≤ 168`: the fields of `k ≤ n` sum to `n + M(n)`. -/
def fast168 (n : Nat) : Int :=
  ofDiff (Nat.mod (Nat.shiftRight mu1_168 (Nat.mul (nat_lit 12) (Nat.sub (nat_lit 168) n))) (nat_lit 4095)) n


/-- Packed per-field sums for `k ≤ 360` (sieving primes [2, 3, 5, 7, 11, 13, 17]). -/
def packed360 : Nat :=
  let sq := Nat.shiftLeft (nat_lit 512) (nat_lit 4320)
  (Nat.add (Nat.add (Nat.add (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x61a000000000000000000000000000000000000000000000000000040) (nat_lit 4104)) (nat_lit 4095)) (Nat.div (Nat.shiftLeft (nat_lit 0x3a00023a) (nat_lit 4320)) (nat_lit 0xffffffffffff))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x36000000036000000236) (nat_lit 4320)) (nat_lit 0xfffffffffffffffffffffffffff)) (Nat.div (Nat.shiftLeft (nat_lit 50) (nat_lit 4320)) (nat_lit 0xfffffffffffffff)))) (Nat.add (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 300)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 47) (nat_lit 4320)) (nat_lit 0xfffffffffffffffffffff))) (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 588)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 43) (nat_lit 4320)) (nat_lit 0xfffffffffffffffffffffffffffffffff))))) (Nat.add (Nat.add (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1452)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 42) (nat_lit 4320)) (nat_lit 0xfffffffffffffffffffffffffffffffffffffff))) (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2028)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 39) (nat_lit 4320)) (nat_lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffff)))) (Nat.shiftLeft (nat_lit 512) (nat_lit 852))))

/-- `1 + μ k` in the field of each `k ≤ 360`: bit 11 of `packed360` marks non-squarefree `k`,
bit 6 the parity of the number of prime factors. -/
def mu1_360 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 4320)) (nat_lit 4095)
  let sqf := Nat.xor (Nat.land (Nat.shiftRight packed360 (nat_lit 11)) ones) ones
  Nat.sub (Nat.add ones sqf) (Nat.shiftLeft (Nat.land (Nat.shiftRight packed360 (nat_lit 6)) sqf) (nat_lit 1))

/-- `M(n)` for `n ≤ 360`: the fields of `k ≤ n` sum to `n + M(n)`. -/
def fast360 (n : Nat) : Int :=
  ofDiff (Nat.mod (Nat.shiftRight mu1_360 (Nat.mul (nat_lit 12) (Nat.sub (nat_lit 360) n))) (nat_lit 4095)) n


/-- Packed per-field sums for `k ≤ 528` (sieving primes [2, 3, 5, 7, 11, 13, 17, 19]). -/
def packed528 : Nat :=
  let sq := Nat.shiftLeft (nat_lit 512) (nat_lit 6336)
  (Nat.add (Nat.add (Nat.add (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x616000000000000000000000000000000000000000000000000000000000000000040) (nat_lit 6072)) (nat_lit 4095)) (Nat.div (Nat.shiftLeft (nat_lit 0x3b00023b) (nat_lit 6336)) (nat_lit 0xffffffffffff))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x38000000038000000238) (nat_lit 6336)) (nat_lit 0xfffffffffffffffffffffffffff)) (Nat.div (Nat.shiftLeft (nat_lit 52) (nat_lit 6336)) (nat_lit 0xfffffffffffffff)))) (Nat.add (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 300)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 50) (nat_lit 6336)) (nat_lit 0xfffffffffffffffffffff))) (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 588)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 47) (nat_lit 6336)) (nat_lit 0xfffffffffffffffffffffffffffffffff))))) (Nat.add (Nat.add (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1452)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 45) (nat_lit 6336)) (nat_lit 0xfffffffffffffffffffffffffffffffffffffff))) (Nat.add (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2028)) (nat_lit 1))) (Nat.div (Nat.shiftLeft (nat_lit 44) (nat_lit 6336)) (nat_lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffff)))) (Nat.add (Nat.add (Nat.shiftLeft (nat_lit 512) (nat_lit 2868)) (Nat.div (Nat.shiftLeft (nat_lit 43) (nat_lit 6336)) (nat_lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffff))) (Nat.shiftLeft (nat_lit 512) (nat_lit 2004)))))

/-- `1 + μ k` in the field of each `k ≤ 528`: bit 11 of `packed528` marks non-squarefree `k`,
bit 6 the parity of the number of prime factors. -/
def mu1_528 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 6336)) (nat_lit 4095)
  let sqf := Nat.xor (Nat.land (Nat.shiftRight packed528 (nat_lit 11)) ones) ones
  Nat.sub (Nat.add ones sqf) (Nat.shiftLeft (Nat.land (Nat.shiftRight packed528 (nat_lit 6)) sqf) (nat_lit 1))

/-- `M(n)` for `n ≤ 528`: the fields of `k ≤ n` sum to `n + M(n)`. -/
def fast528 (n : Nat) : Int :=
  ofDiff (Nat.mod (Nat.shiftRight mu1_528 (Nat.mul (nat_lit 12) (Nat.sub (nat_lit 528) n))) (nat_lit 4095)) n

/-- Fallback for large `n`. -/
def slow (n : Nat) : Int := ∑ k ∈ Finset.range (n + 1), moebiusByFactors k

/-- Dispatch to the smallest tier containing `n`, or the fallback for `n > 528`. -/
def impl (n : Nat) : Int :=
  (Bool.rec (motive := fun _ => Int) (Bool.rec (motive := fun _ => Int) (Bool.rec (motive := fun _ => Int) (slow n) (fast528 n) (Nat.ble n (nat_lit 528))) (fast360 n) (Nat.ble n (nat_lit 360))) (Bool.rec (motive := fun _ => Int) (Bool.rec (motive := fun _ => Int) (fast168 n) (fast120 n) (Nat.ble n (nat_lit 120))) (fast48 n) (Nat.ble n (nat_lit 48))) (Nat.ble n (nat_lit 168)))

/-! ## Correctness -/

theorem impl_zero : impl 0 = 0 := by decide +kernel

theorem impl_step : ∀ n < 528, impl (n + 1) = impl n + moebiusByFactors (n + 1) := by
  decide +kernel

theorem impl_le : ∀ n ≤ 528, impl n = slow n := by
  intro n
  induction n with
  | zero => intro _; rw [impl_zero]; simp [slow, moebiusByFactors]
  | succ n ih =>
    intro h
    rw [impl_step n (by omega), ih (by omega), slow, slow, Finset.sum_range_succ _ (n + 1)]

theorem impl_gt (n : Nat) (h : 528 < n) : impl n = slow n := by
  have hb : ∀ m, m ≤ 528 → Nat.ble n m = false := fun m hm => by
    cases hc : Nat.ble n m
    · rfl
    · have := Nat.le_of_ble_eq_true hc; omega
  unfold impl
  rw [hb 48 (by norm_num), hb 120 (by norm_num), hb 168 (by norm_num), hb 360 (by norm_num), hb 528 (by norm_num)]

theorem impl_correct : ∀ n, impl n = mertensSpec n := by
  intro n
  have hs : slow n = mertensSpec n := by
    simp only [slow, mertensSpec, moebiusByFactors_eq]
  rw [← hs]
  rcases Nat.lt_or_ge 528 n with h | h
  · exact impl_gt n h
  · exact impl_le n h

end Submission
