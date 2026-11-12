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

/-- `M(n)` from the counts `a = #squarefree`, `c = #odd squarefree`: `a - 2c`. -/
def finish (a c : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.negSucc (Nat.sub (Nat.sub (Nat.add c c) a) (nat_lit 1)))
    (Int.ofNat (Nat.sub a (Nat.add c c))) (Nat.ble (Nat.add c c) a)

/-- Packed per-field sums for `k ≤ 48` (sieving primes [2, 3, 5]). -/
def packed48 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 576)) (nat_lit 4095)
  (Nat.add (Nat.add (Nat.add (Nat.mul (nat_lit 1552) ones) (Nat.mul (nat_lit 64) (Nat.shiftRight ones (nat_lit 72)))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x3a00023a) (nat_lit 576)) (nat_lit 0xffffffffffff)) (Nat.div (Nat.shiftLeft (nat_lit 0x36000000036000000236) (nat_lit 576)) (nat_lit 0xfffffffffffffffffffffffffff)))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 50) (nat_lit 576)) (nat_lit 0xfffffffffffffff)) (Nat.shiftLeft (nat_lit 512) (nat_lit 276))))

/-- `1` in the fields of squarefree `k ≤ 48`. -/
def sqf48 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 576)) (nat_lit 4095)
  Nat.xor (Nat.land (Nat.shiftRight packed48 (nat_lit 11)) ones) ones

/-- `1` in the fields of squarefree `k ≤ 48` with an odd number of prime factors. -/
def odd48 : Nat := Nat.land (Nat.shiftRight packed48 (nat_lit 6)) sqf48

/-- `M(n)` for `n ≤ 48`. -/
def fast48 (n : Nat) : Int :=
  let sh := Nat.mul (nat_lit 12) (Nat.sub (nat_lit 48) n)
  finish (Nat.mod (Nat.shiftRight sqf48 sh) (nat_lit 4095))
    (Nat.mod (Nat.shiftRight odd48 sh) (nat_lit 4095))

/-- Packed per-field sums for `k ≤ 120` (sieving primes [2, 3, 5, 7]). -/
def packed120 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 1440)) (nat_lit 4095)
  let sq := Nat.shiftLeft (nat_lit 512) (nat_lit 1440)
  (Nat.add (Nat.add (Nat.add (Nat.mul (nat_lit 1556) ones) (Nat.mul (nat_lit 64) (Nat.shiftRight ones (nat_lit 120)))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x3a00023a) (nat_lit 1440)) (nat_lit 0xffffffffffff)) (Nat.div (Nat.shiftLeft (nat_lit 0x36000000036000000236) (nat_lit 1440)) (nat_lit 0xfffffffffffffffffffffffffff)))) (Nat.add (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 50) (nat_lit 1440)) (nat_lit 0xfffffffffffffff)) (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 300)) (nat_lit 1)))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 47) (nat_lit 1440)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 84)) (nat_lit 1))) (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 588)) (nat_lit 1))))))

/-- `1` in the fields of squarefree `k ≤ 120`. -/
def sqf120 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 1440)) (nat_lit 4095)
  Nat.xor (Nat.land (Nat.shiftRight packed120 (nat_lit 11)) ones) ones

/-- `1` in the fields of squarefree `k ≤ 120` with an odd number of prime factors. -/
def odd120 : Nat := Nat.land (Nat.shiftRight packed120 (nat_lit 6)) sqf120

/-- `M(n)` for `n ≤ 120`. -/
def fast120 (n : Nat) : Int :=
  let sh := Nat.mul (nat_lit 12) (Nat.sub (nat_lit 120) n)
  finish (Nat.mod (Nat.shiftRight sqf120 sh) (nat_lit 4095))
    (Nat.mod (Nat.shiftRight odd120 sh) (nat_lit 4095))

/-- Packed per-field sums for `k ≤ 528` (sieving primes [2, 3, 5, 7, 11, 13, 17, 19]). -/
def packed528 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 6336)) (nat_lit 4095)
  let sq := Nat.shiftLeft (nat_lit 512) (nat_lit 6336)
  (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (nat_lit 1558) ones) (Nat.mul (nat_lit 64) (Nat.shiftRight ones (nat_lit 264)))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 0x3b00023b) (nat_lit 6336)) (nat_lit 0xffffffffffff)) (Nat.div (Nat.shiftLeft (nat_lit 0x38000000038000000238) (nat_lit 6336)) (nat_lit 0xfffffffffffffffffffffffffff)))) (Nat.add (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 52) (nat_lit 6336)) (nat_lit 0xfffffffffffffff)) (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 300)) (nat_lit 1)))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 50) (nat_lit 6336)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 84)) (nat_lit 1))) (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 588)) (nat_lit 1)))))) (Nat.add (Nat.add (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 47) (nat_lit 6336)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 132)) (nat_lit 1))) (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1452)) (nat_lit 1)))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 45) (nat_lit 6336)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 156)) (nat_lit 1))) (Nat.div sq (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2028)) (nat_lit 1))))) (Nat.add (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 44) (nat_lit 6336)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 204)) (nat_lit 1))) (Nat.shiftLeft (nat_lit 512) (nat_lit 2868))) (Nat.add (Nat.div (Nat.shiftLeft (nat_lit 43) (nat_lit 6336)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 228)) (nat_lit 1))) (Nat.shiftLeft (nat_lit 512) (nat_lit 2004))))))

/-- `1` in the fields of squarefree `k ≤ 528`. -/
def sqf528 : Nat :=
  let ones := Nat.div (Nat.shiftLeft (nat_lit 1) (nat_lit 6336)) (nat_lit 4095)
  Nat.xor (Nat.land (Nat.shiftRight packed528 (nat_lit 11)) ones) ones

/-- `1` in the fields of squarefree `k ≤ 528` with an odd number of prime factors. -/
def odd528 : Nat := Nat.land (Nat.shiftRight packed528 (nat_lit 6)) sqf528

/-- `M(n)` for `n ≤ 528`. -/
def fast528 (n : Nat) : Int :=
  let sh := Nat.mul (nat_lit 12) (Nat.sub (nat_lit 528) n)
  finish (Nat.mod (Nat.shiftRight sqf528 sh) (nat_lit 4095))
    (Nat.mod (Nat.shiftRight odd528 sh) (nat_lit 4095))


/-- Fast path, correct for `n ≤ 528`: dispatch to the smallest tier. -/
def fast (n : Nat) : Int :=
  Bool.rec (motive := fun _ => Int)
    (Bool.rec (motive := fun _ => Int) (fast528 n) (fast120 n) (Nat.ble n (nat_lit 120)))
    (fast48 n) (Nat.ble n (nat_lit 48))

/-- Fallback for large `n`. -/
def slow (n : Nat) : Int := ∑ k ∈ Finset.range (n + 1), moebiusByFactors k

def impl (n : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (slow n) (fast n) (Nat.ble n (nat_lit 528))

/-! ## Correctness -/

theorem fast_zero : fast 0 = 0 := by decide +kernel

theorem fast_step : ∀ n < 528, fast (n + 1) = fast n + moebiusByFactors (n + 1) := by
  decide +kernel

theorem fast_eq : ∀ n ≤ 528, fast n = slow n := by
  intro n
  induction n with
  | zero => intro _; rw [fast_zero]; simp [slow, moebiusByFactors]
  | succ n ih =>
    intro h
    rw [fast_step n (by omega), ih (by omega), slow, slow, Finset.sum_range_succ _ (n + 1)]

theorem impl_correct : ∀ n, impl n = mertensSpec n := by
  intro n
  have hs : slow n = mertensSpec n := by
    simp only [slow, mertensSpec, moebiusByFactors_eq]
  unfold impl
  cases h : Nat.ble n 528
  · exact hs
  · exact (fast_eq n (Nat.le_of_ble_eq_true h)).trans hs

end Submission
