import Spec

/-!
# Mertens function via a packed (SWAR) sieve

For `n ≤ 528 = 23² - 1` the Möbius values of all `k ≤ 528` are computed at once in one
big natural number with 16-bit fields (field at position `528 - k` describes `k`), using a
few dozen kernel-accelerated big-number operations; larger `n` fall back to a direct sum.

Per field we accumulate, with one geometric-series division per comb
(`v * X^528 / (X^m - 1)` puts `v` into the fields of all multiples of `m`, `X = 2^16`):
* for each prime `p ≤ 19`: `2^10 - w p`, where `w p ≈ 64·log₂ p`;
* for each prime `p ≤ 19`: `-2^13` if `p² ∣ k`;
* a ramp `2^15 + 288` (`k ≤ 22`) or `2^15 + 1312` (`k ≥ 23`).
Since `k ≤ 528` has at most one prime factor `q ≥ 23`, the approximate logarithm of
`k / (product of its small prime factors)` (ramp minus the `w p`) is `≥ 2^10` exactly when
such a `q` exists; adding `2^10 · #(small prime factors)` makes bit 10 the parity of the
number of distinct prime factors, and bit 15 is set exactly when `k` is squarefree.
Then `M(n) = #{k ≤ n squarefree} - 2·#{k ≤ n squarefree, odd}`, both counts read off with
one shift and one `mod (2^16 - 1)` (the sum of the fields).
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

/-- `X^528` with `X = 2^16`. -/
def XL : Nat := Nat.shiftLeft 1 (nat_lit 8448)

/-- `v` in every field `528 - k` with `m ∣ k`, `1 ≤ k ≤ 528`. -/
def comb (m v : Nat) : Nat :=
  Nat.div (Nat.mul v XL) (Nat.sub (Nat.shiftLeft 1 (Nat.mul (nat_lit 16) m)) 1)

/-- `1` in every field `528 - k`, `1 ≤ k ≤ 528`. -/
def ones : Nat := Nat.div XL (nat_lit 65535)

/-- The packed per-field sums described in the module docstring. -/
def packed : Nat :=
  Nat.sub
    (Nat.add
      (Nat.add (Nat.mul (nat_lit 33056) ones)
        (Nat.mul (nat_lit 1024) (Nat.shiftRight ones (nat_lit 352))))
      (Nat.add
        (Nat.add (Nat.add (comb 2 (nat_lit 960)) (comb 3 (nat_lit 923)))
          (Nat.add (comb 5 (nat_lit 875)) (comb 7 (nat_lit 844))))
        (Nat.add (Nat.add (comb 11 (nat_lit 803)) (comb 13 (nat_lit 787)))
          (Nat.add (comb 17 (nat_lit 762)) (comb 19 (nat_lit 752))))))
    (Nat.add
      (Nat.add (Nat.add (comb 4 (nat_lit 8192)) (comb 9 (nat_lit 8192)))
        (Nat.add (comb 25 (nat_lit 8192)) (comb 49 (nat_lit 8192))))
      (Nat.add (Nat.add (comb 121 (nat_lit 8192)) (comb 169 (nat_lit 8192)))
        (Nat.add (comb 289 (nat_lit 8192)) (comb 361 (nat_lit 8192)))))

/-- `1` in the fields of squarefree `k`. -/
def sqf : Nat := Nat.land (Nat.shiftRight packed (nat_lit 15)) ones

/-- `1` in the fields of squarefree `k` with an odd number of prime factors. -/
def odd : Nat := Nat.land (Nat.shiftRight packed (nat_lit 10)) sqf

/-- `M(n)` from the counts `a = #squarefree`, `c = #odd squarefree`: `a - 2c`. -/
def finish (a c : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.negSucc (Nat.sub (Nat.sub (Nat.add c c) a) 1))
    (Int.ofNat (Nat.sub a (Nat.add c c))) (Nat.ble (Nat.add c c) a)

/-- Fast path, correct for `n ≤ 528`. -/
def fast (n : Nat) : Int :=
  let sh := Nat.mul (nat_lit 16) (Nat.sub (nat_lit 528) n)
  finish (Nat.mod (Nat.shiftRight sqf sh) (nat_lit 65535))
    (Nat.mod (Nat.shiftRight odd sh) (nat_lit 65535))

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
