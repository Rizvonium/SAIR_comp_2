import Spec

/-!
Fast doubling over the binary digits of `n`, most significant first.

State after processing the top bits: `(F m, F (m + 1))` where `m = n >>> i`.
One doubling step with the next bit `b`:
  F(2m)   = F(m) * (2 F(m+1) - F(m))
  F(2m+1) = F(m)^2 + F(m+1)^2
  F(2m+2) = F(2m) + F(2m+1)
The computation is written with the kernel's accelerated primitives
(`Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.land`, `Nat.shiftRight`, `Nat.beq`, `Nat.log2`)
and a single raw `Nat.rec` loop, so the kernel spends its time in big-number
arithmetic instead of unfolding typeclass instances or recursion compilers.
-/

namespace Submission

/-- One doubling step: from `(F m, F (m+1))` to `(F (2m+bit), F (2m+bit+1))`. -/
def dstep (bit : Bool) (p : Nat × Nat) : Nat × Nat :=
  let a := p.1
  let b := p.2
  let c := Nat.mul a (Nat.sub (Nat.add b b) a)
  let d := Nat.add (Nat.mul a a) (Nat.mul b b)
  cond bit (d, Nat.add c d) (c, d)

/-- Bit `i` of `n` as a `Bool`, using primitives only. -/
def bitAt (n i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight n i) 1) 1

/-- After `t` steps the state describes the prefix `n >>> (L - t)`. -/
def run (n L : Nat) (t : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (0, 1)
    (fun t p => dstep (bitAt n (Nat.sub (Nat.sub L t) 1)) p) t

def impl (n : Nat) : Nat :=
  let L := Nat.add (Nat.log2 n) 1
  (run n L L).1

/-! ## Correctness -/

theorem bitAt_eq (n i : Nat) : bitAt n i = decide ((n >>> i) % 2 = 1) := by
  unfold bitAt
  rw [show Nat.land (Nat.shiftRight n i) 1 = (n >>> i) % 2 from Nat.and_one_is_mod _]
  rcases Nat.mod_two_eq_zero_or_one (n >>> i) with h | h <;> rw [h] <;> rfl

theorem shift_split (n i : Nat) : n >>> i = 2 * (n >>> (i + 1)) + (n >>> i) % 2 := by
  have h1 : n >>> (i + 1) = (n >>> i) / 2 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [h1]
  exact (Nat.div_add_mod _ 2).symm

theorem dstep_spec (m : Nat) (bit : Bool) :
    dstep bit (Nat.fib m, Nat.fib (m + 1)) =
      (Nat.fib (2 * m + cond bit 1 0), Nat.fib (2 * m + cond bit 1 0 + 1)) := by
  have he : Nat.fib (2 * m) = Nat.fib m * (2 * Nat.fib (m + 1) - Nat.fib m) := Nat.fib_two_mul m
  have ho : Nat.fib (2 * m + 1) = Nat.fib m * Nat.fib m + Nat.fib (m + 1) * Nat.fib (m + 1) := by
    rw [Nat.fib_two_mul_add_one, pow_two, pow_two, Nat.add_comm]
  have hs : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
  have h2 : 2 * Nat.fib (m + 1) = Nat.fib (m + 1) + Nat.fib (m + 1) := by omega
  cases bit
  · show (Nat.fib m * (Nat.fib (m + 1) + Nat.fib (m + 1) - Nat.fib m),
        Nat.fib m * Nat.fib m + Nat.fib (m + 1) * Nat.fib (m + 1)) = _
    simp only [cond_false, Nat.add_zero]
    rw [he, ho, h2]
  · show (Nat.fib m * Nat.fib m + Nat.fib (m + 1) * Nat.fib (m + 1),
        Nat.fib m * (Nat.fib (m + 1) + Nat.fib (m + 1) - Nat.fib m) +
          (Nat.fib m * Nat.fib m + Nat.fib (m + 1) * Nat.fib (m + 1))) = _
    simp only [cond_true]
    rw [show 2 * m + 1 + 1 = 2 * m + 2 by omega, hs, he, ho, h2]

theorem cond_bit (n i : Nat) : cond (bitAt n i) 1 0 = (n >>> i) % 2 := by
  rw [bitAt_eq]
  rcases Nat.mod_two_eq_zero_or_one (n >>> i) with h | h <;> rw [h] <;> rfl

theorem run_succ (n L t : Nat) :
    run n L (t + 1) = dstep (bitAt n (L - t - 1)) (run n L t) := rfl

theorem run_spec (n L : Nat) (hL : n >>> L = 0) : ∀ t, t ≤ L →
    run n L t = (Nat.fib (n >>> (L - t)), Nat.fib (n >>> (L - t) + 1)) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [Nat.sub_zero, hL]
    rfl
  | succ t ih =>
    intro ht
    rw [run_succ, ih (by omega)]
    have hi : L - t = (L - t - 1) + 1 := by omega
    rw [hi, dstep_spec, cond_bit, Nat.add_sub_cancel, ← shift_split]
    have : L - (t + 1) = L - t - 1 := by omega
    rw [this]

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  have hL : n >>> (Nat.log2 n + 1) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt Nat.lt_log2_self
  show (run n (Nat.log2 n + 1) (Nat.log2 n + 1)).1 = Nat.fib n
  rw [run_spec n _ hL _ (Nat.le_refl _), Nat.sub_self, Nat.shiftRight_zero]

end Submission
