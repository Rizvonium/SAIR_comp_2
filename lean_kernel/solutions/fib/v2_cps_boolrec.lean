import Spec

/-!
Fast doubling over the binary digits of `n`, most significant first, written for
cheap kernel reduction:

* a single raw `Nat.rec` loop whose counter `t` is the bit index, threading the
  pair `(F m, F (m+1))` as two plain arguments (no `Prod` allocation);
* branching with `Bool.rec` instead of `cond`/`if`;
* only kernel-accelerated primitives (`Nat.add/sub/mul/land/shiftRight/beq/ble`)
  with raw literals;
* no `Nat.log2` (not accelerated by the kernel): a cheap bit-length guess is
  validated at run time (`n >>> c = 0`), falling back to `n` itself, so
  correctness never depends on the guess.

Doubling identities: F(2m) = F(m)·(2F(m+1) − F(m)), F(2m+1) = F(m)² + F(m+1)².
-/

namespace Submission

/-- `go n t a b`: consume bits `t-1, …, 0` of `n`, starting from `(a, b) = (F m, F (m+1))`;
returns `F (m * 2^t + n % 2^t)`. -/
def go (n : Nat) (t : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun a _ => a)
    (fun t k a b =>
      let c := Nat.mul a (Nat.sub (Nat.add b b) a)
      let d := Nat.add (Nat.mul a a) (Nat.mul b b)
      Bool.rec (motive := fun _ => Nat) (k c d) (k d (Nat.add c d))
        (Nat.beq (Nat.land (Nat.shiftRight n t) (nat_lit 1)) (nat_lit 1))) t

/-- Selection `if b then x else y` written with the raw recursor. -/
def sel (b : Bool) (x y : Nat) : Nat := Bool.rec (motive := fun _ => Nat) y x b

/-- Bit-length guess by binary search (exact for `n < 2^32`). Only used as a hint. -/
def guess (n : Nat) : Nat :=
  let t1 := sel (Nat.ble (nat_lit 65536) n) (nat_lit 16) (nat_lit 0)
  let n1 := Nat.shiftRight n t1
  let t2 := sel (Nat.ble (nat_lit 256) n1) (nat_lit 8) (nat_lit 0)
  let n2 := Nat.shiftRight n1 t2
  let t3 := sel (Nat.ble (nat_lit 16) n2) (nat_lit 4) (nat_lit 0)
  let n3 := Nat.shiftRight n2 t3
  let t4 := sel (Nat.ble (nat_lit 4) n3) (nat_lit 2) (nat_lit 0)
  let n4 := Nat.shiftRight n3 t4
  let t5 := sel (Nat.ble (nat_lit 2) n4) (nat_lit 1) (nat_lit 0)
  Nat.add (Nat.add (Nat.add t1 t2) (Nat.add t3 t4)) (Nat.add t5 (Nat.shiftRight n4 t5))

/-- A number of bits `L` with `n >>> L = 0`: the guess if it is valid, else `n`. -/
def bound (n : Nat) : Nat :=
  let c := guess n
  sel (Nat.beq (Nat.shiftRight n c) (nat_lit 0)) c n

def impl (n : Nat) : Nat := go n (bound n) (nat_lit 0) (nat_lit 1)

/-! ## Correctness -/

theorem sel_eq (b : Bool) (x y : Nat) : sel b x y = if b = true then x else y := by
  cases b <;> rfl

theorem bound_spec (n : Nat) : n >>> bound n = 0 := by
  unfold bound
  simp only [sel_eq]
  split
  · next h => exact Nat.eq_of_beq_eq_true h
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (Nat.lt_two_pow_self)

theorem go_succ (n t : Nat) (a b : Nat) :
    go n (t + 1) a b =
      (let c := a * (2 * b - a)
       let d := a * a + b * b
       if (n >>> t) % 2 = 1 then go n t d (c + d) else go n t c d) := by
  show Bool.rec (motive := fun _ => Nat) (go n t (Nat.mul a (Nat.sub (Nat.add b b) a))
      (Nat.add (Nat.mul a a) (Nat.mul b b)))
    (go n t (Nat.add (Nat.mul a a) (Nat.mul b b))
      (Nat.add (Nat.mul a (Nat.sub (Nat.add b b) a)) (Nat.add (Nat.mul a a) (Nat.mul b b))))
    (Nat.beq (Nat.land (Nat.shiftRight n t) 1) 1) = _
  have hland : Nat.land (Nat.shiftRight n t) 1 = (n >>> t) % 2 := Nat.and_one_is_mod _
  rw [hland]
  have h2 : 2 * b = b + b := by omega
  rcases Nat.mod_two_eq_zero_or_one (n >>> t) with h | h
  · rw [h]; simp only [h2]; rfl
  · rw [h]; simp only [h2]; rfl

theorem go_spec (n : Nat) : ∀ t m, go n t (Nat.fib m) (Nat.fib (m + 1)) =
    Nat.fib (m * 2 ^ t + n % 2 ^ t) := by
  intro t
  induction t with
  | zero => intro m; simp [go, Nat.mod_one]
  | succ t ih =>
    intro m
    rw [go_succ]
    have he : Nat.fib (2 * m) = Nat.fib m * (2 * Nat.fib (m + 1) - Nat.fib m) := Nat.fib_two_mul m
    have ho : Nat.fib (2 * m + 1) = Nat.fib m * Nat.fib m + Nat.fib (m + 1) * Nat.fib (m + 1) := by
      rw [Nat.fib_two_mul_add_one, pow_two, pow_two, Nat.add_comm]
    have hs : Nat.fib (2 * m + 1 + 1) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
    have hmod : n % 2 ^ (t + 1) = n % 2 ^ t + 2 ^ t * ((n >>> t) % 2) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.mod_pow_succ]
    simp only
    split
    · next h1 =>
      rw [← he, ← ho, ← hs, ih (2 * m + 1), hmod, h1, Nat.pow_succ]
      congr 1; ring
    · next h0 =>
      have h0' : (n >>> t) % 2 = 0 := by omega
      rw [← he, ← ho, ih (2 * m), hmod, h0', Nat.pow_succ]
      congr 1; ring

theorem impl_eq (n : Nat) : impl n = go n (bound n) (Nat.fib 0) (Nat.fib (0 + 1)) := by
  rw [Nat.fib_zero, Nat.zero_add, Nat.fib_one]; rfl

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  rw [impl_eq, go_spec, Nat.zero_mul, Nat.zero_add]
  have hlt : n < 2 ^ bound n := by
    have h := bound_spec n
    rw [Nat.shiftRight_eq_div_pow] at h
    have := Nat.div_add_mod n (2 ^ bound n)
    rw [h, Nat.mul_zero, Nat.zero_add] at this
    calc n = n % 2 ^ bound n := this.symm
      _ < 2 ^ bound n := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [Nat.mod_eq_of_lt hlt]

end Submission
