import Spec

/-!
Fibonacci numbers with very few kernel reduction steps.

1. **Top bits in O(1) steps (generating function).**  For `B = 2^w`, `D = B^2 - B - 1`:
   `B^(m+2) = S * D + (F(m+2) * B + F(m+1))` for an integer `S`, so when `F(m+2) + 2 ≤ B`,
   `B^(m+2) mod D = F(m+2) * B + F(m+1)`.  With `m = n >>> s` (the top ≈ 8 bits of `n`) and
   `w = m + 2` this gives `F(m+1)`, `F(m+2)` with one big `Nat.mod` and a few shifts.
2. **Remaining `s` bits by Lucas doubling.**  State `(F m, L m, 4 (m % 2))` with
   `L m = 2 F(m+1) - F m`:  `F(2m) = F m * L m`, `L(2m) = L(m)^2 + 4 (m % 2) - 2`,
   `F(2m+1) = (F(2m) + L(2m)) / 2`, `L(2m+1) = (5 F(2m) + L(2m)) / 2`.
   One multiplication and one squaring (`Nat.pow _ 2`, which uses GMP squaring) per bit; the
   kernel evaluates lazily, so in the last step only `F` is computed.

Only kernel-accelerated `Nat` primitives with raw literals, a raw `Nat.rec` loop in
continuation-passing style, `Bool.rec` branching, and no `let` in the loop body.
-/

namespace Submission

/-- `sel b x y = if b then x else y`, with the raw recursor. -/
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

/-- One Lucas doubling step, given `F2 = F(2m)`, `L2 = L(2m)` and the next bit. -/
def lstep (k : Nat → Nat → Nat → Nat) (F2 L2 : Nat) (b : Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (k F2 L2 (nat_lit 0))
    (k (Nat.shiftRight (Nat.add F2 L2) (nat_lit 1))
      (Nat.shiftRight (Nat.add (Nat.mul F2 (nat_lit 5)) L2) (nat_lit 1)) (nat_lit 4)) b

/-- `go n t f l q`: consume bits `t-1, …, 0` of `n` starting from `(F m, L m, 4 (m % 2))`;
returns `F (m * 2^t + n % 2^t)`. -/
def go (n : Nat) (t : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun f _ _ => f)
    (fun t k f l q => lstep k (Nat.mul f l)
      (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
      (Nat.beq (Nat.land (Nat.shiftRight n t) (nat_lit 1)) (nat_lit 1))) t

/-- From `a = F(m+1)`, `b = F(m+2)`: start the doubling with `(F m, L m, 4 (m % 2))`. -/
def fromPair (n s m a b : Nat) : Nat :=
  go n s (Nat.sub b a) (Nat.sub (Nat.mul a (nat_lit 3)) b)
    (Nat.shiftLeft (Nat.land m (nat_lit 1)) (nat_lit 2))

/-- Unpack `r = F(m+2) * 2^w + F(m+1)`. -/
def fromRem (n s m w r : Nat) : Nat :=
  fromPair n s m (Nat.land r (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))
    (Nat.shiftRight r w)

/-- `r = 2^(w*w) mod (2^(2w) - 2^w - 1)` with `w = m + 2`. -/
def fromW (n s m w : Nat) : Nat :=
  fromRem n s m w
    (Nat.mod (Nat.shiftLeft (nat_lit 1) (Nat.mul w w))
      (Nat.sub (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add w w)) (Nat.shiftLeft (nat_lit 1) w))
        (nat_lit 1)))

def fromM (n s m : Nat) : Nat := fromW n s m (Nat.add m (nat_lit 2))

def fromS (n s : Nat) : Nat := fromM n s (Nat.shiftRight n s)

def impl (n : Nat) : Nat := fromS n (Nat.sub (bound n) (nat_lit 8))

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

/-- Lucas numbers, written through Fibonacci numbers. -/
def luc (m : Nat) : Nat := 2 * Nat.fib (m + 1) - Nat.fib m

theorem luc_cast (m : Nat) : (luc m : ℤ) = 2 * (Nat.fib (m + 1) : ℤ) - Nat.fib m := by
  have h : Nat.fib m ≤ 2 * Nat.fib (m + 1) := by
    have := Nat.fib_le_fib_succ (n := m); omega
  unfold luc
  rw [Nat.cast_sub h]
  push_cast
  ring

theorem cassini (m : Nat) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2 = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : (Nat.fib (m + 1 + 1) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [h, pow_succ (-1 : ℤ) m, ← ih]
    ring

theorem fib_two_mul_luc (m : Nat) : Nat.fib (2 * m) = Nat.fib m * luc m := Nat.fib_two_mul m

theorem luc_two_mul (m : Nat) : luc (2 * m) + 2 = luc m ^ 2 + 4 * (m % 2) := by
  have hc := cassini m
  have h1 : (Nat.fib (2 * m + 1) : ℤ) = (Nat.fib (m + 1) : ℤ) ^ 2 + (Nat.fib m : ℤ) ^ 2 := by
    rw [Nat.fib_two_mul_add_one]; push_cast; ring
  have h2 : (Nat.fib (2 * m) : ℤ) = Nat.fib m * (2 * (Nat.fib (m + 1) : ℤ) - Nat.fib m) := by
    rw [fib_two_mul_luc, Nat.cast_mul, luc_cast]
  have hsq : (2 * (Nat.fib (m + 1) : ℤ) - Nat.fib m) ^ 2 =
      4 * (Nat.fib (m + 1) : ℤ) ^ 2 - 4 * Nat.fib (m + 1) * Nat.fib m + (Nat.fib m : ℤ) ^ 2 := by
    ring
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have hp : ((-1 : ℤ)) ^ m = 1 := (Nat.even_iff.mpr hm).neg_one_pow
    have e : (Nat.fib (m + 1) : ℤ) ^ 2 =
        Nat.fib (m + 1) * Nat.fib m + (Nat.fib m : ℤ) ^ 2 + 1 := by
      rw [show (Nat.fib (m + 1) : ℤ) ^ 2 = ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m
        - (Nat.fib m : ℤ) ^ 2) + Nat.fib (m + 1) * Nat.fib m + (Nat.fib m : ℤ) ^ 2 by ring, hc, hp]
      ring
    rw [hm]
    zify
    rw [luc_cast, luc_cast, h1, h2, hsq, e]
    ring
  · have hp : ((-1 : ℤ)) ^ m = -1 := (Nat.odd_iff.mpr hm).neg_one_pow
    have e : (Nat.fib (m + 1) : ℤ) ^ 2 =
        Nat.fib (m + 1) * Nat.fib m + (Nat.fib m : ℤ) ^ 2 - 1 := by
      rw [show (Nat.fib (m + 1) : ℤ) ^ 2 = ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m
        - (Nat.fib m : ℤ) ^ 2) + Nat.fib (m + 1) * Nat.fib m + (Nat.fib m : ℤ) ^ 2 by ring, hc, hp]
      ring
    rw [hm]
    zify
    rw [luc_cast, luc_cast, h1, h2, hsq, e]
    ring

theorem fib_succ_luc (k : Nat) : Nat.fib (k + 1) = (Nat.fib k + luc k) / 2 := by
  have := Nat.fib_le_fib_succ (n := k)
  unfold luc
  omega

theorem luc_succ (k : Nat) : luc (k + 1) = (Nat.fib k * 5 + luc k) / 2 := by
  have h1 := Nat.fib_le_fib_succ (n := k)
  have h2 := Nat.fib_le_fib_succ (n := k + 1)
  have h3 : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
  unfold luc
  omega

theorem go_succ (n t f l q : Nat) :
    go n (t + 1) f l q =
      (if (n >>> t) % 2 = 1 then
        go n t ((f * l + (l ^ 2 + q - 2)) / 2) ((f * l * 5 + (l ^ 2 + q - 2)) / 2) 4
      else go n t (f * l) (l ^ 2 + q - 2) 0) := by
  show Bool.rec (motive := fun _ => Nat) (go n t (Nat.mul f l)
      (Nat.sub (Nat.add (Nat.pow l 2) q) 2) 0)
    (go n t (Nat.shiftRight (Nat.add (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l 2) q) 2)) 1)
      (Nat.shiftRight (Nat.add (Nat.mul (Nat.mul f l) 5) (Nat.sub (Nat.add (Nat.pow l 2) q) 2)) 1) 4)
    (Nat.beq (Nat.land (Nat.shiftRight n t) 1) 1) = _
  have hland : Nat.land (Nat.shiftRight n t) 1 = (n >>> t) % 2 := Nat.and_one_is_mod _
  rw [hland]
  have hs (x : Nat) : Nat.shiftRight x 1 = x / 2 := by
    show x >>> 1 = x / 2
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  rcases Nat.mod_two_eq_zero_or_one (n >>> t) with h | h
  · rw [h]; rfl
  · rw [h]; simp only [hs]; rfl

theorem go_spec (n : Nat) : ∀ t m, go n t (Nat.fib m) (luc m) (4 * (m % 2)) =
    Nat.fib (m * 2 ^ t + n % 2 ^ t) := by
  intro t
  induction t with
  | zero => intro m; simp [go, Nat.mod_one]
  | succ t ih =>
    intro m
    rw [go_succ, ← fib_two_mul_luc]
    have hL : luc m ^ 2 + 4 * (m % 2) - 2 = luc (2 * m) := by
      have := luc_two_mul m; omega
    rw [hL]
    have hmod : n % 2 ^ (t + 1) = n % 2 ^ t + 2 ^ t * ((n >>> t) % 2) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.mod_pow_succ]
    split
    · next h1 =>
      rw [← fib_succ_luc, ← luc_succ]
      have h4 : (4 : Nat) = 4 * ((2 * m + 1) % 2) := by omega
      rw [h4, ih (2 * m + 1), hmod, h1, Nat.pow_succ]
      congr 1; ring
    · next h0 =>
      have h0' : (n >>> t) % 2 = 0 := by omega
      have h4 : (0 : Nat) = 4 * ((2 * m) % 2) := by omega
      rw [h4, ih (2 * m), hmod, h0', Nat.pow_succ]
      congr 1; ring

/-! ### The generating-function start -/

theorem gf_aux (B D : Nat) (hD : D + B + 1 = B * B) :
    ∀ k, ∃ S, B ^ (k + 2) = S * D + (Nat.fib (k + 2) * B + Nat.fib (k + 1)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨1, ?_⟩
    simp only [Nat.zero_add, Nat.fib_two, Nat.fib_one, pow_two]
    omega
  | succ k ih =>
    obtain ⟨S, hS⟩ := ih
    refine ⟨B * S + Nat.fib (k + 2), ?_⟩
    have h3 : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have key : Nat.fib (k + 2) * (B * B) = Nat.fib (k + 2) * (D + B + 1) := by rw [hD]
    rw [show k + 1 + 2 = (k + 2) + 1 from rfl, pow_succ, hS, h3, show k + 1 + 1 = k + 2 from rfl]
    calc (S * D + (Nat.fib (k + 2) * B + Nat.fib (k + 1))) * B
        = S * D * B + Nat.fib (k + 2) * (B * B) + Nat.fib (k + 1) * B := by ring
      _ = S * D * B + Nat.fib (k + 2) * (D + B + 1) + Nat.fib (k + 1) * B := by rw [key]
      _ = (B * S + Nat.fib (k + 2)) * D + ((Nat.fib (k + 1) + Nat.fib (k + 2)) * B + Nat.fib (k + 2)) := by ring

theorem fib_succ_le_two_pow : ∀ k, Nat.fib (k + 1) ≤ 2 ^ k ∧ Nat.fib (k + 2) ≤ 2 ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp [Nat.fib_two]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h3 : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have e1 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    have e2 : 2 ^ (k + 1 + 1) = 2 ^ k * 2 * 2 := by rw [pow_succ, e1]
    rw [h3, e2]
    have ha := ih.1
    have hb := ih.2
    rw [e1] at hb
    omega

theorem gf_mod (m : Nat) :
    2 ^ ((m + 2) * (m + 2)) % (2 ^ ((m + 2) + (m + 2)) - 2 ^ (m + 2) - 1) =
      Nat.fib (m + 2) * 2 ^ (m + 2) + Nat.fib (m + 1) := by
  have hb : Nat.fib (m + 2) ≤ 2 ^ (m + 1) := (fib_succ_le_two_pow m).2
  have ha : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_le_fib_succ
  have hB2 : 2 ≤ 2 ^ (m + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hBB : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := pow_succ 2 (m + 1)
  have hsq : 2 ^ ((m + 2) + (m + 2)) = 2 ^ (m + 2) * 2 ^ (m + 2) := by rw [pow_add]
  have hpow : 2 ^ ((m + 2) * (m + 2)) = (2 ^ (m + 2)) ^ (m + 2) := by rw [pow_mul]
  rw [hsq, hpow]
  generalize hBdef : 2 ^ (m + 2) = B at *
  have hB4 : 4 ≤ B := by omega
  have hBsq : B * 2 ≤ B * B := Nat.mul_le_mul_left B (by omega)
  have hD : (B * B - B - 1) + B + 1 = B * B := by omega
  obtain ⟨S, hS⟩ := gf_aux B (B * B - B - 1) hD m
  rw [hS, Nat.mul_comm S, Nat.mul_add_mod]
  apply Nat.mod_eq_of_lt
  have h1 : (Nat.fib (m + 2) + 1) * B ≤ (B - 1) * B := Nat.mul_le_mul_right B (by omega)
  have h2 : (B - 1) * B = B * B - B := by rw [Nat.sub_mul, Nat.one_mul]
  have h1' : (Nat.fib (m + 2) + 1) * B = Nat.fib (m + 2) * B + B := by ring
  omega

theorem fromPair_eq (n s m a b : Nat) :
    fromPair n s m a b = go n s (b - a) (a * 3 - b) ((m &&& 1) <<< 2) := rfl

theorem fromRem_eq (n s m w r : Nat) :
    fromRem n s m w r = fromPair n s m (r &&& ((1 <<< w) - 1)) (r >>> w) := rfl

theorem fromW_eq (n s m w : Nat) :
    fromW n s m w = fromRem n s m w ((1 <<< (w * w)) % ((1 <<< (w + w)) - (1 <<< w) - 1)) := rfl

theorem fromM_eq' (n s m : Nat) : fromM n s m = fromW n s m (m + 2) := rfl

theorem fromM_eq (n s m : Nat) :
    fromM n s m = go n s (Nat.fib m) (luc m) (4 * (m % 2)) := by
  rw [fromM_eq', fromW_eq, fromRem_eq, fromPair_eq]
  have hr : (1 <<< ((m + 2) * (m + 2))) % ((1 <<< ((m + 2) + (m + 2))) - (1 <<< (m + 2)) - 1) =
      Nat.fib (m + 2) * 2 ^ (m + 2) + Nat.fib (m + 1) := by
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    exact gf_mod m
  rw [hr]
  have hlt : Nat.fib (m + 1) < 2 ^ (m + 2) := by
    have h0 := (fib_succ_le_two_pow m).1
    have : 2 ^ m < 2 ^ (m + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hA : (Nat.fib (m + 2) * 2 ^ (m + 2) + Nat.fib (m + 1)) &&& ((1 <<< (m + 2)) - 1) =
      Nat.fib (m + 1) := by
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mul_comm (Nat.fib (m + 2)), Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have hB : (Nat.fib (m + 2) * 2 ^ (m + 2) + Nat.fib (m + 1)) >>> (m + 2) = Nat.fib (m + 2) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm (Nat.fib (m + 2)),
      Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.add_zero]
  have hQ : (m &&& 1) <<< 2 = 4 * (m % 2) := by
    rw [Nat.and_one_is_mod, Nat.shiftLeft_eq]; ring
  rw [hA, hB, hQ]
  have h3 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have h4 := Nat.fib_le_fib_succ (n := m)
  have hF : Nat.fib (m + 2) - Nat.fib (m + 1) = Nat.fib m := by omega
  have hLu : Nat.fib (m + 1) * 3 - Nat.fib (m + 2) = luc m := by
    unfold luc
    omega
  rw [hF, hLu]

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  show fromM n (bound n - 8) (n >>> (bound n - 8)) = _
  rw [fromM_eq, go_spec, Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.div_add_mod]

end Submission
