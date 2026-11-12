import Spec

/-!
Fibonacci numbers with very few kernel reduction steps (v4).

1. **Top bits in O(1) steps (generating function).**  For `B = 2^w`, `D = B^2 - B - 1`:
   `B^(m+2) = S * D + (F(m+2) * B + F(m+1))`, so `B^(m+2) mod D = F(m+2) * B + F(m+1)` when
   `F(m+2) + 2 ≤ B`.  With `m = n >>> s` (the top ≈ 8 bits of `n`) and `w = m + 2` this gives
   `F(m+1)`, `F(m+2)` with one big `Nat.mod` and a few shifts.
2. **Remaining bits by Lucas doubling.**  State `(F m, L m, 4 (m % 2))`, `L m = 2 F(m+1) - F m`:
   `F(2m) = F m * L m`, `L(2m) = L(m)^2 + 4 (m % 2) - 2`, `F(2m+1) = (F(2m) + L(2m)) / 2`,
   `L(2m+1) = 2 F(2m) + F(2m+1)`.  The last bit uses a single multiplication:
   `F(2m) = F m * L m`, `F(2m+1) = F(m+1) * L m + 2 (m % 2) - 1`.
3. **Cheap control.**  For `n < 2^18` the shift `s = bits(n) - 8` is chosen by a comparison tree and
   the doubling loop is unrolled (separate definitions `go1 … go9`, no recursor step per bit); larger
   `n` use the same algorithm with a general bit-length bound and a `Nat.rec` loop.

Only kernel-accelerated `Nat` primitives with raw literals, `Bool.rec` branching, no `let` in hot code.
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
      (Nat.add (Nat.shiftLeft F2 (nat_lit 1)) (Nat.shiftRight (Nat.add F2 L2) (nat_lit 1)))
      (nat_lit 4)) b

/-- Last step, from `(F m, L m, 4 (m % 2))` and the lowest bit of `n`. -/
def fin (n f l q : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.mul f l)
    (Nat.sub (Nat.add (Nat.mul (Nat.shiftRight (Nat.add f l) (nat_lit 1)) l)
      (Nat.shiftRight q (nat_lit 1))) (nat_lit 1))
    (Nat.beq (Nat.land n (nat_lit 1)) (nat_lit 1))

/-- `go n h t f l q` with `h = n >>> 1`: consume bits `t-1, …, 0` of `h`, then the last bit of `n`. -/
def go (n h : Nat) (t : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun f l q => fin n f l q)
    (fun t k f l q => lstep k (Nat.mul f l)
      (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
      (Nat.beq (Nat.land (Nat.shiftRight h t) (nat_lit 1)) (nat_lit 1))) t

/-! `go n h t` unrolled for `t = 1, …, 9` (definitionally equal, see `goK_eq`). -/
def go1 (n h f l q : Nat) : Nat :=
  lstep (fin n) (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
    (Nat.beq (Nat.land (Nat.shiftRight h (nat_lit 0)) (nat_lit 1)) (nat_lit 1))
def go2 (n h f l q : Nat) : Nat :=
  lstep (go1 n h) (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
    (Nat.beq (Nat.land (Nat.shiftRight h (nat_lit 1)) (nat_lit 1)) (nat_lit 1))
def go3 (n h f l q : Nat) : Nat :=
  lstep (go2 n h) (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
    (Nat.beq (Nat.land (Nat.shiftRight h (nat_lit 2)) (nat_lit 1)) (nat_lit 1))
def go4 (n h f l q : Nat) : Nat :=
  lstep (go3 n h) (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
    (Nat.beq (Nat.land (Nat.shiftRight h (nat_lit 3)) (nat_lit 1)) (nat_lit 1))
def go5 (n h f l q : Nat) : Nat :=
  lstep (go4 n h) (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
    (Nat.beq (Nat.land (Nat.shiftRight h (nat_lit 4)) (nat_lit 1)) (nat_lit 1))
def go6 (n h f l q : Nat) : Nat :=
  lstep (go5 n h) (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
    (Nat.beq (Nat.land (Nat.shiftRight h (nat_lit 5)) (nat_lit 1)) (nat_lit 1))
def go7 (n h f l q : Nat) : Nat :=
  lstep (go6 n h) (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
    (Nat.beq (Nat.land (Nat.shiftRight h (nat_lit 6)) (nat_lit 1)) (nat_lit 1))
def go8 (n h f l q : Nat) : Nat :=
  lstep (go7 n h) (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
    (Nat.beq (Nat.land (Nat.shiftRight h (nat_lit 7)) (nat_lit 1)) (nat_lit 1))
def go9 (n h f l q : Nat) : Nat :=
  lstep (go8 n h) (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l (nat_lit 2)) q) (nat_lit 2))
    (Nat.beq (Nat.land (Nat.shiftRight h (nat_lit 8)) (nat_lit 1)) (nat_lit 1))

/-- From `a = F(m+1)`, `b = F(m+2)`: continue with `(F m, L m, 4 (m % 2))`. -/
def fromPair (G : Nat → Nat → Nat → Nat) (m a b : Nat) : Nat :=
  G (Nat.sub b a) (Nat.sub (Nat.mul a (nat_lit 3)) b)
    (Nat.shiftLeft (Nat.land m (nat_lit 1)) (nat_lit 2))

/-- Unpack `r = F(m+2) * 2^w + F(m+1)`. -/
def fromRem (G : Nat → Nat → Nat → Nat) (m w r : Nat) : Nat :=
  fromPair G m (Nat.land r (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))
    (Nat.shiftRight r w)

/-- `r = 2^(w*w) mod (2^(2w) - 2^w - 1)` with `w = m + 2`. -/
def fromW (G : Nat → Nat → Nat → Nat) (m w : Nat) : Nat :=
  fromRem G m w
    (Nat.mod (Nat.shiftLeft (nat_lit 1) (Nat.mul w w))
      (Nat.sub (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add w w)) (Nat.shiftLeft (nat_lit 1) w))
        (nat_lit 1)))

/-- Start the doubling continuation `G` at `m` (top bits of `n`). -/
def fromM (G : Nat → Nat → Nat → Nat) (m : Nat) : Nat := fromW G m (Nat.add m (nat_lit 2))

/-- `F n`.  Leaves of the tree use `s = bits(n) - 8` doubling steps (`s - 1` in the loop plus the
last bit); any `s ≥ 1` is correct, the choice only affects speed. -/
def impl (n : Nat) : Nat :=
  sel (Nat.ble (nat_lit 262144) n)
    (fromM (go n (Nat.shiftRight n (nat_lit 1)) (Nat.sub (bound n) (nat_lit 9)))
      (Nat.shiftRight n (Nat.add (Nat.sub (bound n) (nat_lit 9)) (nat_lit 1))))
    (sel (Nat.ble (nat_lit 32768) n)
      (sel (Nat.ble (nat_lit 131072) n)
        (fromM (go9 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 10)))
        (sel (Nat.ble (nat_lit 65536) n)
          (fromM (go8 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 9)))
          (fromM (go7 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 8)))))
      (sel (Nat.ble (nat_lit 16384) n)
        (fromM (go6 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 7)))
        (sel (Nat.ble (nat_lit 8192) n)
          (fromM (go5 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 6)))
          (fromM (go4 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 5))))))

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


theorem luc_succ' (k : Nat) : luc (k + 1) = Nat.fib k * 2 + Nat.fib (k + 1) := by
  have h3 : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
  have h1 := Nat.fib_le_fib_succ (n := k)
  unfold luc
  omega

theorem fib_odd_luc (m : Nat) :
    Nat.fib (2 * m + 1) + 1 = Nat.fib (m + 1) * luc m + 2 * (m % 2) := by
  have hc := cassini m
  have h1 : (Nat.fib (2 * m + 1) : ℤ) = (Nat.fib (m + 1) : ℤ) ^ 2 + (Nat.fib m : ℤ) ^ 2 := by
    rw [Nat.fib_two_mul_add_one]; push_cast; ring
  have hm : (Nat.fib (m + 1) : ℤ) * (2 * (Nat.fib (m + 1) : ℤ) - Nat.fib m) =
      2 * (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m := by ring
  rcases Nat.mod_two_eq_zero_or_one m with hm2 | hm2
  · have hp : ((-1 : ℤ)) ^ m = 1 := (Nat.even_iff.mpr hm2).neg_one_pow
    have e : (Nat.fib (m + 1) : ℤ) ^ 2 =
        Nat.fib (m + 1) * Nat.fib m + (Nat.fib m : ℤ) ^ 2 + 1 := by
      rw [show (Nat.fib (m + 1) : ℤ) ^ 2 = ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m
        - (Nat.fib m : ℤ) ^ 2) + Nat.fib (m + 1) * Nat.fib m + (Nat.fib m : ℤ) ^ 2 by ring, hc, hp]
      ring
    rw [hm2]
    zify
    rw [luc_cast, h1, hm, e]
    ring
  · have hp : ((-1 : ℤ)) ^ m = -1 := (Nat.odd_iff.mpr hm2).neg_one_pow
    have e : (Nat.fib (m + 1) : ℤ) ^ 2 =
        Nat.fib (m + 1) * Nat.fib m + (Nat.fib m : ℤ) ^ 2 - 1 := by
      rw [show (Nat.fib (m + 1) : ℤ) ^ 2 = ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m
        - (Nat.fib m : ℤ) ^ 2) + Nat.fib (m + 1) * Nat.fib m + (Nat.fib m : ℤ) ^ 2 by ring, hc, hp]
      ring
    rw [hm2]
    zify
    rw [luc_cast, h1, hm, e]
    ring

theorem shr1 (x : Nat) : Nat.shiftRight x 1 = x / 2 := by
  show x >>> 1 = x / 2
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem shl1 (x : Nat) : Nat.shiftLeft x 1 = x * 2 := by
  show x <<< 1 = x * 2
  rw [Nat.shiftLeft_eq, pow_one]

theorem fin_spec (n m : Nat) :
    fin n (Nat.fib m) (luc m) (4 * (m % 2)) = Nat.fib (2 * m + n % 2) := by
  show Bool.rec (motive := fun _ => Nat) (Nat.mul (Nat.fib m) (luc m))
    (Nat.sub (Nat.add (Nat.mul (Nat.shiftRight (Nat.add (Nat.fib m) (luc m)) 1) (luc m))
      (Nat.shiftRight (4 * (m % 2)) 1)) 1)
    (Nat.beq (Nat.land n 1) 1) = _
  have hland : Nat.land n 1 = n % 2 := Nat.and_one_is_mod _
  rw [hland]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h]
    show Nat.fib m * luc m = _
    rw [Nat.add_zero, fib_two_mul_luc]
  · rw [h]
    show Nat.sub (Nat.add (Nat.mul (Nat.shiftRight (Nat.add (Nat.fib m) (luc m)) 1) (luc m))
      (Nat.shiftRight (4 * (m % 2)) 1)) 1 = _
    rw [shr1, shr1]
    show (Nat.fib m + luc m) / 2 * luc m + 4 * (m % 2) / 2 - 1 = _
    rw [← fib_succ_luc]
    have := fib_odd_luc m
    omega

theorem go_succ (n h t f l q : Nat) :
    go n h (t + 1) f l q =
      (if (h >>> t) % 2 = 1 then
        go n h t ((f * l + (l ^ 2 + q - 2)) / 2) (f * l * 2 + (f * l + (l ^ 2 + q - 2)) / 2) 4
      else go n h t (f * l) (l ^ 2 + q - 2) 0) := by
  show Bool.rec (motive := fun _ => Nat) (go n h t (Nat.mul f l)
      (Nat.sub (Nat.add (Nat.pow l 2) q) 2) 0)
    (go n h t (Nat.shiftRight (Nat.add (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l 2) q) 2)) 1)
      (Nat.add (Nat.shiftLeft (Nat.mul f l) 1)
        (Nat.shiftRight (Nat.add (Nat.mul f l) (Nat.sub (Nat.add (Nat.pow l 2) q) 2)) 1)) 4)
    (Nat.beq (Nat.land (Nat.shiftRight h t) 1) 1) = _
  have hland : Nat.land (Nat.shiftRight h t) 1 = (h >>> t) % 2 := Nat.and_one_is_mod _
  rw [hland]
  rcases Nat.mod_two_eq_zero_or_one (h >>> t) with hb | hb
  · rw [hb]; rfl
  · rw [hb]; simp only [shr1, shl1]; rfl

theorem go_spec (n h : Nat) : ∀ t m, go n h t (Nat.fib m) (luc m) (4 * (m % 2)) =
    Nat.fib (2 * (m * 2 ^ t + h % 2 ^ t) + n % 2) := by
  intro t
  induction t with
  | zero =>
    intro m
    show fin n (Nat.fib m) (luc m) (4 * (m % 2)) = _
    rw [fin_spec, Nat.pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero]
  | succ t ih =>
    intro m
    rw [go_succ, ← fib_two_mul_luc]
    have hL : luc m ^ 2 + 4 * (m % 2) - 2 = luc (2 * m) := by
      have := luc_two_mul m; omega
    rw [hL]
    have hmod : h % 2 ^ (t + 1) = h % 2 ^ t + 2 ^ t * ((h >>> t) % 2) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.mod_pow_succ]
    split
    · next h1 =>
      rw [← fib_succ_luc, ← luc_succ']
      have h4 : (4 : Nat) = 4 * ((2 * m + 1) % 2) := by omega
      rw [h4, ih (2 * m + 1), hmod, h1, Nat.pow_succ]
      congr 1; ring
    · next h0 =>
      have h0' : (h >>> t) % 2 = 0 := by omega
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


theorem fromPair_eq (G : Nat → Nat → Nat → Nat) (m a b : Nat) :
    fromPair G m a b = G (b - a) (a * 3 - b) ((m &&& 1) <<< 2) := rfl

theorem fromRem_eq (G : Nat → Nat → Nat → Nat) (m w r : Nat) :
    fromRem G m w r = fromPair G m (r &&& ((1 <<< w) - 1)) (r >>> w) := rfl

theorem fromW_eq (G : Nat → Nat → Nat → Nat) (m w : Nat) :
    fromW G m w = fromRem G m w ((1 <<< (w * w)) % ((1 <<< (w + w)) - (1 <<< w) - 1)) := rfl

theorem fromM_eq' (G : Nat → Nat → Nat → Nat) (m : Nat) : fromM G m = fromW G m (m + 2) := rfl

theorem fromM_eq (G : Nat → Nat → Nat → Nat) (m : Nat) :
    fromM G m = G (Nat.fib m) (luc m) (4 * (m % 2)) := by
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

/-! ### Assembling -/

/-- With `t + 1` doubling steps the result is `F n`, for every `t`. -/
theorem run_spec (n t : Nat) :
    fromM (go n (n >>> 1) t) (n >>> (t + 1)) = Nat.fib n := by
  rw [fromM_eq, go_spec]
  congr 1
  have hs : n >>> (t + 1) = (n >>> 1) >>> t := by
    rw [Nat.add_comm, Nat.shiftRight_add]
  rw [hs, Nat.shiftRight_eq_div_pow (n >>> 1) t, Nat.div_add_mod',
    Nat.shiftRight_eq_div_pow n 1, pow_one]
  exact Nat.div_add_mod n 2

theorem sel_self (b : Bool) (x : Nat) : sel b x x = x := by cases b <;> rfl

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  have e4 : fromM (go4 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 5)) =
      Nat.fib n := run_spec n 4
  have e5 : fromM (go5 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 6)) =
      Nat.fib n := run_spec n 5
  have e6 : fromM (go6 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 7)) =
      Nat.fib n := run_spec n 6
  have e7 : fromM (go7 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 8)) =
      Nat.fib n := run_spec n 7
  have e8 : fromM (go8 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 9)) =
      Nat.fib n := run_spec n 8
  have e9 : fromM (go9 n (Nat.shiftRight n (nat_lit 1))) (Nat.shiftRight n (nat_lit 10)) =
      Nat.fib n := run_spec n 9
  have eG : fromM (go n (Nat.shiftRight n (nat_lit 1)) (Nat.sub (bound n) (nat_lit 9)))
      (Nat.shiftRight n (Nat.add (Nat.sub (bound n) (nat_lit 9)) (nat_lit 1))) = Nat.fib n :=
    run_spec n _
  unfold impl
  rw [e4, e5, e6, e7, e8, e9, eG]
  simp only [sel_self]

end Submission
