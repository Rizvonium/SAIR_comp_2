import Spec

/-!
# Permanent of the seeded 3-per-row matrix by a bit-parallel subset DP

For dimension `d ≥ 3` the permanent is computed by a backward dynamic programme over
column subsets, all `2^d` subsets at once, packed into one big natural number
(lane `L` occupies bits `[W·L, W·L + W)`):

* start: only lane `2^d - 1` (all columns used) holds `1`;
* for rows `d-1, …, 0`: `X ← Σ_{j ∈ row} X >>> (W·2^j)`, i.e. lane `L` receives lanes `L + 2^j`;
* the answer is lane `0`.

Lane `L` after the rows `r … d-1` counts the column choices `j_r, …, j_{d-1}` of those rows with
`L + Σ 2^{j_i} = 2^d - 1`.  On lanes with popcount `r` (the used-column masks reachable by the
spec's depth-first search) a choice `j` already in `L` produces a carry and lands on a lane
whose count is provably zero, so these lanes equal the spec's `permanentRows` value.
No masks are needed.  Lanes are `W` bits wide with `3^d < 2^W`, so they never overflow.

Everything on the computational path uses kernel-accelerated `Nat` primitives with raw
literals; loops are raw `Nat.rec`.
-/

namespace Submission

/-! ## Computation -/

/-- First round of `permanentMix32`. -/
def mixA (x : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x (nat_lit 16))) (nat_lit 0x7feb352d)) (nat_lit 0xffffffff)

/-- Second round of `permanentMix32`. -/
def mixB (x : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x (nat_lit 15))) (nat_lit 0x846ca68b)) (nat_lit 0xffffffff)

/-- Final round of `permanentMix32`. -/
def mixC (x : Nat) : Nat :=
  Nat.land (Nat.xor x (Nat.shiftRight x (nat_lit 16))) (nat_lit 0xffffffff)

/-- `permanentMix32` with raw primitives. -/
def mix (x : Nat) : Nat := mixC (mixB (mixA x))

/-- `permanentSkipOne e k = k + [e ≤ k]`, branch-free. -/
def skip (e k : Nat) : Nat := Nat.add k (Nat.sub (nat_lit 1) (Nat.sub e k))

/-- `permanentSkipTwo a b k`: skip `min a b`, then `max a b`. -/
def skip2 (a b k : Nat) : Nat :=
  skip (Nat.add b (Nat.sub a b)) (skip (Nat.sub a (Nat.sub a b)) k)

/-- The seeded hash input of row `i`, before the salt. -/
def rowHash (s i : Nat) : Nat := Nat.xor s (Nat.mul i (nat_lit 0x9e3779b9))

/-- First off-diagonal column of row `i`. -/
def col1 (d s i : Nat) : Nat :=
  skip i (Nat.mod (mix (Nat.xor (rowHash s i) (nat_lit 0x85ebca6b))) (Nat.sub d (nat_lit 1)))

/-- Second off-diagonal column of row `i`, given the first one `c`. -/
def col2 (d s i c : Nat) : Nat :=
  skip2 i c (Nat.mod (mix (Nat.xor (rowHash s i) (nat_lit 0xc2b2ae35))) (Nat.sub d (nat_lit 2)))

/-- One backward row step on the packed lanes: `Σ_{j ∈ {i,a,b}} X >>> (W·2^j)`. -/
def step (W i a b X : Nat) : Nat :=
  Nat.add (Nat.add (Nat.shiftRight X (Nat.shiftLeft W i)) (Nat.shiftRight X (Nat.shiftLeft W a)))
    (Nat.shiftRight X (Nat.shiftLeft W b))

/-- Row step with the second column computed from the first. -/
def rowStepAux (d s W i c X : Nat) : Nat := step W i c (col2 d s i c) X

/-- Row step for row `i`. -/
def rowStep (d s W i X : Nat) : Nat := rowStepAux d s W i (col1 d s i) X

/-- `loopG f t X` applies `f (t-1)`, …, `f 0` to `X`, in that order. -/
def loopG (f : Nat → Nat → Nat) (t : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun X => X) (fun t k X => k (f t X)) t

/-- Lane width: `8·(d/5) + 2·(d%5)`, which satisfies `3^d < 2^width` for `d ≥ 1`. -/
def width (d : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 8) (Nat.div d (nat_lit 5))) (Nat.mul (nat_lit 2) (Nat.mod d (nat_lit 5)))

/-- The DP for `d ≥ 3` with lane width `W`. -/
def fast (d s W : Nat) : Nat :=
  Nat.land
    (loopG (rowStep d s W) d (Nat.shiftLeft (nat_lit 1) (Nat.mul W (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)))))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))

/-- Dimensions below 3 have the all-ones matrix: permanent `d! = max d 1`. -/
def implAux (d s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (fast d s (width d))
    (fun _ _ => Nat.add d (Nat.sub (nat_lit 1) d)) (Nat.sub (nat_lit 3) d)

def impl (n : Nat) : Nat :=
  implAux (Nat.shiftRight n (nat_lit 32)) (Nat.land n (nat_lit 0xffffffff))

/-! ## Finite sums -/

/-- `sumTo n f = Σ_{j<n} f j`. -/
def sumTo (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => sumTo n f + f n

theorem sumTo_congr (n : Nat) (f g : Nat → Nat) (h : ∀ j, j < n → f j = g j) :
    sumTo n f = sumTo n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem sumTo_add (n : Nat) (f g : Nat → Nat) :
    sumTo n (fun j => f j + g j) = sumTo n f + sumTo n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo]; rw [ih]; omega

theorem sumTo_single (n x v : Nat) (hx : x < n) :
    sumTo n (fun j => if j = x then v else 0) = v := by
  have hz : ∀ m, m ≤ x → sumTo m (fun j => if j = x then v else 0) = 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ihm => simp only [sumTo]; rw [ihm (by omega), if_neg (by omega)]
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumTo]
    by_cases h : x = n
    · subst h; rw [hz x (Nat.le_refl x), if_pos rfl, Nat.zero_add]
    · rw [ih (by omega), if_neg (fun e => h e.symm), Nat.add_zero]

theorem sumTo_three (n : Nat) (h : Nat → Nat) (x y z : Nat) (hx : x < n) (hy : y < n) (hz : z < n)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h0 : ∀ j, j < n → j ≠ x → j ≠ y → j ≠ z → h j = 0) :
    sumTo n h = h x + h y + h z := by
  have e : sumTo n h = sumTo n (fun j => ((if j = x then h x else 0) + (if j = y then h y else 0)) +
      (if j = z then h z else 0)) := by
    apply sumTo_congr
    intro j hj
    by_cases jx : j = x
    · subst jx; simp [hxy, hxz]
    · by_cases jy : j = y
      · subst jy; simp [jx, hyz]
      · by_cases jz : j = z
        · subst jz; simp [jx, jy]
        · simp [jx, jy, jz, h0 j hj jx jy jz]
  rw [e, sumTo_add, sumTo_add, sumTo_single n x _ hx, sumTo_single n y _ hy, sumTo_single n z _ hz]

theorem foldl_range_eq_sumTo (C : Nat → Bool) (G : Nat → Nat) (n a : Nat) :
    (List.range n).foldl (fun t j => if C j = true then t else t + G j) a =
      a + sumTo n (fun j => if C j = true then 0 else G j) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [show n + 1 = Nat.succ n from rfl, List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, sumTo]
    by_cases hc : C n = true <;> simp [hc] <;> omega

/-! ## Popcount -/

/-- Number of one bits. -/
def pc : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + pc ((n + 1) / 2)
decreasing_by omega

theorem pc_eq (n : Nat) : pc n = n % 2 + pc (n / 2) := by
  cases n with
  | zero => simp [pc]
  | succ n => rw [pc]

theorem pc_succ_le (L : Nat) : pc (L + 1) ≤ pc L + 1 := by
  induction L using Nat.strongRecOn with
  | ind L ih =>
    rw [pc_eq (L + 1), pc_eq L]
    rcases Nat.mod_two_eq_zero_or_one L with h | h
    · have h1 : (L + 1) % 2 = 1 := by omega
      have h2 : (L + 1) / 2 = L / 2 := by omega
      rw [h1, h2, h]; omega
    · have h1 : (L + 1) % 2 = 0 := by omega
      have h2 : (L + 1) / 2 = L / 2 + 1 := by omega
      rw [h1, h2, h]
      have := ih (L / 2) (by omega)
      omega

theorem testBit_succ' (L j : Nat) : L.testBit (j + 1) = (L / 2).testBit j := by
  rw [Nat.testBit_succ]

theorem testBit_zero' (L : Nat) : L.testBit 0 = decide (L % 2 = 1) := by
  rw [Nat.testBit_zero]

theorem pc_add_of_not (j : Nat) : ∀ L, L.testBit j = false → pc (L + 2 ^ j) = pc L + 1 := by
  induction j with
  | zero =>
    intro L h
    rw [testBit_zero'] at h
    simp at h
    rw [pc_eq (L + 2 ^ 0), pc_eq L]
    have h1 : (L + 2 ^ 0) % 2 = 1 := by simp; omega
    have h2 : (L + 2 ^ 0) / 2 = L / 2 := by simp; omega
    rw [h1, h2]; omega
  | succ j ih =>
    intro L h
    rw [testBit_succ'] at h
    rw [pc_eq (L + 2 ^ (j + 1)), pc_eq L]
    have h1 : (L + 2 ^ (j + 1)) % 2 = L % 2 := by rw [Nat.pow_succ]; omega
    have h2 : (L + 2 ^ (j + 1)) / 2 = L / 2 + 2 ^ j := by rw [Nat.pow_succ]; omega
    rw [h1, h2, ih (L / 2) h]; omega

theorem pc_add_of_set (j : Nat) : ∀ L, L.testBit j = true → pc (L + 2 ^ j) ≤ pc L := by
  induction j with
  | zero =>
    intro L h
    rw [testBit_zero'] at h
    simp at h
    rw [pc_eq (L + 2 ^ 0), pc_eq L]
    have h1 : (L + 2 ^ 0) % 2 = 0 := by simp; omega
    have h2 : (L + 2 ^ 0) / 2 = L / 2 + 1 := by simp; omega
    rw [h1, h2, h]
    have := pc_succ_le (L / 2)
    omega
  | succ j ih =>
    intro L h
    rw [testBit_succ'] at h
    rw [pc_eq (L + 2 ^ (j + 1)), pc_eq L]
    have h1 : (L + 2 ^ (j + 1)) % 2 = L % 2 := by rw [Nat.pow_succ]; omega
    have h2 : (L + 2 ^ (j + 1)) / 2 = L / 2 + 2 ^ j := by rw [Nat.pow_succ]; omega
    rw [h1, h2]
    have := ih (L / 2) h
    omega

theorem pc_add_le (j L : Nat) : pc (L + 2 ^ j) ≤ pc L + 1 := by
  cases h : L.testBit j
  · rw [pc_add_of_not j L h]; omega
  · have := pc_add_of_set j L h; omega

theorem pc_le (n : Nat) : ∀ L, L < 2 ^ n → pc L ≤ n := by
  induction n with
  | zero => intro L h; simp at h; subst h; simp [pc]
  | succ n ih =>
    intro L h
    rw [pc_eq]
    have := ih (L / 2) (by rw [Nat.pow_succ] at h; omega)
    have : L % 2 ≤ 1 := by omega
    omega

theorem pc_full (n : Nat) : ∀ L, L < 2 ^ n → pc L = n → L = 2 ^ n - 1 := by
  induction n with
  | zero => intro L h _; simp at h; simp [h]
  | succ n ih =>
    intro L h hp
    rw [pc_eq] at hp
    have hl : L / 2 < 2 ^ n := by rw [Nat.pow_succ] at h; omega
    have h1 := pc_le n (L / 2) hl
    have hm : L % 2 = 1 := by omega
    have hq := ih (L / 2) hl (by omega)
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    rw [Nat.pow_succ]
    omega

theorem pc_zero : pc 0 = 0 := by simp [pc]

/-! ## Packed lanes -/

/-- `enc W f n = Σ_{L<n} f L · 2^(W·L)`. -/
def enc (W : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => enc W f n + f n * 2 ^ (W * n)

theorem enc_lt (W : Nat) (f : Nat → Nat) (n : Nat) (hf : ∀ L, L < n → f L < 2 ^ W) :
    enc W f n < 2 ^ (W * n) := by
  induction n with
  | zero => simp [enc]
  | succ n ih =>
    simp only [enc]
    have h1 := ih (fun L hL => hf L (by omega))
    have h2 : f n + 1 ≤ 2 ^ W := hf n (by omega)
    have h3 : (f n + 1) * 2 ^ (W * n) ≤ 2 ^ W * 2 ^ (W * n) := Nat.mul_le_mul_right _ h2
    have h4 : 2 ^ (W * (n + 1)) = 2 ^ W * 2 ^ (W * n) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [h4]
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

theorem enc_split (W : Nat) (f : Nat → Nat) (k m : Nat) :
    enc W f (k + m) = enc W f k + 2 ^ (W * k) * enc W (fun L => f (L + k)) m := by
  induction m with
  | zero => simp [enc]
  | succ m ih =>
    rw [show k + (m + 1) = (k + m) + 1 by omega]
    simp only [enc]
    rw [ih, Nat.add_comm m k, Nat.mul_add (2 ^ (W * k)), Nat.mul_add W k m, Nat.pow_add, Nat.add_assoc,
      Nat.mul_left_comm]

theorem enc_shiftRight (W : Nat) (f : Nat → Nat) (k m : Nat) (hf : ∀ L, L < k → f L < 2 ^ W) :
    enc W f (k + m) / 2 ^ (W * k) = enc W (fun L => f (L + k)) m := by
  rw [enc_split, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (enc_lt W f k hf), Nat.zero_add]

theorem enc_add (W : Nat) (f g : Nat → Nat) (n : Nat) :
    enc W f n + enc W g n = enc W (fun L => f L + g L) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [enc]
    rw [← ih, Nat.add_mul]; omega

theorem enc_congr (W : Nat) (f g : Nat → Nat) (n : Nat) (h : ∀ L, L < n → f L = g L) :
    enc W f n = enc W g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [enc]
    rw [ih (fun L hL => h L (by omega)), h n (by omega)]

theorem enc_zero_fn (W n : Nat) : enc W (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [enc, ih]

theorem enc_tail_zero (W : Nat) (f : Nat → Nat) (n m : Nat) (h : ∀ L, n ≤ L → f L = 0) :
    enc W f (n + m) = enc W f n := by
  rw [enc_split]
  have : enc W (fun L => f (L + n)) m = 0 := by
    rw [enc_congr W _ (fun _ => 0) m (fun L _ => h (L + n) (by omega))]
    exact enc_zero_fn W m
  rw [this]; simp

theorem enc_mod (W : Nat) (f : Nat → Nat) (m : Nat) (h0 : f 0 < 2 ^ W) :
    enc W f (1 + m) % 2 ^ W = f 0 := by
  rw [enc_split]
  simp only [enc, Nat.mul_one, Nat.mul_zero, Nat.pow_zero, Nat.zero_add]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]

theorem enc_single (W n : Nat) :
    enc W (fun L => if L = n then 1 else 0) (n + 1) = 2 ^ (W * n) := by
  simp only [enc]
  rw [enc_congr W _ (fun _ => 0) n (fun L hL => by simp; omega), enc_zero_fn]
  simp

/-! ## The abstract backward recursion -/

section Abstract

variable (d : Nat) (a b : Nat → Nat)

/-- Lane function after processing the last `k` rows (`d-1, …, d-k`); row `i` has columns
`i, a i, b i`. -/
def R : Nat → Nat → Nat
  | 0, L => if L = 2 ^ d - 1 then 1 else 0
  | k + 1, L => R k (L + 2 ^ (d - k - 1)) + R k (L + 2 ^ a (d - k - 1)) + R k (L + 2 ^ b (d - k - 1))

theorem R_succ (k L : Nat) :
    R d a b (k + 1) L = R d a b k (L + 2 ^ (d - k - 1)) + R d a b k (L + 2 ^ a (d - k - 1)) +
      R d a b k (L + 2 ^ b (d - k - 1)) := rfl

theorem R_bound (k : Nat) : ∀ L, R d a b k L ≤ 3 ^ k := by
  induction k with
  | zero => intro L; simp only [R]; split <;> simp
  | succ k ih =>
    intro L
    rw [R_succ, Nat.pow_succ]
    have := ih (L + 2 ^ (d - k - 1)); have := ih (L + 2 ^ a (d - k - 1))
    have := ih (L + 2 ^ b (d - k - 1))
    omega

theorem R_above (k : Nat) : ∀ L, 2 ^ d ≤ L → R d a b k L = 0 := by
  induction k with
  | zero =>
    intro L h
    simp only [R]
    have : L ≠ 2 ^ d - 1 := by have := Nat.two_pow_pos d; omega
    simp [this]
  | succ k ih =>
    intro L h
    rw [R_succ, ih (L + 2 ^ (d - k - 1)) (Nat.le_trans h (Nat.le_add_right _ _)),
      ih (L + 2 ^ a (d - k - 1)) (Nat.le_trans h (Nat.le_add_right _ _)),
      ih (L + 2 ^ b (d - k - 1)) (Nat.le_trans h (Nat.le_add_right _ _))]

theorem R_pc (k : Nat) : ∀ L, R d a b k L ≠ 0 → d - k ≤ pc L := by
  induction k with
  | zero =>
    intro L h
    simp only [R] at h
    split at h
    · next hL =>
      subst hL
      have h2 : 2 ^ d - 1 < 2 ^ d := by have := Nat.two_pow_pos d; omega
      -- popcount of 2^d - 1 is d
      have : ∀ n, pc (2 ^ n - 1) = n := by
        intro n
        induction n with
        | zero => simp [pc]
        | succ n ihn =>
          rw [pc_eq]
          have hp := Nat.two_pow_pos n
          have e1 : (2 ^ (n + 1) - 1) % 2 = 1 := by rw [Nat.pow_succ]; omega
          have e2 : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by rw [Nat.pow_succ]; omega
          rw [e1, e2, ihn]; omega
      rw [this]; omega
    · simp at h
  | succ k ih =>
    intro L h
    rw [R_succ] at h
    have key : ∀ j, R d a b k (L + 2 ^ j) ≠ 0 → d - (k + 1) ≤ pc L := by
      intro j hj
      have h1 := ih _ hj
      have h2 := pc_add_le j L
      omega
    by_cases h1 : R d a b k (L + 2 ^ (d - k - 1)) = 0
    · by_cases h2 : R d a b k (L + 2 ^ a (d - k - 1)) = 0
      · exact key (b (d - k - 1)) (by omega)
      · exact key _ h2
    · exact key _ h1

end Abstract

/-! ## The spec's depth-first search, one row at a time -/

/-- Rows `r, r+1, …, d-1` of the generated matrix. -/
def rowsFrom (d s r : Nat) : List (List Nat) := (List.range' r (d - r)).map (genPermanentRow d s)

theorem rowsFrom_succ (d s r : Nat) (h : r < d) :
    rowsFrom d s r = genPermanentRow d s r :: rowsFrom d s (r + 1) := by
  unfold rowsFrom
  have : d - r = (d - (r + 1)) + 1 := by omega
  rw [this, List.range'_succ]
  simp

theorem rowsFrom_end (d s : Nat) : rowsFrom d s d = [] := by simp [rowsFrom]

theorem matrix_eq (d s : Nat) : genPermanentMatrix d s = rowsFrom d s 0 := by
  simp [genPermanentMatrix, rowsFrom, List.range_eq_range']

theorem skipOne_facts (e k n : Nat) (hk : k < n - 1) (he : e < n) :
    permanentSkipOne e k < n ∧ permanentSkipOne e k ≠ e := by
  unfold permanentSkipOne; split <;> omega

theorem skipTwo_facts (a b k n : Nat) (hk : k < n - 2) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    permanentSkipTwo a b k < n ∧ permanentSkipTwo a b k ≠ a ∧ permanentSkipTwo a b k ≠ b := by
  unfold permanentSkipTwo
  by_cases h1 : k < min a b
  · simp only [h1, if_true]; split <;> omega
  · simp only [h1, if_false]; split <;> omega

/-- Facts about the two seeded columns. -/
theorem col_facts (d s r : Nat) (hd : 3 ≤ d) (hr : r < d) :
    permanentColumnOne d s r < d ∧ permanentColumnTwo d s r < d ∧
    permanentColumnOne d s r ≠ r ∧ permanentColumnTwo d s r ≠ r ∧
    permanentColumnTwo d s r ≠ permanentColumnOne d s r := by
  have h1 := skipOne_facts r (permanentMix32 (s ^^^ (r * 0x9e3779b9) ^^^ 0x85ebca6b) % (d - 1)) d
    (Nat.mod_lt _ (by omega)) hr
  have hc1 : permanentColumnOne d s r =
      permanentSkipOne r (permanentMix32 (s ^^^ (r * 0x9e3779b9) ^^^ 0x85ebca6b) % (d - 1)) := rfl
  rw [← hc1] at h1
  have h2 := skipTwo_facts r (permanentColumnOne d s r)
    (permanentMix32 (s ^^^ (r * 0x9e3779b9) ^^^ 0xc2b2ae35) % (d - 2)) d (Nat.mod_lt _ (by omega)) hr h1.1
    (Ne.symm h1.2)
  have hc2 : permanentColumnTwo d s r = permanentSkipTwo r (permanentColumnOne d s r)
      (permanentMix32 (s ^^^ (r * 0x9e3779b9) ^^^ 0xc2b2ae35) % (d - 2)) := rfl
  rw [← hc2] at h2
  exact ⟨h1.1, h2.1, h1.2, h2.2.1, h2.2.2⟩

theorem entry_eq (d s r j : Nat) (hd : 3 ≤ d) (hj : j < d) :
    (genPermanentRow d s r).getD j 0 =
      if j = r ∨ j = permanentColumnOne d s r ∨ j = permanentColumnTwo d s r then 1 else 0 := by
  simp only [genPermanentRow, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, permanentEntry]
  have : ¬ d < 3 := by omega
  simp only [this, if_false]
  by_cases h1 : j = r
  · subst h1; simp
  · by_cases h2 : j = permanentColumnOne d s r
    · simp [h2]
    · by_cases h3 : j = permanentColumnTwo d s r
      · simp [h3]
      · simp [h1, h2, h3, Ne.symm h1]

/-- The depth-first search step for one row: a sum over its three columns. -/
theorem dfs_step (d s r U : Nat) (hd : 3 ≤ d) (hr : r < d) :
    permanentRows d (rowsFrom d s r) U =
      (if U.testBit r then 0 else permanentRows d (rowsFrom d s (r + 1)) (U ||| 1 <<< r)) +
      (if U.testBit (permanentColumnOne d s r) then 0 else
        permanentRows d (rowsFrom d s (r + 1)) (U ||| 1 <<< permanentColumnOne d s r)) +
      (if U.testBit (permanentColumnTwo d s r) then 0 else
        permanentRows d (rowsFrom d s (r + 1)) (U ||| 1 <<< permanentColumnTwo d s r)) := by
  obtain ⟨c1d, c2d, c1r, c2r, c21⟩ := col_facts d s r hd hr
  have hfold : permanentRows d (genPermanentRow d s r :: rowsFrom d s (r + 1)) U =
      (List.range d).foldl (fun t j => if (decide ((genPermanentRow d s r).getD j 0 = 0) || U.testBit j) = true
        then t else t + (genPermanentRow d s r).getD j 0 *
          permanentRows d (rowsFrom d s (r + 1)) (U ||| 1 <<< j)) 0 := by
    rw [permanentRows]
  rw [rowsFrom_succ d s r hr, hfold]
  rw [foldl_range_eq_sumTo
    (fun j => decide ((genPermanentRow d s r).getD j 0 = 0) || U.testBit j)
    (fun j => (genPermanentRow d s r).getD j 0 * permanentRows d (rowsFrom d s (r + 1)) (U ||| 1 <<< j)),
    Nat.zero_add]
  let h : Nat → Nat := fun j => if (decide ((genPermanentRow d s r).getD j 0 = 0) || U.testBit j) = true
    then 0 else (genPermanentRow d s r).getD j 0 * permanentRows d (rowsFrom d s (r + 1)) (U ||| 1 <<< j)
  show sumTo d h = _
  rw [sumTo_three d h r (permanentColumnOne d s r) (permanentColumnTwo d s r) hr c1d c2d
    (Ne.symm c1r) (Ne.symm c2r) (Ne.symm c21)]
  · have e1 : h r = (if U.testBit r then 0 else permanentRows d (rowsFrom d s (r + 1)) (U ||| 1 <<< r)) := by
      simp only [h, entry_eq d s r r hd hr]; simp
    have e2 : h (permanentColumnOne d s r) = (if U.testBit (permanentColumnOne d s r) then 0 else
        permanentRows d (rowsFrom d s (r + 1)) (U ||| 1 <<< permanentColumnOne d s r)) := by
      simp only [h, entry_eq d s r _ hd c1d]; simp
    have e3 : h (permanentColumnTwo d s r) = (if U.testBit (permanentColumnTwo d s r) then 0 else
        permanentRows d (rowsFrom d s (r + 1)) (U ||| 1 <<< permanentColumnTwo d s r)) := by
      simp only [h, entry_eq d s r _ hd c2d]; simp
    rw [e1, e2, e3]
  · intro j hj h1 h2 h3
    simp only [h, entry_eq d s r j hd hj]
    simp [h1, h2, h3]

/-! ## Lanes on popcount-`r` masks equal the depth-first search -/

theorem or_eq_add (U j : Nat) (h : U.testBit j = false) : U ||| 1 <<< j = U + 2 ^ j := by
  rw [Nat.one_shiftLeft]
  have hpj := Nat.two_pow_pos j
  have hbit : U / 2 ^ j % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at h
    simp at h; omega
  have hB : U % 2 ^ (j + 1) < 2 ^ j := by
    rw [Nat.mod_pow_succ, hbit, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_lt _ hpj
  have hB2 : U % 2 ^ (j + 1) + 2 ^ j < 2 ^ (j + 1) := by
    have e : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have eU : U = 2 ^ (j + 1) * (U / 2 ^ (j + 1)) + U % 2 ^ (j + 1) := (Nat.div_add_mod U _).symm
  have e1 : U = 2 ^ (j + 1) * (U / 2 ^ (j + 1)) ||| U % 2 ^ (j + 1) := by
    rw [← Nat.two_pow_add_eq_or_of_lt (Nat.lt_trans hB (Nat.pow_lt_pow_right (by decide) (by omega)))]
    exact eU
  conv => lhs; rw [e1]
  rw [Nat.or_assoc, Nat.or_two_pow_eq_add_of_lt hB, ← Nat.two_pow_add_eq_or_of_lt hB2]
  omega

theorem or_lt (U j d : Nat) (hU : U < 2 ^ d) (hj : j < d) (h : U.testBit j = false) :
    U + 2 ^ j < 2 ^ d := by
  rw [← or_eq_add U j h, Nat.one_shiftLeft]
  exact Nat.or_lt_two_pow hU (Nat.pow_lt_pow_right (by omega) hj)

section Main

variable (d s : Nat)

/-- The columns `a, b` of the abstract recursion are the spec's seeded columns. -/
abbrev Rs := R d (permanentColumnOne d s) (permanentColumnTwo d s)

theorem R_eq_dfs (hd : 3 ≤ d) (k : Nat) (hk : k ≤ d) :
    ∀ U, U < 2 ^ d → pc U = d - k → Rs d s k U = permanentRows d (rowsFrom d s (d - k)) U := by
  induction k with
  | zero =>
    intro U hU hp
    rw [Nat.sub_zero] at hp ⊢
    rw [rowsFrom_end, permanentRows]
    have := pc_full d U hU hp
    simp [Rs, R, this]
  | succ k ih =>
    intro U hU hp
    have hr : d - (k + 1) < d := by omega
    obtain ⟨c1d, c2d, _, _, _⟩ := col_facts d s (d - (k + 1)) hd hr
    rw [dfs_step d s (d - (k + 1)) U hd hr]
    have hsucc : d - (k + 1) + 1 = d - k := by omega
    rw [hsucc]
    simp only [Rs, R_succ]
    have hdk : d - k - 1 = d - (k + 1) := by omega
    rw [hdk]
    have term : ∀ j, j < d → R d (permanentColumnOne d s) (permanentColumnTwo d s) k (U + 2 ^ j) =
        (if U.testBit j then 0 else permanentRows d (rowsFrom d s (d - k)) (U ||| 1 <<< j)) := by
      intro j hj
      cases hb : U.testBit j
      · simp only [Bool.false_eq_true, if_false]
        rw [or_eq_add U j hb]
        apply ih (by omega)
        · exact or_lt U j d hU hj hb
        · rw [pc_add_of_not j U hb, hp]; omega
      · rw [if_pos rfl]
        apply Classical.byContradiction
        intro hne
        have h1 := R_pc d _ _ k _ hne
        have h2 := pc_add_of_set j U hb
        omega
    rw [term _ hr, term _ c1d, term _ c2d]

end Main

/-! ## Packed computation equals the abstract recursion -/

theorem pow3_lt_width (d : Nat) (hd : 1 ≤ d) : 3 ^ d < 2 ^ width d := by
  have hw : width d = 8 * (d / 5) + 2 * (d % 5) := rfl
  rw [hw]
  have hd' : d = 5 * (d / 5) + d % 5 := (Nat.div_add_mod d 5).symm
  have e3 : 3 ^ d = (3 ^ 5) ^ (d / 5) * 3 ^ (d % 5) := by
    conv => lhs; rw [hd']
    rw [Nat.pow_add, Nat.pow_mul]
  have e2 : 2 ^ (8 * (d / 5) + 2 * (d % 5)) = (2 ^ 8) ^ (d / 5) * (2 ^ 2) ^ (d % 5) := by
    rw [Nat.pow_add, Nat.pow_mul, Nat.pow_mul]
  rw [e3, e2]
  have h1 : (3 ^ 5) ^ (d / 5) ≤ (2 ^ 8) ^ (d / 5) := Nat.pow_le_pow_left (by decide) _
  have h4 : 0 < (2 ^ 8) ^ (d / 5) := Nat.pow_pos_iff.mpr (Or.inl (by decide))
  rcases Nat.eq_zero_or_pos (d % 5) with h0 | hpos
  · rw [h0]
    simpa using (Nat.pow_lt_pow_left (show 3 ^ 5 < 2 ^ 8 by decide) (show d / 5 ≠ 0 by omega))
  · have h3 : (3 : Nat) ^ (d % 5) < (2 ^ 2) ^ (d % 5) := Nat.pow_lt_pow_left (by decide) (by omega)
    calc (3 ^ 5) ^ (d / 5) * 3 ^ (d % 5) ≤ (2 ^ 8) ^ (d / 5) * 3 ^ (d % 5) := Nat.mul_le_mul_right _ h1
      _ < (2 ^ 8) ^ (d / 5) * (2 ^ 2) ^ (d % 5) := Nat.mul_lt_mul_of_pos_left h3 h4

theorem mix_eq (x : Nat) : mix x = permanentMix32 x := rfl

theorem skip_eq (e k : Nat) : skip e k = permanentSkipOne e k := by
  simp only [skip, permanentSkipOne]
  show k + (1 - (e - k)) = _
  split <;> omega

theorem skip2_eq (a b k : Nat) : skip2 a b k = permanentSkipTwo a b k := by
  have h1 : Nat.sub a (Nat.sub a b) = min a b := by show a - (a - b) = min a b; omega
  have h2 : Nat.add b (Nat.sub a b) = max a b := by show b + (a - b) = max a b; omega
  unfold skip2
  rw [h1, h2, skip_eq, skip_eq]
  rfl

theorem col1_eq (d s i : Nat) : col1 d s i = permanentColumnOne d s i := by
  unfold col1; rw [skip_eq]; rfl

theorem col2_eq (d s i : Nat) : col2 d s i (col1 d s i) = permanentColumnTwo d s i := by
  unfold col2; rw [skip2_eq, col1_eq]; rfl

theorem step_eq (W i a b X : Nat) :
    step W i a b X = X / 2 ^ (W * 2 ^ i) + X / 2 ^ (W * 2 ^ a) + X / 2 ^ (W * 2 ^ b) := by
  show X >>> (W <<< i) + X >>> (W <<< a) + X >>> (W <<< b) = _
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

/-- Shifting a packed number right by `j` lanes. -/
theorem enc_shift_lanes (W d j : Nat) (f : Nat → Nat) (hj : j < d) (hf : ∀ L, f L < 2 ^ W)
    (hz : ∀ L, 2 ^ d ≤ L → f L = 0) :
    enc W f (2 ^ d) / 2 ^ (W * 2 ^ j) = enc W (fun L => f (L + 2 ^ j)) (2 ^ d) := by
  have hle : 2 ^ j ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
  have e : 2 ^ d = 2 ^ j + (2 ^ d - 2 ^ j) := by omega
  conv => lhs; rw [e]
  rw [enc_shiftRight W f (2 ^ j) _ (fun L _ => hf L)]
  conv => rhs; rw [show 2 ^ d = (2 ^ d - 2 ^ j) + 2 ^ j by omega]
  rw [enc_tail_zero W _ (2 ^ d - 2 ^ j) (2 ^ j) (fun L hL => hz _ (by omega))]

theorem loopG_succ (f : Nat → Nat → Nat) (t X : Nat) : loopG f (t + 1) X = loopG f t (f t X) := rfl

theorem loop_spec (d s : Nat) (hd : 3 ≤ d) (W : Nat) (hW : 3 ^ d < 2 ^ W) :
    ∀ t, t ≤ d → loopG (rowStep d s W) t (enc W (Rs d s (d - t)) (2 ^ d)) = enc W (Rs d s d) (2 ^ d) := by
  intro t
  induction t with
  | zero => intro _; rw [Nat.sub_zero]; rfl
  | succ t ih =>
    intro ht
    rw [loopG_succ]
    have hbound : ∀ k L, Rs d s k L < 2 ^ W → True := fun _ _ _ => trivial
    have hlt : ∀ k, k ≤ d → ∀ L, Rs d s k L < 2 ^ W := by
      intro k hk L
      have h1 := R_bound d (permanentColumnOne d s) (permanentColumnTwo d s) k L
      have h2 : 3 ^ k ≤ 3 ^ d := Nat.pow_le_pow_right (by decide) hk
      exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) hW
    have key : rowStep d s W t (enc W (Rs d s (d - (t + 1))) (2 ^ d)) = enc W (Rs d s (d - t)) (2 ^ d) := by
      have ht' : t < d := by omega
      obtain ⟨c1d, c2d, _, _, _⟩ := col_facts d s t hd ht'
      show step W t (col1 d s t) (col2 d s t (col1 d s t)) _ = _
      rw [col2_eq, col1_eq, step_eq]
      have hz := R_above d (permanentColumnOne d s) (permanentColumnTwo d s) (d - (t + 1))
      have hf := hlt (d - (t + 1)) (by omega)
      rw [enc_shift_lanes W d t _ ht' hf hz, enc_shift_lanes W d _ _ c1d hf hz,
        enc_shift_lanes W d _ _ c2d hf hz, enc_add, enc_add]
      have hk : d - t = (d - (t + 1)) + 1 := by omega
      rw [hk]
      apply enc_congr
      intro L _
      simp only [Rs, R_succ]
      have hi : d - (d - (t + 1)) - 1 = t := by omega
      rw [hi]
    rw [key]
    exact ih (by omega)

theorem fast_eq (d s : Nat) (hd : 3 ≤ d) :
    fast d s (width d) = permanentRows d (rowsFrom d s 0) 0 := by
  have hW := pow3_lt_width d (by omega)
  generalize width d = W at hW ⊢
  have hfast : fast d s W = loopG (rowStep d s W) d (2 ^ (W * (2 ^ d - 1))) % 2 ^ W := by
    show loopG (rowStep d s W) d (1 <<< (W * ((1 <<< d) - 1))) &&& ((1 <<< W) - 1) = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  have hinit : 2 ^ (W * (2 ^ d - 1)) = enc W (Rs d s (d - d)) (2 ^ d) := by
    rw [Nat.sub_self]
    have hpos := Nat.two_pow_pos d
    have e : 2 ^ d = (2 ^ d - 1) + 1 := by omega
    conv => rhs; rw [e]
    rw [← enc_single W (2 ^ d - 1)]
    apply enc_congr
    intro L _
    simp only [Rs, R]
  rw [hfast, hinit, loop_spec d s hd W hW d (Nat.le_refl d)]
  have hpos := Nat.two_pow_pos d
  have e : 2 ^ d = 1 + (2 ^ d - 1) := by omega
  conv => lhs; rw [e]
  rw [enc_mod]
  · have := R_eq_dfs d s hd d (Nat.le_refl d) 0 hpos (by rw [pc_zero]; omega)
    rw [Nat.sub_self] at this
    exact this
  · have h1 := R_bound d (permanentColumnOne d s) (permanentColumnTwo d s) d 0
    exact Nat.lt_of_le_of_lt h1 hW

theorem small_eq (d s : Nat) (hd : d < 3) :
    d + (1 - d) = permanentRows d (genPermanentMatrix d s) 0 := by
  have : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases this with h | h | h <;> subst h <;> rfl

theorem impl_correct : ∀ n, impl n = permanentSpecN n := by
  intro n
  show implAux (permanentDimension n) (permanentSeed n) = _
  simp only [permanentSpecN, permanentSpec]
  generalize permanentDimension n = d
  generalize permanentSeed n = s
  have hlen : (genPermanentMatrix d s).length = d := by simp [genPermanentMatrix]
  rw [hlen]
  by_cases hd : 3 ≤ d
  · have h0 : 3 - d = 0 := by omega
    show Nat.rec (motive := fun _ => Nat) (fast d s (width d))
      (fun _ _ => Nat.add d (Nat.sub (nat_lit 1) d)) (3 - d) = _
    rw [h0, matrix_eq]
    exact fast_eq d s hd
  · have h0 : 3 - d = (2 - d) + 1 := by omega
    show Nat.rec (motive := fun _ => Nat) (fast d s (width d))
      (fun _ _ => Nat.add d (Nat.sub (nat_lit 1) d)) (3 - d) = _
    rw [h0]
    exact small_eq d s (by omega)

end Submission
