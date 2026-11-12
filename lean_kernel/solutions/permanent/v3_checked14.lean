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

/-! Column generation for all rows at once: the hash inputs of rows `0, …, d-1` sit in lanes
of width `w = d + 128` of one natural number, and the three rounds of `permanentMix32` are applied
to all lanes simultaneously (shift, xor, mask, multiply, mask). -/

/-- One `xor-shift, mask, multiply, mask` round on all lanes (`M` holds `0xffffffff` per lane). -/
def mRound (M sh c X : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.land (Nat.xor X (Nat.shiftRight X sh)) M) c) M

/-- Final `xor-shift, mask` round on all lanes. -/
def mLast (M X : Nat) : Nat := Nat.land (Nat.xor X (Nat.shiftRight X (nat_lit 16))) M

/-- `permanentMix32` on every lane. -/
def mixArr (M X : Nat) : Nat :=
  mLast M (mRound M (nat_lit 15) (nat_lit 0x846ca68b) (mRound M (nat_lit 16) (nat_lit 0x7feb352d) X))

/-- `Σ_{i<d} 2^(w·i)`: a `1` in each of `d` lanes (geometric series). -/
def rep (w d : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w d)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

/-- `Σ_{i<d} i·2^(w·i)`: lane `i` holds `i` (closed form of the arithmetico-geometric series). -/
def idx (w d : Nat) : Nat :=
  Nat.div
    (Nat.sub (Nat.add (Nat.mul (Nat.sub d (nat_lit 1)) (Nat.shiftLeft (nat_lit 1) (Nat.mul w (Nat.add d (nat_lit 1)))))
        (Nat.shiftLeft (nat_lit 1) w))
      (Nat.mul d (Nat.shiftLeft (nat_lit 1) (Nat.mul w d))))
    (Nat.pow (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)) (nat_lit 2))

/-- Lane `i`: `s ^^^ (i * 0x9e3779b9)`. -/
def hashArr (s R I : Nat) : Nat := Nat.xor (Nat.mul s R) (Nat.mul I (nat_lit 0x9e3779b9))

/-- Lane `i`: `permanentMix32 (s ^^^ (i * 0x9e3779b9) ^^^ salt)`. -/
def mixes (M R H salt : Nat) : Nat := mixArr M (Nat.xor H (Nat.mul R salt))

/-- `permanentSkipOne e k = k + [e ≤ k]`, branch-free. -/
def skip (e k : Nat) : Nat := Nat.add k (Nat.sub (nat_lit 1) (Nat.sub e k))

/-- `permanentSkipTwo a b k`: skip `min a b`, then `max a b`. -/
def skip2 (a b k : Nat) : Nat :=
  skip (Nat.add b (Nat.sub a b)) (skip (Nat.sub a (Nat.sub a b)) k)

/-- One backward row step on the packed lanes: `Σ_{j ∈ {i,a,b}} X >>> (W·2^j)`. -/
def step (W i a b X : Nat) : Nat :=
  Nat.add (Nat.add (Nat.shiftRight X (Nat.shiftLeft W i)) (Nat.shiftRight X (Nat.shiftLeft W a)))
    (Nat.shiftRight X (Nat.shiftLeft W b))

/-- Row step given the first column `c1` and the reduced second hash `v`. -/
def rowC (W t c1 v X : Nat) : Nat := step W t c1 (skip2 t c1 v) X

/-- Row step for row `t`, reading lane `t` (bit offset `tw`) of the two mixed arrays. -/
def rowS (W dm1 dm2 A1 A2 t tw X : Nat) : Nat :=
  rowC W t (skip t (Nat.mod (Nat.land (Nat.shiftRight A1 tw) (nat_lit 0xffffffff)) dm1))
    (Nat.mod (Nat.land (Nat.shiftRight A2 tw) (nat_lit 0xffffffff)) dm2) X

/-- Row step for row `t`. -/
def rowF (W w dm1 dm2 A1 A2 t X : Nat) : Nat := rowS W dm1 dm2 A1 A2 t (Nat.mul t w) X

/-- `loopG f t X` applies `f (t-1)`, …, `f 0` to `X`, in that order. -/
def loopG (f : Nat → Nat → Nat) (t : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun X => X) (fun t k X => k (f t X)) t

/-- Lane width: `8·(d/5) + 2·(d%5)`, which satisfies `3^d < 2^width` for `d ≥ 1`. -/
def width (d : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 8) (Nat.div d (nat_lit 5))) (Nat.mul (nat_lit 2) (Nat.mod d (nat_lit 5)))

/-- The DP for `d ≥ 3` with DP lane width `W`, given the two mixed hash arrays. -/
def fastC (d W w A1 A2 : Nat) : Nat :=
  Nat.land
    (loopG (rowF W w (Nat.sub d (nat_lit 1)) (Nat.sub d (nat_lit 2)) A1 A2) d
      (Nat.shiftLeft (nat_lit 1) (Nat.mul W (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)))))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))

def fastB (d W w M R H : Nat) : Nat :=
  fastC d W w (mixes M R H (nat_lit 0x85ebca6b)) (mixes M R H (nat_lit 0xc2b2ae35))

def fastA (d s W w R : Nat) : Nat :=
  fastB d W w (Nat.mul R (nat_lit 0xffffffff)) R (hashArr s R (idx w d))

def fast0 (d s w : Nat) : Nat := fastA d s (width d) w (rep w d)

/-- The DP for `d ≥ 3` (hash lanes of width `d + 128`). -/
def fast (d s : Nat) : Nat := fast0 d s (Nat.add d (nat_lit 128))

/-! Fast variant: lanes of only 14 bits, with a proven run-time overflow check after every row
(the top two bits of every lane must stay clear); if any check fails it returns `0` and the
caller falls back to `fast` (lanes wide enough for the worst case). -/

/-- Record the overflow check of the new state `Y` in the accumulator, then continue. -/
def chk (k : Nat → Nat → Nat) (H Y A : Nat) : Nat := k Y (Nat.lor A (Nat.land Y H))

/-- Like `loopG`, accumulating the checks; returns `0` if any check failed. -/
def loopC (f : Nat → Nat → Nat) (H t : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun X A => Nat.rec (motive := fun _ => Nat) X (fun _ _ => nat_lit 0) A)
    (fun t k X A => chk k H (f t X) A) t

def fastK (d W w A1 A2 H : Nat) : Nat :=
  Nat.land
    (loopC (rowF W w (Nat.sub d (nat_lit 1)) (Nat.sub d (nat_lit 2)) A1 A2) H d
      (Nat.shiftLeft (nat_lit 1) (Nat.mul W (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)))) (nat_lit 0))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))

def ckB (d w M R Hh H : Nat) : Nat :=
  fastK d (nat_lit 14) w (mixes M R Hh (nat_lit 0x85ebca6b)) (mixes M R Hh (nat_lit 0xc2b2ae35)) H

def ckA (d s w R : Nat) : Nat :=
  ckB d w (Nat.mul R (nat_lit 0xffffffff)) R (hashArr s R (idx w d))
    (Nat.mul (rep (nat_lit 14) (Nat.shiftLeft (nat_lit 1) d)) (Nat.shiftLeft (nat_lit 3) (nat_lit 12)))

/-- Checked 14-bit-lane DP: `0` or the permanent. -/
def ck (d s : Nat) : Nat := ckA d s (Nat.add d (nat_lit 128)) (rep (Nat.add d (nat_lit 128)) d)

/-- `r` if nonzero, else the fallback `fb`. -/
def sel (fb r : Nat) : Nat := Nat.rec (motive := fun _ => Nat) fb (fun _ _ => r) r

/-- Dimensions `≥ 13` try the checked narrow-lane DP first. -/
def big (d s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (sel (fast d s) (ck d s)) (fun _ _ => fast d s) (Nat.sub (nat_lit 13) d)

/-- Dimensions below 3 have the all-ones matrix: permanent `d! = max d 1`. -/
def implAux (d s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (big d s)
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

/-! ## Lane-wise behaviour of the packed column generation -/

theorem and32 (a : Nat) : a &&& 0xffffffff = a % 2 ^ 32 := by
  have := Nat.and_two_pow_sub_one_eq_mod a 32
  simpa using this

theorem enc_testBit (w : Nat) (hw : 0 < w) (f : Nat → Nat) :
    ∀ n, (∀ i, i < n → f i < 2 ^ w) →
      ∀ k, (enc w f n).testBit k = (decide (k < w * n) && (f (k / w)).testBit (k % w)) := by
  intro n
  induction n with
  | zero => intro _ k; simp [enc]
  | succ n ih =>
    intro hf k
    have hlt := enc_lt w f n (fun i hi => hf i (by omega))
    have e : enc w f (n + 1) = 2 ^ (w * n) * f n + enc w f n := by
      simp only [enc]; rw [Nat.add_comm, Nat.mul_comm]
    have hk := Nat.div_add_mod k w
    have hkw := Nat.mod_lt k hw
    rw [e, Nat.testBit_two_pow_mul_add _ hlt]
    by_cases h1 : k < w * n
    · rw [if_pos h1, ih (fun i hi => hf i (by omega)) k]
      have : k < w * (n + 1) := by rw [Nat.mul_succ]; omega
      simp [h1, this]
    · rw [if_neg h1]
      have hq : n ≤ k / w := (Nat.le_div_iff_mul_le hw).mpr (by rw [Nat.mul_comm]; omega)
      by_cases h2 : k < w * (n + 1)
      · have hq2 : k / w = n := by
          apply Nat.le_antisymm _ hq
          exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hw).mpr (by rw [Nat.mul_comm]; exact h2))
        have hr : k % w = k - w * n := by rw [hq2] at hk; omega
        simp [h2, hq2, hr]
      · have hfn := hf n (by omega)
        have : (f n).testBit (k - w * n) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hfn
            (Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_succ] at h2; omega)))
        simp [h2, this]

theorem enc_and (w : Nat) (hw : 0 < w) (f g : Nat → Nat) (n : Nat)
    (hf : ∀ i, i < n → f i < 2 ^ w) (hg : ∀ i, i < n → g i < 2 ^ w) :
    enc w f n &&& enc w g n = enc w (fun i => f i &&& g i) n := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, enc_testBit w hw f n hf, enc_testBit w hw g n hg,
    enc_testBit w hw _ n (fun i hi => Nat.lt_of_le_of_lt Nat.and_le_left (hf i hi)), Nat.testBit_and]
  cases decide (k < w * n) <;> simp

theorem enc_xor (w : Nat) (hw : 0 < w) (f g : Nat → Nat) (n : Nat)
    (hf : ∀ i, i < n → f i < 2 ^ w) (hg : ∀ i, i < n → g i < 2 ^ w) :
    enc w f n ^^^ enc w g n = enc w (fun i => f i ^^^ g i) n := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, enc_testBit w hw f n hf, enc_testBit w hw g n hg,
    enc_testBit w hw _ n (fun i hi => Nat.xor_lt_two_pow (hf i hi) (hg i hi)), Nat.testBit_xor]
  cases decide (k < w * n) <;> simp

theorem enc_mul (w : Nat) (f : Nat → Nat) (c n : Nat) :
    enc w f n * c = enc w (fun i => f i * c) n := by
  induction n with
  | zero => simp [enc]
  | succ n ih => simp only [enc]; rw [Nat.add_mul, ih, Nat.mul_right_comm]

theorem enc_shr_and (w : Nat) (hw : 0 < w) (f : Nat → Nat) (n : Nat) (hf : ∀ i, i < n → f i < 2 ^ w)
    (b s m : Nat) (hm : m = 2 ^ b - 1) (hbs : b + s ≤ w) :
    (enc w f n >>> s) &&& enc w (fun _ => m) n = enc w (fun i => (f i >>> s) &&& m) n := by
  subst hm
  have hb : 2 ^ b - 1 < 2 ^ w := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show b ≤ w by omega)
    have := Nat.two_pow_pos b
    omega
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, Nat.testBit_shiftRight, enc_testBit w hw f n hf, enc_testBit w hw _ n (fun _ _ => hb),
    enc_testBit w hw _ n (fun i _ => Nat.lt_of_le_of_lt Nat.and_le_right hb), Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  have hk := Nat.div_add_mod k w
  have hkw := Nat.mod_lt k hw
  generalize k / w = q at hk ⊢
  generalize k % w = r at hk hkw ⊢
  subst hk
  by_cases hr : r < b
  · have e1 : (s + (w * q + r)) / w = q := by
      rw [show s + (w * q + r) = w * q + (s + r) by omega, Nat.mul_add_div hw, Nat.div_eq_of_lt (by omega)]
      simp
    have e2 : (s + (w * q + r)) % w = s + r := by
      rw [show s + (w * q + r) = w * q + (s + r) by omega, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have e3 : decide (s + (w * q + r) < w * n) = decide (w * q + r < w * n) := by
      have h4 : (w * q + r < w * n) ↔ q < n := by
        constructor
        · intro h; apply Classical.byContradiction; intro hn
          have : w * n ≤ w * q := Nat.mul_le_mul_left w (by omega)
          omega
        · intro h; have : w * (q + 1) ≤ w * n := Nat.mul_le_mul_left w h
          rw [Nat.mul_succ] at this; omega
      have h5 : (s + (w * q + r) < w * n) ↔ q < n := by
        constructor
        · intro h; apply Classical.byContradiction; intro hn
          have : w * n ≤ w * q := Nat.mul_le_mul_left w (by omega)
          omega
        · intro h; have : w * (q + 1) ≤ w * n := Nat.mul_le_mul_left w h
          rw [Nat.mul_succ] at this; omega
      simp only [decide_eq_decide]; exact h5.trans h4.symm
    rw [e1, e2, e3]
    simp [hr]
    intro h _; exact h
  · simp [hr]

theorem enc_const_lt (w n v : Nat) (hv : v < 2 ^ w) : ∀ i, i < n → (fun _ => v) i < 2 ^ w :=
  fun _ _ => hv

/-- Lane value of one `mRound`. -/
def laneR (sh c x : Nat) : Nat := (((x ^^^ (x >>> sh)) &&& 0xffffffff) * c) &&& 0xffffffff

/-- Lane value of `mLast`. -/
def laneL (x : Nat) : Nat := (x ^^^ (x >>> 16)) &&& 0xffffffff

theorem lane_mix (x : Nat) : laneL (laneR 15 0x846ca68b (laneR 16 0x7feb352d x)) = permanentMix32 x := by
  unfold laneL laneR permanentMix32
  simp only [and32, Nat.mod_mul_mod]

theorem ffff_lt (w : Nat) (hw : 64 ≤ w) : (0xffffffff : Nat) < 2 ^ w :=
  Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 32 ≤ w by omega))

theorem lane32_lt (w : Nat) (hw : 64 ≤ w) (a : Nat) : a &&& 0xffffffff < 2 ^ w :=
  Nat.lt_of_le_of_lt Nat.and_le_right (ffff_lt w hw)

theorem mRound_enc (w n sh c : Nat) (hw : 64 ≤ w) (hsh : sh ≤ 32) (hc : c < 2 ^ 32) (x : Nat → Nat)
    (hx : ∀ i, i < n → x i < 2 ^ w) :
    mRound (enc w (fun _ => 0xffffffff) n) sh c (enc w x n) = enc w (fun i => laneR sh c (x i)) n := by
  have hw0 : 0 < w := by omega
  have hM := enc_const_lt w n _ (ffff_lt w hw)
  show (((enc w x n ^^^ (enc w x n >>> sh)) &&& enc w (fun _ => 0xffffffff) n) * c) &&&
    enc w (fun _ => 0xffffffff) n = _
  rw [Nat.and_xor_distrib_right, enc_and w hw0 x _ n hx hM,
    enc_shr_and w hw0 x n hx 32 sh 0xffffffff (by decide) (by omega),
    enc_xor w hw0 _ _ n (fun i _ => lane32_lt w hw _) (fun i _ => lane32_lt w hw _), enc_mul,
    enc_and w hw0 _ _ n _ hM]
  · apply enc_congr; intro i _
    unfold laneR; rw [Nat.and_xor_distrib_right]
  · intro i _
    have h1 : (x i &&& 0xffffffff ^^^ x i >>> sh &&& 0xffffffff) < 2 ^ 32 :=
      Nat.xor_lt_two_pow (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
        (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
    have h2 : (x i &&& 0xffffffff ^^^ x i >>> sh &&& 0xffffffff) * c < 2 ^ 32 * 2 ^ 32 :=
      Nat.mul_lt_mul_of_lt_of_lt h1 hc
    exact Nat.lt_of_lt_of_le h2 (by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega))

theorem mLast_enc (w n : Nat) (hw : 64 ≤ w) (x : Nat → Nat) (hx : ∀ i, i < n → x i < 2 ^ w) :
    mLast (enc w (fun _ => 0xffffffff) n) (enc w x n) = enc w (fun i => laneL (x i)) n := by
  have hw0 : 0 < w := by omega
  have hM := enc_const_lt w n _ (ffff_lt w hw)
  show (enc w x n ^^^ (enc w x n >>> 16)) &&& enc w (fun _ => 0xffffffff) n = _
  rw [Nat.and_xor_distrib_right, enc_and w hw0 x _ n hx hM,
    enc_shr_and w hw0 x n hx 32 16 0xffffffff (by decide) (by omega),
    enc_xor w hw0 _ _ n (fun i _ => lane32_lt w hw _) (fun i _ => lane32_lt w hw _)]
  apply enc_congr; intro i _
  unfold laneL; rw [Nat.and_xor_distrib_right]

theorem mixArr_enc (w n : Nat) (hw : 64 ≤ w) (x : Nat → Nat) (hx : ∀ i, i < n → x i < 2 ^ w) :
    mixArr (enc w (fun _ => 0xffffffff) n) (enc w x n) = enc w (fun i => permanentMix32 (x i)) n := by
  unfold mixArr
  rw [mRound_enc w n 16 _ hw (by decide) (by decide) x hx,
    mRound_enc w n 15 _ hw (by decide) (by decide) _ (fun i _ => by unfold laneR; exact lane32_lt w hw _),
    mLast_enc w n hw _ (fun i _ => by unfold laneR; exact lane32_lt w hw _)]
  apply enc_congr; intro i _
  exact lane_mix (x i)

theorem rep_eq (w d : Nat) (hw : 1 ≤ w) : rep w d = enc w (fun _ => 1) d := by
  have key : ∀ n, enc w (fun _ => 1) n * (2 ^ w - 1) + 1 = 2 ^ (w * n) := by
    intro n
    induction n with
    | zero => simp [enc]
    | succ n ih =>
      simp only [enc]
      have hp : 2 ^ (w * (n + 1)) = 2 ^ (w * n) * 2 ^ w := by rw [Nat.mul_succ, Nat.pow_add]
      rw [hp, ← ih]
      have h2 : 2 ≤ 2 ^ w := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hw; simpa using this
      generalize enc w (fun _ => 1) n = E
      generalize 2 ^ w = P at h2 ⊢
      obtain ⟨y, rfl⟩ : ∃ y, P = y + 1 := ⟨P - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      grind
  show (1 <<< (w * d) - 1) / (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
  have h2 : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hw; simpa using this
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have := key d
  omega

theorem idx_eq (w d : Nat) (hw : 1 ≤ w) (hd : 1 ≤ d) : idx w d = enc w (fun i => i) d := by
  have key : ∀ n, enc w (fun i => i) (n + 1) * (2 ^ w - 1) ^ 2 + (n + 1) * 2 ^ (w * (n + 1)) =
      n * 2 ^ (w * (n + 1 + 1)) + 2 ^ w := by
    intro n
    induction n with
    | zero => simp [enc]
    | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 from rfl]
      simp only [enc] at ih ⊢
      simp only [Nat.pow_mul] at ih ⊢
      have h2 : 2 ≤ 2 ^ w := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hw; simpa using this
      generalize enc w (fun i => i) n = E at ih ⊢
      generalize 2 ^ w = P at h2 ih ⊢
      obtain ⟨y, rfl⟩ : ∃ y, P = y + 1 := ⟨P - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at ih ⊢
      grind
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  show ((n + 1 - 1) * (1 <<< (w * (n + 1 + 1))) + (1 <<< w) - (n + 1) * (1 <<< (w * (n + 1)))) /
    ((1 <<< w) - 1) ^ 2 = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.add_sub_cancel]
  have h2 : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hw; simpa using this
  have hpos : 0 < (2 ^ w - 1) ^ 2 := Nat.pow_pos_iff.mpr (Or.inl (by omega))
  apply Nat.div_eq_of_eq_mul_left hpos
  have := key n
  omega

/-- Reading lane `t` of a packed array (values below `2^32`). -/
theorem extract (w d t : Nat) (f : Nat → Nat) (hw : 64 ≤ w) (ht : t < d)
    (hf : ∀ i, i < d → f i < 2 ^ w) (h32 : f t < 2 ^ 32) :
    Nat.land (Nat.shiftRight (enc w f d) (Nat.mul t w)) (nat_lit 0xffffffff) = f t := by
  show (enc w f d >>> (t * w)) &&& 0xffffffff = f t
  rw [and32, Nat.shiftRight_eq_div_pow]
  have e : d = t + (1 + (d - t - 1)) := by omega
  rw [e, Nat.mul_comm t w, enc_shiftRight w f t _ (fun L hL => hf L (by omega)),
    ← Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show 32 ≤ w by omega)), enc_mod]
  · simp only [Nat.zero_add]; exact Nat.mod_eq_of_lt h32
  · simp only [Nat.zero_add]; exact hf t ht

/-- The hash lanes of the spec. -/
def hlane (s salt i : Nat) : Nat := s ^^^ (i * 0x9e3779b9) ^^^ salt

theorem hlane_lt (w d s salt : Nat) (hw : w = d + 128) (hs : s < 2 ^ 32) (hsalt : salt < 2 ^ 32) :
    ∀ i, i < d → hlane s salt i < 2 ^ w := by
  intro i hi
  have h1 : s < 2 ^ w := Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega))
  have h2 : salt < 2 ^ w := Nat.lt_of_lt_of_le hsalt (Nat.pow_le_pow_right (by decide) (by omega))
  have h3 : i * 0x9e3779b9 < 2 ^ w := by
    have hd : d < 2 ^ d := Nat.lt_two_pow_self
    have : i * 0x9e3779b9 < 2 ^ d * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_lt (by omega) (by decide)
    rw [← Nat.pow_add] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h1 h3) h2

theorem mixes_enc (d s w : Nat) (hd1 : 1 ≤ d) (hw : w = d + 128) (hs : s < 2 ^ 32) (salt : Nat)
    (hsalt : salt < 2 ^ 32) :
    mixes (Nat.mul (rep w d) (nat_lit 0xffffffff)) (rep w d) (hashArr s (rep w d) (idx w d)) salt =
      enc w (fun i => permanentMix32 (hlane s salt i)) d := by
  have hw1 : 1 ≤ w := by omega
  have hw0 : 0 < w := by omega
  have hw64 : 64 ≤ w := by omega
  have hR := rep_eq w d hw1
  have hI := idx_eq w d hw1 hd1
  have hs' : s < 2 ^ w := Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega))
  have hsalt' : salt < 2 ^ w := Nat.lt_of_lt_of_le hsalt (Nat.pow_le_pow_right (by decide) (by omega))
  have hM : Nat.mul (rep w d) (nat_lit 0xffffffff) = enc w (fun _ => 0xffffffff) d := by
    show rep w d * 0xffffffff = _
    rw [hR, enc_mul] <;> simp
  have hS : Nat.mul s (rep w d) = enc w (fun _ => s) d := by
    show s * rep w d = _
    rw [hR, Nat.mul_comm, enc_mul] <;> simp
  have hK : Nat.mul (idx w d) (nat_lit 0x9e3779b9) = enc w (fun i => i * 0x9e3779b9) d := by
    show idx w d * 0x9e3779b9 = _
    rw [hI, enc_mul]
  have hT : Nat.mul (rep w d) salt = enc w (fun _ => salt) d := by
    show rep w d * salt = _
    rw [hR, enc_mul] <;> simp
  have hK' := hlane_lt w d 0 0 hw (by decide) (by decide)
  have hKlt : ∀ i, i < d → i * 0x9e3779b9 < 2 ^ w := by
    intro i hi; have := hK' i hi; simp [hlane] at this; exact this
  unfold mixes hashArr
  rw [hM, hS, hK, hT]
  show mixArr (enc w (fun _ => 0xffffffff) d)
    ((enc w (fun _ => s) d ^^^ enc w (fun i => i * 0x9e3779b9) d) ^^^ enc w (fun _ => salt) d) = _
  rw [enc_xor w hw0 _ _ d (fun _ _ => hs') hKlt,
    enc_xor w hw0 _ _ d (fun i hi => Nat.xor_lt_two_pow hs' (hKlt i hi)) (fun _ _ => hsalt'),
    mixArr_enc w d hw64 _ (fun i hi => Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hs' (hKlt i hi)) hsalt')]
  rfl

theorem mix_lt (x : Nat) : permanentMix32 x < 2 ^ 32 := by
  have h : ∀ y : Nat, y &&& 0xffffffff < 2 ^ 32 := fun y => by
    rw [and32]; exact Nat.mod_lt _ (Nat.two_pow_pos 32)
  exact h _

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

theorem rowF_eq (d s W w dm1 dm2 t X : Nat) (ht : t < d) (hw : w = d + 128)
    (h1 : dm1 = d - 1) (h2 : dm2 = d - 2) :
    rowF W w dm1 dm2 (enc w (fun i => permanentMix32 (hlane s 0x85ebca6b i)) d)
      (enc w (fun i => permanentMix32 (hlane s 0xc2b2ae35 i)) d) t X =
      step W t (permanentColumnOne d s t) (permanentColumnTwo d s t) X := by
  have hw64 : 64 ≤ w := by omega
  have e1 : Nat.mod (Nat.land (Nat.shiftRight (enc w (fun i => permanentMix32 (hlane s 0x85ebca6b i)) d)
      (Nat.mul t w)) (nat_lit 0xffffffff)) dm1 =
      permanentMix32 (s ^^^ (t * 0x9e3779b9) ^^^ 0x85ebca6b) % (d - 1) := by
    rw [extract w d t _ hw64 ht (fun i _ => Nat.lt_of_lt_of_le (mix_lt _)
      (Nat.pow_le_pow_right (by decide) (by omega))) (mix_lt _), h1]
    rfl
  have e2 : Nat.mod (Nat.land (Nat.shiftRight (enc w (fun i => permanentMix32 (hlane s 0xc2b2ae35 i)) d)
      (Nat.mul t w)) (nat_lit 0xffffffff)) dm2 =
      permanentMix32 (s ^^^ (t * 0x9e3779b9) ^^^ 0xc2b2ae35) % (d - 2) := by
    rw [extract w d t _ hw64 ht (fun i _ => Nat.lt_of_lt_of_le (mix_lt _)
      (Nat.pow_le_pow_right (by decide) (by omega))) (mix_lt _), h2]
    rfl
  unfold rowF rowS rowC
  rw [e1, e2, skip_eq, skip2_eq]
  have hc1 : permanentColumnOne d s t =
      permanentSkipOne t (permanentMix32 (s ^^^ (t * 0x9e3779b9) ^^^ 0x85ebca6b) % (d - 1)) := rfl
  have hc2 : permanentColumnTwo d s t = permanentSkipTwo t (permanentColumnOne d s t)
      (permanentMix32 (s ^^^ (t * 0x9e3779b9) ^^^ 0xc2b2ae35) % (d - 2)) := rfl
  rw [← hc1, ← hc2]

theorem loop_spec (d s : Nat) (hd : 3 ≤ d) (W : Nat) (hW : 3 ^ d < 2 ^ W) (f : Nat → Nat → Nat)
    (hf : ∀ t X, t < d → f t X = step W t (permanentColumnOne d s t) (permanentColumnTwo d s t) X) :
    ∀ t, t ≤ d → loopG f t (enc W (Rs d s (d - t)) (2 ^ d)) = enc W (Rs d s d) (2 ^ d) := by
  intro t
  induction t with
  | zero => intro _; rw [Nat.sub_zero]; rfl
  | succ t ih =>
    intro ht
    rw [loopG_succ]
    have hlt : ∀ k, k ≤ d → ∀ L, Rs d s k L < 2 ^ W := by
      intro k hk L
      have h1 := R_bound d (permanentColumnOne d s) (permanentColumnTwo d s) k L
      have h2 : 3 ^ k ≤ 3 ^ d := Nat.pow_le_pow_right (by decide) hk
      exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) hW
    have key : f t (enc W (Rs d s (d - (t + 1))) (2 ^ d)) = enc W (Rs d s (d - t)) (2 ^ d) := by
      have ht' : t < d := by omega
      obtain ⟨c1d, c2d, _, _, _⟩ := col_facts d s t hd ht'
      rw [hf t _ ht', step_eq]
      have hz := R_above d (permanentColumnOne d s) (permanentColumnTwo d s) (d - (t + 1))
      have hf' := hlt (d - (t + 1)) (by omega)
      rw [enc_shift_lanes W d t _ ht' hf' hz, enc_shift_lanes W d _ _ c1d hf' hz,
        enc_shift_lanes W d _ _ c2d hf' hz, enc_add, enc_add]
      have hk : d - t = (d - (t + 1)) + 1 := by omega
      rw [hk]
      apply enc_congr
      intro L _
      simp only [Rs, R_succ]
      have hi : d - (d - (t + 1)) - 1 = t := by omega
      rw [hi]
    rw [key]
    exact ih (by omega)

theorem fast_eq (d s : Nat) (hd : 3 ≤ d) (hs : s < 2 ^ 32) :
    fast d s = permanentRows d (rowsFrom d s 0) 0 := by
  have hW := pow3_lt_width d (by omega)
  show fastC d (width d) (d + 128)
    (mixes (Nat.mul (rep (d + 128) d) (nat_lit 0xffffffff)) (rep (d + 128) d)
      (hashArr s (rep (d + 128) d) (idx (d + 128) d)) (nat_lit 0x85ebca6b))
    (mixes (Nat.mul (rep (d + 128) d) (nat_lit 0xffffffff)) (rep (d + 128) d)
      (hashArr s (rep (d + 128) d) (idx (d + 128) d)) (nat_lit 0xc2b2ae35)) = _
  rw [mixes_enc d s (d + 128) (by omega) rfl hs _ (by decide),
    mixes_enc d s (d + 128) (by omega) rfl hs _ (by decide)]
  generalize width d = W at hW ⊢
  have hfast : fastC d W (d + 128) (enc (d + 128) (fun i => permanentMix32 (hlane s 0x85ebca6b i)) d)
      (enc (d + 128) (fun i => permanentMix32 (hlane s 0xc2b2ae35 i)) d) =
      loopG (rowF W (d + 128) (Nat.sub d (nat_lit 1)) (Nat.sub d (nat_lit 2))
        (enc (d + 128) (fun i => permanentMix32 (hlane s 0x85ebca6b i)) d)
        (enc (d + 128) (fun i => permanentMix32 (hlane s 0xc2b2ae35 i)) d)) d
        (2 ^ (W * (2 ^ d - 1))) % 2 ^ W := by
    show loopG _ d (1 <<< (W * ((1 <<< d) - 1))) &&& ((1 <<< W) - 1) = _
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
  rw [hfast, hinit, loop_spec d s hd W hW (rowF W (d + 128) (Nat.sub d (nat_lit 1)) (Nat.sub d (nat_lit 2))
      (enc (d + 128) (fun i => permanentMix32 (hlane s 0x85ebca6b i)) d)
      (enc (d + 128) (fun i => permanentMix32 (hlane s 0xc2b2ae35 i)) d))
    (fun t X ht => rowF_eq d s W (d + 128) _ _ t X ht rfl rfl rfl) d (Nat.le_refl d)]
  have hpos := Nat.two_pow_pos d
  have e : 2 ^ d = 1 + (2 ^ d - 1) := by omega
  conv => lhs; rw [e]
  rw [enc_mod]
  · have := R_eq_dfs d s hd d (Nat.le_refl d) 0 hpos (by rw [pc_zero]; omega)
    rw [Nat.sub_self] at this
    exact this
  · have h1 := R_bound d (permanentColumnOne d s) (permanentColumnTwo d s) d 0
    exact Nat.lt_of_le_of_lt h1 hW

theorem step_enc (d s : Nat) (hd : 3 ≤ d) (W : Nat) (f : Nat → Nat → Nat)
    (hf : ∀ t X, t < d → f t X = step W t (permanentColumnOne d s t) (permanentColumnTwo d s t) X)
    (t : Nat) (ht' : t < d) (hlt : ∀ L, Rs d s (d - (t + 1)) L < 2 ^ W) :
    f t (enc W (Rs d s (d - (t + 1))) (2 ^ d)) = enc W (Rs d s (d - t)) (2 ^ d) := by
  obtain ⟨c1d, c2d, _, _, _⟩ := col_facts d s t hd ht'
  rw [hf t _ ht', step_eq]
  have hz := R_above d (permanentColumnOne d s) (permanentColumnTwo d s) (d - (t + 1))
  rw [enc_shift_lanes W d t _ ht' hlt hz, enc_shift_lanes W d _ _ c1d hlt hz,
    enc_shift_lanes W d _ _ c2d hlt hz, enc_add, enc_add]
  have hk : d - t = (d - (t + 1)) + 1 := by omega
  rw [hk]
  apply enc_congr
  intro L _
  simp only [Rs, R_succ]
  have hi : d - (d - (t + 1)) - 1 = t := by omega
  rw [hi]

theorem lane_check (W g : Nat) (hW : 2 ≤ W) (hg : g < 2 ^ W) (h0 : g &&& 3 * 2 ^ (W - 2) = 0) :
    g < 2 ^ (W - 2) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases hiW : i < W
  · have h1 : (g &&& 3 * 2 ^ (W - 2)).testBit i = false := by rw [h0]; exact Nat.zero_testBit i
    have h2 : (3 * 2 ^ (W - 2)).testBit i = true := by
      rw [Nat.mul_comm, Nat.testBit_two_pow_mul, decide_eq_true hi, Bool.true_and]
      have : i - (W - 2) = 0 ∨ i - (W - 2) = 1 := by omega
      rcases this with h | h <;> rw [h] <;> decide
    rw [Nat.testBit_and, h2, Bool.and_true] at h1
    exact h1
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (by decide) (by omega)))

theorem enc_check (W N : Nat) (hW : 2 ≤ W) (g : Nat → Nat) (hg : ∀ L, L < N → g L < 2 ^ W)
    (h0 : enc W g N &&& enc W (fun _ => 3 * 2 ^ (W - 2)) N = 0) : ∀ L, L < N → g L < 2 ^ (W - 2) := by
  have hW0 : 0 < W := by omega
  have hc : 3 * 2 ^ (W - 2) < 2 ^ W := by
    have e : 2 ^ W = 4 * 2 ^ (W - 2) := by
      rw [show W = (W - 2) + 2 by omega, Nat.pow_add]; simp; omega
    have := Nat.two_pow_pos (W - 2); omega
  rw [enc_and W hW0 g _ N hg (fun _ _ => hc)] at h0
  intro L hL
  apply lane_check W (g L) hW (hg L hL)
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < W
  · have := enc_testBit W hW0 (fun L => g L &&& 3 * 2 ^ (W - 2)) N
      (fun L hL => Nat.lt_of_le_of_lt Nat.and_le_right hc) (W * L + i)
    rw [h0, Nat.zero_testBit] at this
    have e1 : (W * L + i) / W = L := by rw [Nat.mul_add_div hW0, Nat.div_eq_of_lt hi]; simp
    have e2 : (W * L + i) % W = i := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    have e3 : W * L + i < W * N := by
      have : W * (L + 1) ≤ W * N := Nat.mul_le_mul_left W hL
      rw [Nat.mul_succ] at this; omega
    rw [e1, e2] at this
    simp [e3] at this
    rw [Nat.testBit_and]
    cases h1 : (g L).testBit i
    · simp
    · simp [this h1]
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt Nat.and_le_right hc)
      (Nat.pow_le_pow_right (by decide) (by omega)))

theorem loopC_zero (f : Nat → Nat → Nat) (H : Nat) :
    ∀ t X A, A ≠ 0 → loopC f H t X A = 0 := by
  intro t
  induction t with
  | zero =>
    intro X A hA
    obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
    rfl
  | succ t ih =>
    intro X A hA
    show chk (loopC f H t) H (f t X) A = 0
    unfold chk
    apply ih
    intro h
    exact hA (Nat.or_eq_zero_iff.mp h).1

theorem loopC_spec (d s : Nat) (hd : 3 ≤ d) (W : Nat) (hW : 2 ≤ W) (f : Nat → Nat → Nat)
    (hf : ∀ t X, t < d → f t X = step W t (permanentColumnOne d s t) (permanentColumnTwo d s t) X) :
    ∀ t, t ≤ d → ∀ A, (∀ L, Rs d s (d - t) L < 2 ^ (W - 2)) →
      loopC f (enc W (fun _ => 3 * 2 ^ (W - 2)) (2 ^ d)) t (enc W (Rs d s (d - t)) (2 ^ d)) A = 0 ∨
      (loopC f (enc W (fun _ => 3 * 2 ^ (W - 2)) (2 ^ d)) t (enc W (Rs d s (d - t)) (2 ^ d)) A =
        enc W (Rs d s d) (2 ^ d) ∧ Rs d s d 0 < 2 ^ W) := by
  have hp : 2 ^ (W - 2) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) (by omega)
  have h4 : 2 ^ W = 4 * 2 ^ (W - 2) := by
    rw [show W = (W - 2) + 2 by omega, Nat.pow_add]; simp; omega
  intro t
  induction t with
  | zero =>
    intro _ A hb
    rw [Nat.sub_zero] at hb ⊢
    rcases Nat.eq_zero_or_pos A with h | h
    · subst h; right; exact ⟨rfl, Nat.lt_of_lt_of_le (hb 0) hp⟩
    · left; exact loopC_zero f _ 0 _ A (by omega)
  | succ t ih =>
    intro ht A hb
    have ht' : t < d := by omega
    show chk (loopC f _ t) _ (f t _) A = 0 ∨ (chk (loopC f _ t) _ (f t _) A = _ ∧ _)
    unfold chk
    rw [step_enc d s hd W f hf t ht' (fun L => Nat.lt_of_lt_of_le (hb L) hp)]
    have hnew : ∀ L, Rs d s (d - t) L < 2 ^ W := by
      intro L
      have hk : d - t = (d - (t + 1)) + 1 := by omega
      rw [hk]; simp only [Rs, R_succ]
      have := hb (L + 2 ^ (d - (d - (t + 1)) - 1))
      have := hb (L + 2 ^ permanentColumnOne d s (d - (d - (t + 1)) - 1))
      have := hb (L + 2 ^ permanentColumnTwo d s (d - (d - (t + 1)) - 1))
      simp only [Rs] at *
      omega
    by_cases hc : enc W (Rs d s (d - t)) (2 ^ d) &&& enc W (fun _ => 3 * 2 ^ (W - 2)) (2 ^ d) = 0
    · have hA : Nat.lor A (Nat.land (enc W (Rs d s (d - t)) (2 ^ d)) (enc W (fun _ => 3 * 2 ^ (W - 2)) (2 ^ d)))
          = A := by
        show A ||| (enc W (Rs d s (d - t)) (2 ^ d) &&& enc W (fun _ => 3 * 2 ^ (W - 2)) (2 ^ d)) = A
        rw [hc, Nat.or_zero]
      rw [hA]
      apply ih (by omega)
      intro L
      by_cases hL : L < 2 ^ d
      · exact enc_check W (2 ^ d) hW _ (fun L _ => hnew L) hc L hL
      · rw [show Rs d s (d - t) L = 0 from R_above d _ _ _ L (by omega)]; exact Nat.two_pow_pos _
    · left
      apply loopC_zero
      intro h
      exact hc (Nat.or_eq_zero_iff.mp h).2

theorem ck_spec (d s : Nat) (hd : 3 ≤ d) (hs : s < 2 ^ 32) :
    ck d s = 0 ∨ ck d s = permanentRows d (rowsFrom d s 0) 0 := by
  have hH : Nat.mul (rep (nat_lit 14) (Nat.shiftLeft (nat_lit 1) d)) (Nat.shiftLeft (nat_lit 3) (nat_lit 12)) =
      enc 14 (fun _ => 3 * 2 ^ (14 - 2)) (2 ^ d) := by
    show rep 14 (1 <<< d) * (3 <<< 12) = _
    rw [Nat.one_shiftLeft, rep_eq 14 _ (by decide), enc_mul]
    rfl
  have hck : ck d s = fastK d 14 (d + 128)
    (mixes (Nat.mul (rep (d + 128) d) (nat_lit 0xffffffff)) (rep (d + 128) d)
      (hashArr s (rep (d + 128) d) (idx (d + 128) d)) (nat_lit 0x85ebca6b))
    (mixes (Nat.mul (rep (d + 128) d) (nat_lit 0xffffffff)) (rep (d + 128) d)
      (hashArr s (rep (d + 128) d) (idx (d + 128) d)) (nat_lit 0xc2b2ae35))
    (Nat.mul (rep (nat_lit 14) (Nat.shiftLeft (nat_lit 1) d)) (Nat.shiftLeft (nat_lit 3) (nat_lit 12))) := rfl
  rw [hck, mixes_enc d s (d + 128) (by omega) rfl hs _ (by decide),
    mixes_enc d s (d + 128) (by omega) rfl hs _ (by decide), hH]
  have hinit : 2 ^ (14 * (2 ^ d - 1)) = enc 14 (Rs d s (d - d)) (2 ^ d) := by
    rw [Nat.sub_self]
    have hpos := Nat.two_pow_pos d
    have e : 2 ^ d = (2 ^ d - 1) + 1 := by omega
    conv => rhs; rw [e]
    rw [← enc_single 14 (2 ^ d - 1)]
    apply enc_congr
    intro L _
    simp only [Rs, R]
  have hK : ∀ A1 A2 H, fastK d 14 (d + 128) A1 A2 H =
      loopC (rowF 14 (d + 128) (Nat.sub d (nat_lit 1)) (Nat.sub d (nat_lit 2)) A1 A2) H d
        (2 ^ (14 * (2 ^ d - 1))) 0 % 2 ^ 14 := by
    intro A1 A2 H
    show loopC _ H d (1 <<< (14 * ((1 <<< d) - 1))) 0 &&& ((1 <<< 14) - 1) = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  rw [hK, hinit]
  have hb0 : ∀ L, Rs d s (d - d) L < 2 ^ (14 - 2) := by
    intro L; rw [Nat.sub_self]; simp only [Rs, R]; split <;> decide
  rcases loopC_spec d s hd 14 (by decide) (rowF 14 (d + 128) (Nat.sub d (nat_lit 1)) (Nat.sub d (nat_lit 2))
      (enc (d + 128) (fun i => permanentMix32 (hlane s 0x85ebca6b i)) d)
      (enc (d + 128) (fun i => permanentMix32 (hlane s 0xc2b2ae35 i)) d))
    (fun t X ht => rowF_eq d s 14 (d + 128) _ _ t X ht rfl rfl rfl) d (Nat.le_refl d) 0 hb0 with h | ⟨h, hlt⟩
  · left; rw [h]
  · right
    rw [h]
    have hpos := Nat.two_pow_pos d
    have e : 2 ^ d = 1 + (2 ^ d - 1) := by omega
    conv => lhs; rw [e]
    rw [enc_mod _ _ _ hlt]
    have := R_eq_dfs d s hd d (Nat.le_refl d) 0 hpos (by rw [pc_zero]; omega)
    rw [Nat.sub_self] at this
    exact this

theorem big_eq (d s : Nat) (hd : 3 ≤ d) (hs : s < 2 ^ 32) :
    big d s = permanentRows d (rowsFrom d s 0) 0 := by
  unfold big
  generalize Nat.sub (nat_lit 13) d = k
  cases k with
  | zero =>
    show sel (fast d s) (ck d s) = _
    unfold sel
    rcases ck_spec d s hd hs with h | h
    · rw [h]; exact fast_eq d s hd hs
    · cases hc : ck d s with
      | zero => exact fast_eq d s hd hs
      | succ c => rw [← h, hc]
  | succ k => exact fast_eq d s hd hs

theorem small_eq (d s : Nat) (hd : d < 3) :
    d + (1 - d) = permanentRows d (genPermanentMatrix d s) 0 := by
  have : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases this with h | h | h <;> subst h <;> rfl

theorem impl_correct : ∀ n, impl n = permanentSpecN n := by
  intro n
  show implAux (permanentDimension n) (permanentSeed n) = _
  simp only [permanentSpecN, permanentSpec]
  generalize permanentDimension n = d
  have hs : permanentSeed n < 2 ^ 32 := by
    show n &&& 0xffffffff < 2 ^ 32
    rw [and32]; exact Nat.mod_lt _ (by decide)
  generalize permanentSeed n = s at hs
  have hlen : (genPermanentMatrix d s).length = d := by simp [genPermanentMatrix]
  rw [hlen]
  by_cases hd : 3 ≤ d
  · have h0 : 3 - d = 0 := by omega
    show Nat.rec (motive := fun _ => Nat) (big d s)
      (fun _ _ => Nat.add d (Nat.sub (nat_lit 1) d)) (3 - d) = _
    rw [h0, matrix_eq]
    exact big_eq d s hd hs
  · have h0 : 3 - d = (2 - d) + 1 := by omega
    show Nat.rec (motive := fun _ => Nat) (big d s)
      (fun _ _ => Nat.add d (Nat.sub (nat_lit 1) d)) (3 - d) = _
    rw [h0]
    exact small_eq d s (by omega)

end Submission
