import Spec

/-!
Rule 110 on a cyclic 256-cell row.

Initial row: all 254 hash inputs `seed + (i+1)·φ` (cells 2..255) are packed into 254 lanes of
256 bits of one natural number (one division builds the arithmetic progression, entries taken
modulo 2^48 which is all the mixer reads), `caMix32` runs lane-parallel with ~10 big-number
operations, bit 31 of each lane is extracted, and a single `mod (2^255 - 1)` gathers lane `k`
(at bit 256k) to bit `k` because `2^256 ≡ 2`. Evolution: bit-parallel Rule 110 steps.
-/

namespace Submission


def P (W : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f 0 + 2 ^ W * P W (fun k => f (k + 1)) n

theorem P_succ (W : Nat) (f : Nat → Nat) (n : Nat) :
    P W f (n + 1) = 2 ^ W * P W (fun k => f (k + 1)) n + f 0 := by
  show f 0 + _ = _; omega

theorem P_lt (W : Nat) : ∀ (n : Nat) (f : Nat → Nat), (∀ k, f k < 2 ^ W) → P W f n < 2 ^ (W * n) := by
  intro n
  induction n with
  | zero => intro f _; simp [P]
  | succ n ih =>
    intro f hf
    have h1 := ih (fun k => f (k + 1)) (fun k => hf (k + 1))
    have h0 := hf 0
    rw [P_succ]
    have : 2 ^ (W * (n + 1)) = 2 ^ W * 2 ^ (W * n) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [this]
    have h3 : 2 ^ W * (P W (fun k => f (k + 1)) n + 1) ≤ 2 ^ W * 2 ^ (W * n) :=
      Nat.mul_le_mul_left _ h1
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega

theorem testBit_P (W : Nat) : ∀ (n : Nat) (f : Nat → Nat), (∀ k, f k < 2 ^ W) →
    ∀ k b, b < W → (P W f n).testBit (W * k + b) = (decide (k < n) && (f k).testBit b) := by
  intro n
  induction n with
  | zero => intro f _ k b _; simp [P]
  | succ n ih =>
    intro f hf k b hb
    rw [P_succ, Nat.testBit_two_pow_mul_add _ (hf 0)]
    cases k with
    | zero => simp [hb]
    | succ k =>
      have h1 : ¬ (W * (k + 1) + b < W) := by
        have : W ≤ W * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have h2 : W * (k + 1) + b - W = W * k + b := by
        rw [Nat.mul_succ]; omega
      rw [if_neg h1, h2, ih _ (fun k => hf (k + 1)) k b hb]
      simp

theorem testBit_P_high (W : Nat) (hW : 0 < W) (n : Nat) (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ W)
    (j : Nat) : (P W f n).testBit j = (decide (j / W < n) && (f (j / W)).testBit (j % W)) := by
  have := testBit_P W n f hf (j / W) (j % W) (Nat.mod_lt _ hW)
  rwa [Nat.div_add_mod] at this

theorem eq_P (W : Nat) (hW : 0 < W) (n : Nat) (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ W) (N : Nat)
    (h : ∀ k b, b < W → N.testBit (W * k + b) = (decide (k < n) && (f k).testBit b)) :
    N = P W f n := by
  apply Nat.eq_of_testBit_eq
  intro j
  have e := h (j / W) (j % W) (Nat.mod_lt _ hW)
  rw [Nat.div_add_mod] at e
  rw [e, testBit_P_high W hW n f hf]

theorem P_mul (W : Nat) : ∀ (n : Nat) (f : Nat → Nat) (c : Nat),
    P W f n * c = P W (fun k => f k * c) n := by
  intro n
  induction n with
  | zero => intro f c; simp [P]
  | succ n ih =>
    intro f c
    rw [P_succ, P_succ, ← ih]
    rw [Nat.add_mul, Nat.mul_assoc]

theorem P_and (W : Nat) (hW : 0 < W) (n : Nat) (f g : Nat → Nat) (hf : ∀ k, f k < 2 ^ W)
    (hg : ∀ k, g k < 2 ^ W) : P W f n &&& P W g n = P W (fun k => f k &&& g k) n := by
  apply eq_P W hW n _ (fun k => Nat.and_lt_two_pow _ (hg k))
  intro k b hb
  rw [Nat.testBit_and, testBit_P W n f hf k b hb, testBit_P W n g hg k b hb, Nat.testBit_and]
  cases decide (k < n) <;> simp

theorem P_xor (W : Nat) (hW : 0 < W) (n : Nat) (f g : Nat → Nat) (hf : ∀ k, f k < 2 ^ W)
    (hg : ∀ k, g k < 2 ^ W) : P W f n ^^^ P W g n = P W (fun k => f k ^^^ g k) n := by
  apply eq_P W hW n _ (fun k => Nat.xor_lt_two_pow (hf k) (hg k))
  intro k b hb
  rw [Nat.testBit_xor, testBit_P W n f hf k b hb, testBit_P W n g hg k b hb, Nat.testBit_xor]
  cases decide (k < n) <;> simp

/-- Shift right inside lanes, then keep the low `t` bits of every lane (no cross-lane leakage). -/
theorem P_shift_mask (W : Nat) (hW : 0 < W) (n : Nat) (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ W)
    (s t : Nat) (hst : s + t ≤ W) :
    (P W f n >>> s) &&& P W (fun _ => 2 ^ t - 1) n = P W (fun k => (f k >>> s) &&& (2 ^ t - 1)) n := by
  have ht : 2 ^ t - 1 < 2 ^ W := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show t ≤ W by omega)
    have := Nat.one_le_two_pow (n := t); omega
  apply eq_P W hW n _ (fun k => Nat.and_lt_two_pow _ ht)
  intro k b hb
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_P W n _ (fun _ => ht) k b hb,
    Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hbt : b < t
  · have e : s + (W * k + b) = W * k + (b + s) := by omega
    rw [e, testBit_P W n f hf k (b + s) (by omega)]
    cases decide (k < n) <;> simp [hbt, Nat.add_comm s b]
  · simp [hbt]

/-- Ones in the low bit of every lane: `R^n / (R-1)`. -/
theorem P_ones (W : Nat) : ∀ n, 2 ^ (W * n) = (2 ^ W - 1) * P W (fun _ => 1) n + 1 := by
  intro n
  induction n with
  | zero => simp [P]
  | succ n ih =>
    rw [P_succ, Nat.mul_succ, Nat.pow_add, ih]
    have h1 : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    generalize 2 ^ W = R at *
    generalize P W (fun _ => 1) n = Q
    obtain ⟨S, rfl⟩ : ∃ S, R = S + 1 := ⟨R - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    grind

theorem ones_eq (W : Nat) (hW : 2 ≤ W) (n : Nat) :
    2 ^ (W * n) / (2 ^ W - 1) = P W (fun _ => 1) n := by
  have h1 : 4 ≤ 2 ^ W := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) hW; simpa using this
  rw [P_ones W n, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]

/-- Descending arithmetic-progression lanes from one division (floor trick). -/
theorem P_agp (W : Nat) (A c : Nat) : ∀ n,
    2 ^ (W * n) * (A * (2 ^ W - 1) + c * 2 ^ W) =
      (2 ^ W - 1) * (2 ^ W - 1) * P W (fun m => A + (n - m) * c) n
        + (A * (2 ^ W - 1) + c * ((n + 1) * (2 ^ W - 1) + 1)) := by
  intro n
  have h1 : 1 ≤ 2 ^ W := Nat.one_le_two_pow
  induction n with
  | zero =>
    simp [P]
    obtain ⟨S, hS⟩ : ∃ S, 2 ^ W = S + 1 := ⟨2 ^ W - 1, by omega⟩
    rw [hS]; simp
  | succ n ih =>
    rw [P_succ]
    have e : (fun k => A + (n + 1 - (k + 1)) * c) = (fun m => A + (n - m) * c) := by
      funext k; congr 2; omega
    rw [e, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (W * n)) (2 ^ W), Nat.mul_assoc, ih]
    generalize P W (fun m => A + (n - m) * c) n = Q
    obtain ⟨S, hS⟩ : ∃ S, 2 ^ W = S + 1 := ⟨2 ^ W - 1, by omega⟩
    rw [hS, Nat.add_sub_cancel, Nat.sub_zero]
    grind

theorem agp_eq (W : Nat) (A c n : Nat)
    (hsmall : A * (2 ^ W - 1) + c * ((n + 1) * (2 ^ W - 1) + 1) < (2 ^ W - 1) * (2 ^ W - 1)) :
    ((A * (2 ^ W - 1) + c * 2 ^ W) <<< (W * n)) / ((2 ^ W - 1) * (2 ^ W - 1)) =
      P W (fun m => A + (n - m) * c) n := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm _ (2 ^ (W * n)), P_agp, Nat.mul_add_div (by omega),
    Nat.div_eq_of_lt hsmall, Nat.add_zero]

/-- Lanes of width `W` reduce modulo `2^(W-1) - 1` to a base-2 number. -/
theorem P_mod (V : Nat) (hV : 0 < V) : ∀ (n : Nat) (g : Nat → Nat),
    P (V + 1) g n % (2 ^ V - 1) = P 1 g n % (2 ^ V - 1) := by
  intro n
  have h1 : 2 ≤ 2 ^ V := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) hV; simpa using this
  have hR : 2 ^ (V + 1) = 2 * (2 ^ V - 1) + 2 := by rw [Nat.pow_succ]; omega
  induction n with
  | zero => intro g; rfl
  | succ n ih =>
    intro g
    rw [P_succ, P_succ, Nat.add_mod, Nat.mul_mod, ih, ← Nat.mul_mod, hR]
    rw [Nat.add_mod (2 ^ 1 * _), Nat.mul_mod (2 * (2 ^ V - 1) + 2)]
    simp



/-! ## Per-lane facts -/

/-- Low 48 bits decide everything the mixer's first round looks at. -/
theorem testBit_junk (x j i : Nat) (hx : x < 2 ^ 48) (hi : i < 48) :
    (2 ^ 48 * j + x).testBit i = x.testBit i := by
  rw [Nat.testBit_two_pow_mul_add _ hx, if_pos hi]

theorem round1 (x j : Nat) (hx : x < 2 ^ 48) :
    ((2 ^ 48 * j + x) &&& (2 ^ 32 - 1)) ^^^ (((2 ^ 48 * j + x) >>> 16) &&& (2 ^ 32 - 1)) =
      (x ^^^ (x >>> 16)) % 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow]
  by_cases hi : i < 32
  · rw [testBit_junk x j i hx (by omega), testBit_junk x j (16 + i) hx (by omega)]
    simp [hi]
  · simp [hi]

theorem round2 (b : Nat) :
    (b &&& (2 ^ 32 - 1)) ^^^ ((b >>> 15) &&& (2 ^ 32 - 1)) = (b ^^^ (b >>> 15)) % 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow]
  by_cases hi : i < 32 <;> simp [hi]

theorem testBit31_mod (a : Nat) : a.testBit 31 = (a % 2 ^ 32).testBit 31 := by
  rw [Nat.testBit_mod_two_pow]; simp

theorem caMix32_bit (x : Nat) : (caMix32 x).testBit 31 =
    ((((x ^^^ (x >>> 16)) * 0x7feb352d % 2 ^ 32) ^^^ (((x ^^^ (x >>> 16)) * 0x7feb352d % 2 ^ 32) >>> 15))
      * 0x846ca68b).testBit 31 := by
  have h32 : (0xffffffff : Nat) = 2 ^ 32 - 1 := rfl
  simp only [caMix32, h32, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow,
    Nat.testBit_xor, Nat.testBit_shiftRight]
  simp

/-! Lane-wise stages of the mixer (each is what one SIMD stage does to one lane). -/
def M32 : Nat := 2 ^ 32 - 1
def r1 (v : Nat) : Nat := (v &&& M32) ^^^ ((v >>> 16) &&& M32)
def r2 (y : Nat) : Nat := (y * 0x7feb352d) &&& M32
def r3 (b : Nat) : Nat := (b &&& M32) ^^^ ((b >>> 15) &&& M32)
def r4 (d : Nat) : Nat := d * 0x846ca68b

/-- The lane computation agrees with bit 31 of `caMix32` on the true input `x`. -/
theorem lane_bit (x j : Nat) (hx : x < 2 ^ 48) :
    (r4 (r3 (r2 (r1 (2 ^ 48 * j + x))))).testBit 31 = (caMix32 x).testBit 31 := by
  unfold r4 r3 r2 r1 M32
  rw [round1 x j hx, round2, caMix32_bit, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mul_mod,
    testBit31_mod, Nat.mod_mul_mod, ← testBit31_mod]



/-! ## SIMD stages on 254 lanes of 256 bits -/

def ONES : Nat := P 256 (fun _ => 1) 254
def L32 : Nat := P 256 (fun _ => M32) 254

theorem M32_lt : M32 < 2 ^ 256 := by unfold M32; decide

theorem L32_eq : ONES * 4294967295 = L32 := by
  unfold ONES L32; rw [P_mul]; rfl

theorem stage_xs (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ 256) (s : Nat) (hs : s ≤ 224) :
    (P 256 f 254 ^^^ (P 256 f 254 >>> s)) &&& L32 =
      P 256 (fun k => (f k &&& M32) ^^^ ((f k >>> s) &&& M32)) 254 := by
  have hd : ∀ a b c : Nat, (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
    intro a b c; apply Nat.eq_of_testBit_eq; intro i; simp; cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl
  rw [hd, L32, P_and 256 (by omega) 254 f _ hf (fun _ => M32_lt)]
  have := P_shift_mask 256 (by omega) 254 f hf s 32 (by omega)
  have M32d : M32 = 2 ^ 32 - 1 := rfl
  rw [← M32d] at this
  rw [this, P_xor 256 (by omega) 254 _ _ (fun k => Nat.and_lt_two_pow _ M32_lt)
    (fun k => Nat.and_lt_two_pow _ M32_lt)]

theorem stage_mm (f : Nat → Nat) (c : Nat) (hf : ∀ k, f k * c < 2 ^ 256) :
    (P 256 f 254 * c) &&& L32 = P 256 (fun k => (f k * c) &&& M32) 254 := by
  rw [P_mul, L32, P_and 256 (by omega) 254 _ _ hf (fun _ => M32_lt)]

theorem stage_ex (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ 256) :
    (P 256 f 254 >>> 31) &&& ONES = P 256 (fun k => (f k >>> 31) &&& 1) 254 := by
  have := P_shift_mask 256 (by omega) 254 f hf 31 1 (by omega)
  exact this

theorem lt32_and (a : Nat) : a &&& M32 < 2 ^ 32 := by
  unfold M32; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by decide)

theorem r1_lt (v : Nat) : r1 v < 2 ^ 32 := Nat.xor_lt_two_pow (lt32_and _) (lt32_and _)
theorem r2_lt (v : Nat) : r2 v < 2 ^ 32 := lt32_and _
theorem r3_lt (v : Nat) : r3 v < 2 ^ 32 := Nat.xor_lt_two_pow (lt32_and _) (lt32_and _)

/-! ## The initial row -/

def PHI : Nat := 0x9e3779b9
/-- `2^48 - PHI`: adding it is subtracting `PHI` modulo `2^48`. -/
def CNEG : Nat := 281472322274887

def lane (seed m : Nat) : Nat := (seed + 257 * PHI) + (254 - m) * CNEG

def gbit (seed k : Nat) : Nat := (r4 (r3 (r2 (r1 (lane seed k)))) >>> 31) &&& 1

/-- Mathematical form of the packed computation. -/
def rowMath (seed : Nat) : Nat :=
  let R1 := (1 <<< 256) - 1
  let X := ((((seed + 682189992633) * R1) + (CNEG <<< 256)) <<< 65024) / (R1 * R1)
  let ONES' := (1 <<< 65024) / R1
  let L := ONES' * 4294967295
  let Y := (X ^^^ (X >>> 16)) &&& L
  let B := (Y * 2146121005) &&& L
  let D := (B ^^^ (B >>> 15)) &&& L
  let E := D * 2221713035
  let G := (E >>> 31) &&& ONES'
  ((G % ((1 <<< 255) - 1)) <<< 2) ||| 1

theorem lane_lt (seed m : Nat) (hs : seed < 2 ^ 32) : lane seed m < 2 ^ 256 := by
  unfold lane PHI CNEG
  have : (254 - m) * 281472322274887 ≤ 254 * 281472322274887 := Nat.mul_le_mul_right _ (by omega)
  omega

theorem lane_eq (seed m : Nat) (hm : m < 254) :
    lane seed m = 2 ^ 48 * (254 - m) + (seed + (m + 2 + 1) * 0x9e3779b9) := by
  unfold lane PHI CNEG; omega

theorem X_eq (seed : Nat) (hs : seed < 2 ^ 32) :
    ((((seed + 682189992633) * ((1 <<< 256) - 1)) + (CNEG <<< 256)) <<< 65024) /
      (((1 <<< 256) - 1) * ((1 <<< 256) - 1)) = P 256 (lane seed) 254 := by
  have := agp_eq 256 (seed + 682189992633) CNEG 254 (by unfold CNEG; omega)
  rw [Nat.one_shiftLeft, Nat.shiftLeft_eq CNEG 256]
  rw [show (65024 : Nat) = 256 * 254 from rfl, this]
  rfl

theorem ONES_eq : (1 <<< 65024) / ((1 <<< 256) - 1) = ONES := by
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft, show (65024 : Nat) = 256 * 254 from rfl,
    ones_eq 256 (by omega) 254]; rfl

theorem gbit_lt (seed k : Nat) : gbit seed k < 2 := by
  unfold gbit; rw [Nat.and_one_is_mod]; exact Nat.mod_lt _ (by omega)

theorem packed_eq (seed : Nat) (hs : seed < 2 ^ 32) :
    rowMath seed = ((P 1 (gbit seed) 254) <<< 2) ||| 1 := by
  dsimp only [rowMath]
  rw [X_eq seed hs, ONES_eq, L32_eq]
  rw [stage_xs (lane seed) (fun k => lane_lt seed k hs) 16 (by omega)]
  have h1 : ∀ k, (lane seed k &&& M32 ^^^ lane seed k >>> 16 &&& M32) * 2146121005 < 2 ^ 256 := by
    intro k
    have := r1_lt (lane seed k)
    unfold r1 at this
    have : (lane seed k &&& M32 ^^^ lane seed k >>> 16 &&& M32) * 2146121005 < 2 ^ 32 * 2146121005 :=
      Nat.mul_lt_mul_of_pos_right this (by decide)
    exact Nat.lt_of_lt_of_le this (by decide)
  rw [stage_mm _ _ h1]
  rw [stage_xs _ (fun k => Nat.lt_of_lt_of_le (lt32_and _) (by decide)) 15 (by omega)]
  rw [P_mul]
  have h2 : ∀ k, r4 (r3 (r2 (r1 (lane seed k)))) < 2 ^ 256 := by
    intro k
    have := r3_lt (r2 (r1 (lane seed k)))
    unfold r4
    have : r3 (r2 (r1 (lane seed k))) * 2221713035 < 2 ^ 32 * 2221713035 :=
      Nat.mul_lt_mul_of_pos_right this (by decide)
    exact Nat.lt_of_lt_of_le this (by decide)
  have e := stage_ex _ h2
  unfold r4 r3 r2 r1 at e
  rw [e]
  have hg := P_mod 255 (by omega) 254 (gbit seed)
  have hlt : P 1 (gbit seed) 254 < 2 ^ 255 - 1 := by
    have := P_lt 1 254 (gbit seed) (fun k => gbit_lt seed k)
    exact Nat.lt_of_lt_of_le this (by decide)
  unfold gbit r4 r3 r2 r1 at hg hlt
  rw [Nat.one_shiftLeft, hg, Nat.mod_eq_of_lt hlt]
  rfl



theorem testBit_encodeRow (row : List Bool) (i : Nat) :
    (encodeRow row).testBit i = row.getD i false := by
  induction row generalizing i with
  | nil => simp [encodeRow]
  | cons b bs ih =>
    have hrec : encodeRow (b :: bs) = 2 * encodeRow bs + (if b then 1 else 0) := rfl
    cases i with
    | zero => rw [hrec]; cases b <;> simp [Nat.testBit_zero] <;> omega
    | succ j =>
      rw [hrec, Nat.testBit_succ]
      have : (2 * encodeRow bs + (if b then 1 else 0)) / 2 = encodeRow bs := by
        cases b <;> simp <;> omega
      rw [this, ih]; rfl

theorem encodeRow_lt (row : List Bool) : encodeRow row < 2 ^ row.length := by
  induction row with
  | nil => simp [encodeRow]
  | cons b bs ih =>
    have hrec : encodeRow (b :: bs) = 2 * encodeRow bs + (if b then 1 else 0) := rfl
    rw [hrec, List.length_cons, Nat.pow_succ]; split <;> omega

@[simp] theorem length_stepRow (row : List Bool) : (stepRow row).length = row.length := by
  simp [stepRow]

theorem getD_stepRow (row : List Bool) (i : Nat) :
    (stepRow row).getD i false =
      if i < row.length then
        rule110 (row.getD ((i + row.length - 1) % row.length) false)
                (row.getD i false) (row.getD ((i + 1) % row.length) false)
      else false := by
  by_cases h : i < row.length
  · rw [List.getD_eq_getElem?_getD]; simp [stepRow, h]
  · have hlen : (stepRow row).length ≤ i := by rw [length_stepRow]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, Option.getD_none, if_neg h]

def M : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
theorem M_eq : M = 2 ^ 256 - 1 := by decide
theorem testBit_M (i : Nat) : M.testBit i = decide (i < 256) := by
  rw [M_eq, Nat.testBit_two_pow_sub_one]
theorem testBit_high {m : Nat} (hm : m < 2 ^ 256) {j : Nat} (hj : 256 ≤ j) : m.testBit j = false := by
  have hlt : m < 2 ^ j := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hj)
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]

theorem testBit_rotL {m : Nat} (hm : m < 2 ^ 256) {i : Nat} (hi : i < 256) :
    (((m <<< 1) ||| (m >>> 255)) &&& M).testBit i = m.testBit ((i + 255) % 256) := by
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, testBit_M]
  simp only [hi, decide_true, Bool.and_true]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0; simp
  · have h1 : (1 ≤ i) := hipos
    have hmod : (i + 255) % 256 = i - 1 := by omega
    have hhi : m.testBit (255 + i) = false := testBit_high hm (by omega)
    simp [h1, hmod, hhi]

theorem testBit_rotR {m : Nat} (hm : m < 2 ^ 256) {i : Nat} (hi : i < 256) :
    (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M).testBit i = m.testBit ((i + 1) % 256) := by
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, testBit_M]
  simp only [hi, decide_true, Bool.and_true]
  by_cases h255 : i = 255
  · subst h255
    have hmod : (255 + 1) % 256 = 0 := by decide
    have hhi : m.testBit (1 + 255) = false := testBit_high hm (by omega)
    rw [hmod]; simp [hhi]
  · have hmod : (i + 1) % 256 = i + 1 := by omega
    have hnot : ¬ (255 ≤ i) := by omega
    simp [hmod, hnot, Nat.add_comm 1 i]

def bstep (m : Nat) : Nat :=
  (M ^^^ (((M ^^^ m) &&& (M ^^^ (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M)))
          ||| ((((m <<< 1) ||| (m >>> 255)) &&& M) &&& m &&& (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M)))) &&& M

def biter : Nat → Nat → Nat
  | 0, m => m
  | t + 1, m => biter t (bstep m)


theorem getD_initRowFor (seed j : Nat) : (initRowFor seed).getD j false =
    if j < 256 then (if j = 0 then true else if j = 1 then false
      else (caMix32 (seed + (j + 1) * 0x9e3779b9)).testBit 31) else false := by
  by_cases h : j < 256
  · rw [if_pos h, List.getD_eq_getElem?_getD]; simp [initRowFor, ruleWidth, h]
  · rw [if_neg h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [initRowFor, ruleWidth]; omega)]
    rfl

theorem step_eq {row : List Bool} (hlen : row.length = 256) :
    encodeRow (stepRow row) = bstep (encodeRow row) := by
  have hm : encodeRow row < 2 ^ 256 := hlen ▸ encodeRow_lt row
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_encodeRow, getD_stepRow, hlen]
  by_cases hi : i < 256
  · rw [if_pos hi]
    have he : i + 256 - 1 = i + 255 := by omega
    rw [he]
    simp only [bstep, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, testBit_M,
               testBit_rotL hm hi, testBit_rotR hm hi, testBit_encodeRow, hi, decide_true]
    generalize row.getD ((i + 255) % 256) false = a
    generalize row.getD i false = b
    generalize row.getD ((i + 1) % 256) false = c
    cases a <;> cases b <;> cases c <;> decide
  · rw [if_neg hi]
    unfold bstep
    rw [Nat.testBit_and, testBit_M, decide_eq_false hi, Bool.and_false]

theorem iter_eq : ∀ (n : Nat) (row : List Bool), row.length = 256 →
    encodeRow (iterRow n row) = biter n (encodeRow row) := by
  intro n
  induction n with
  | zero => intro row _; rfl
  | succ k ih =>
    intro row hlen
    show encodeRow (iterRow k (stepRow row)) = biter k (bstep (encodeRow row))
    rw [ih (stepRow row) (by rw [length_stepRow, hlen]), step_eq hlen]


theorem row_eq (seed : Nat) (hs : seed < 2 ^ 32) :
    ((P 1 (gbit seed) 254) <<< 2) ||| 1 = encodeRow (initRowFor seed) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_encodeRow, getD_initRowFor, Nat.testBit_or, Nat.testBit_shiftLeft]
  rcases j with _ | _ | i
  · simp
  · simp; rfl
  · have hb := testBit_P 1 254 (gbit seed) (fun k => gbit_lt seed k) i 0 (by omega)
    rw [Nat.one_mul, Nat.add_zero] at hb
    have e : i + 1 + 1 - 2 = i := by omega
    simp only [show 2 ≤ i + 1 + 1 by omega, decide_true, Bool.true_and, e, hb]
    have h1 : (1 : Nat).testBit (i + 1 + 1) = false := Nat.testBit_lt_two_pow (by
      have := Nat.one_lt_two_pow (n := i + 1 + 1) (by omega); omega)
    rw [h1, Bool.or_false]
    by_cases hi : i < 254
    · have hx : seed + (i + 2 + 1) * 0x9e3779b9 < 2 ^ 48 := by omega
      unfold gbit
      rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_zero, lane_eq seed i hi, lane_bit _ _ hx]
      simp [hi, show i + 1 + 1 < 256 by omega]
    · simp [hi, show ¬ (i + 1 + 1 < 256) by omega]

/-- The initial row, computed lane-parallel with kernel primitives (same as `rowMath`). -/
def initRow (seed : Nat) : Nat :=
  let R1 := Nat.sub (Nat.shiftLeft 1 256) 1
  let X := Nat.div (Nat.shiftLeft (Nat.add (Nat.mul (Nat.add seed 682189992633) R1)
    (Nat.shiftLeft 281472322274887 256)) 65024) (Nat.mul R1 R1)
  let ONES' := Nat.div (Nat.shiftLeft 1 65024) R1
  let L := Nat.mul ONES' 4294967295
  let Y := Nat.land (Nat.xor X (Nat.shiftRight X 16)) L
  let B := Nat.land (Nat.mul Y 2146121005) L
  let D := Nat.land (Nat.xor B (Nat.shiftRight B 15)) L
  let E := Nat.mul D 2221713035
  let G := Nat.land (Nat.shiftRight E 31) ONES'
  Nat.lor (Nat.shiftLeft (Nat.mod G (Nat.sub (Nat.shiftLeft 1 255) 1)) 2) 1

theorem initRow_eq (seed : Nat) (hs : seed < 2 ^ 32) : initRow seed = encodeRow (initRowFor seed) := by
  rw [← row_eq seed hs, ← packed_eq seed hs]; rfl

def impl : Nat → Nat := fun n =>
  biter (Nat.shiftRight n 32) (initRow (Nat.land n 4294967295))

theorem impl_correct : ∀ n, impl n = caSpecN n := by
  intro n
  show biter (n >>> 32) (initRow (n &&& 4294967295)) =
    encodeRow (iterRow (caSteps n) (initRowFor (caSeed n)))
  have hs : n &&& 4294967295 < 2 ^ 32 := Nat.and_lt_two_pow _ (by decide)
  rw [initRow_eq _ hs]
  exact (iter_eq (caSteps n) (initRowFor (caSeed n))
    (by simp [initRowFor, ruleWidth])).symm

end Submission
