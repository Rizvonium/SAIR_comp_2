import Spec

/-!
Rule 110 on a cyclic 256-cell row.

Initial row (no per-cell loop): the 254 hash inputs `seed + (c+1)·φ` (cells `c = 2 … 255`) are
packed into 256 lanes of 64 bits of one natural number, in transposed order (lane `4q+i` holds
cell `q + 64 i + 1`; lanes 0 and 255 are masked off). One division builds the packed
arithmetic progression (exact modulo `2^48`, which is all `caMix32` reads), `caMix32` runs
lane-parallel with a handful of big-number operations, bit 31 of each lane is extracted, and a
single `mod (2^255 - 1)` gathers lane `4q+i` to bit `q + 64 i` (because `2^256 ≡ 2`).

Evolution: the row is tripled (768 bits) and stepped with 5 primitive operations per step;
the middle copy stays exact for up to 256 steps (light cone), so steps run in chunks of 256.
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



theorem P_add (W : Nat) : ∀ (n : Nat) (f g : Nat → Nat), P W f n + P W g n = P W (fun k => f k + g k) n := by
  intro n
  induction n with
  | zero => intro f g; rfl
  | succ n ih =>
    intro f g
    rw [P_succ, P_succ, P_succ, ← ih]
    rw [Nat.mul_add]; omega

theorem P_cmul (W : Nat) (n : Nat) (f : Nat → Nat) (c : Nat) : c * P W f n = P W (fun k => c * f k) n := by
  rw [Nat.mul_comm, P_mul]; congr 1; funext k; exact Nat.mul_comm _ _

theorem P_congr (W n : Nat) (f g : Nat → Nat) (h : ∀ k, k < n → f k = g k) : P W f n = P W g n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [P_succ, P_succ, h 0 (by omega), ih (fun k => f (k + 1)) (fun k => g (k + 1))
      (fun k hk => h (k + 1) (by omega))]

theorem P_append (W : Nat) : ∀ (a b : Nat) (f : Nat → Nat),
    P W f (a + b) = P W f a + 2 ^ (W * a) * P W (fun k => f (a + k)) b := by
  intro a
  induction a with
  | zero => intro b f; simp [P]
  | succ a ih =>
    intro b f
    rw [show a + 1 + b = (a + b) + 1 by omega, P_succ, P_succ, ih]
    have e : (fun k => f (a + 1 + k)) = (fun k => (fun k => f (k + 1)) (a + k)) := by
      funext k; congr 1; omega
    rw [e, Nat.mul_succ, Nat.pow_add]
    grind

/-- Regroup `m*n` lanes of width `W` into `n` super-lanes of width `W*m`. -/
theorem P_regroup (W m : Nat) : ∀ (n : Nat) (g : Nat → Nat),
    P W g (m * n) = P (W * m) (fun q => P W (fun i => g (m * q + i)) m) n := by
  intro n
  induction n with
  | zero => intro g; rfl
  | succ n ih =>
    intro g
    rw [Nat.mul_succ, Nat.add_comm, P_append, ih, P_succ]
    have e : (fun q => P W (fun i => (fun k => g (m + k)) (m * q + i)) m) =
        (fun k => P W (fun i => g (m * (k + 1) + i)) m) := by
      funext q; congr 1; funext i; show g (m + (m * q + i)) = _; congr 1; rw [Nat.mul_succ]; omega
    rw [e]; simp only [Nat.mul_zero, Nat.zero_add]; rw [Nat.add_comm]

theorem P_zero (W : Nat) : ∀ (m : Nat) (F : Nat → Nat), (∀ i, F i = 0) → P W F m = 0 := by
  intro m
  induction m with
  | zero => intro F _; rfl
  | succ m ih => intro F hF; rw [P_succ, ih _ (fun i => hF (i + 1)), hF 0]; rfl

/-- Swap the two levels of a doubly packed number. -/
theorem P_swap (V W : Nat) : ∀ (n m : Nat) (h : Nat → Nat → Nat),
    P V (fun q => P W (fun i => h q i) m) n = P W (fun i => P V (fun q => h q i) n) m := by
  intro n
  induction n with
  | zero =>
    intro m h
    show 0 = _
    exact (P_zero W m _ (fun _ => rfl)).symm
  | succ n ih =>
    intro m h
    rw [P_succ, ih m (fun q i => h (q + 1) i), P_cmul, P_add]
    congr 1; funext i; rw [P_succ]

/-- Generalised lane mask: every mask lane is below `2^t`. -/
theorem P_shift_maskG (W : Nat) (hW : 0 < W) (n : Nat) (f m : Nat → Nat) (hf : ∀ k, f k < 2 ^ W)
    (s t : Nat) (hst : s + t ≤ W) (hm : ∀ k, m k < 2 ^ t) :
    (P W f n >>> s) &&& P W m n = P W (fun k => (f k >>> s) &&& m k) n := by
  have hmW : ∀ k, m k < 2 ^ W := fun k =>
    Nat.lt_of_lt_of_le (hm k) (Nat.pow_le_pow_right (by omega) (by omega))
  apply eq_P W hW n _ (fun k => Nat.and_lt_two_pow _ (hmW k))
  intro k b hb
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_P W n m hmW k b hb, Nat.testBit_and,
    Nat.testBit_shiftRight]
  by_cases hbt : b < t
  · have e : s + (W * k + b) = W * k + (b + s) := by omega
    rw [e, testBit_P W n f hf k (b + s) (by omega)]
    cases decide (k < n) <;> simp [Nat.add_comm s b]
  · have : (m k).testBit b = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hm k) (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this]

theorem P_extend (W n : Nat) (f : Nat → Nat) (h : f n = 0) : P W f (n + 1) = P W f n := by
  rw [P_append W n 1]; simp [P, h]



/-! ## Transposed lanes: 256 lanes of 64 bits

Lane `K = 4q + i` (q < 64, i < 4) carries cell `q + 64 i + 1`; lanes 0 and 255 are masked off.
Since `2^64·4 = 2^256 ≡ 2 (mod 2^255 - 1)`, reducing modulo `2^255 - 1` sends the bit of lane
`4q + i` (at `64(4q+i)`) to position `q + 64 i`. -/

def PHI : Nat := 0x9e3779b9
def C0 : Nat := 281472322274887   -- 2^48 - PHI

/-- Lane contents (exact): `seed + (q + 64 i + 2)·PHI` plus junk at bits ≥ 48. -/
def lv (seed K : Nat) : Nat := seed + (66 + 64 * (K % 4)) * PHI + (64 - K / 4) * C0

def DD : Nat := 0x1000000000000000100000000000000010000000000000001
def KA : Nat := 0x9f73e8ac7200000077e60a3e3200000050582bcff200000028ca4d61b2

theorem DD_eq : DD = P 64 (fun _ => 1) 4 := by decide
theorem KA_eq : KA = P 64 (fun i => (66 + 64 * i) * PHI) 4 := by decide

theorem super_eq (seed q : Nat) :
    (seed * DD + KA) + (64 - q) * (C0 * DD) = P 64 (fun i => lv seed (4 * q + i)) 4 := by
  rw [DD_eq, KA_eq, P_cmul, P_add, P_cmul, P_cmul, P_add]
  apply P_congr
  intro i hi
  simp only [lv]
  have h1 : (4 * q + i) % 4 = i := by omega
  have h2 : (4 * q + i) / 4 = q := by omega
  rw [h1, h2]; simp only [Nat.mul_one]

theorem X_eq2 (seed : Nat) (hs : seed < 2 ^ 32) :
    (((seed * DD + KA) * (2 ^ 256 - 1) + (C0 * DD) * 2 ^ 256) <<< (256 * 64)) /
      ((2 ^ 256 - 1) * (2 ^ 256 - 1)) = P 64 (lv seed) 256 := by
  rw [agp_eq 256 _ _ 64]
  · have hr := P_regroup 64 4 64 (lv seed)
    rw [show 4 * 64 = 256 from rfl] at hr
    rw [hr]
    exact P_congr _ _ _ _ (fun q _ => super_eq seed q)
  · have h1 : seed * DD + KA ≤ (2 ^ 32 - 1) * DD + KA := by
      have := Nat.mul_le_mul_right DD (show seed ≤ 2 ^ 32 - 1 by omega); omega
    have h2 := Nat.mul_le_mul_right (2 ^ 256 - 1) h1
    have h3 : ((2 ^ 32 - 1) * DD + KA) * (2 ^ 256 - 1) + C0 * DD * ((64 + 1) * (2 ^ 256 - 1) + 1)
        < (2 ^ 256 - 1) * (2 ^ 256 - 1) := Nat.lt_of_succ_le (Nat.le_of_ble_eq_true rfl)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_right h2 _) h3

/-! ### Masks: lanes `1 … 254` only -/

def msk1 (K : Nat) : Nat := if 1 ≤ K ∧ K < 255 then 1 else 0

theorem msk1_lt (K : Nat) : msk1 K < 2 := by unfold msk1; split <;> omega

theorem L1_eq : 2 ^ (64 * 255) / (2 ^ 64 - 1) - 1 = P 64 msk1 256 := by
  rw [ones_eq 64 (by omega) 255, P_extend 64 255 msk1 (by simp [msk1]),
    P_succ 64 (fun _ => 1) 254, P_succ 64 msk1 254]
  have : P 64 (fun k => msk1 (k + 1)) 254 = P 64 (fun k => (fun _ => 1) (k + 1)) 254 :=
    P_congr _ _ _ _ (fun k hk => by simp [msk1]; omega)
  rw [this]; simp [msk1]

theorem mk_lt (K : Nat) : msk1 K * M32 < 2 ^ 32 := by
  unfold msk1 M32; split <;> simp

theorem st_xs (f m : Nat → Nat) (hf : ∀ k, f k < 2 ^ 64) (hm : ∀ k, m k < 2 ^ 32) (s : Nat) (hs : s ≤ 32) :
    (P 64 f 256 ^^^ (P 64 f 256 >>> s)) &&& P 64 m 256 =
      P 64 (fun k => (f k &&& m k) ^^^ ((f k >>> s) &&& m k)) 256 := by
  have hd : ∀ a b c : Nat, (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
    intro a b c; apply Nat.eq_of_testBit_eq; intro i; simp
    cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl
  have hm64 : ∀ k, m k < 2 ^ 64 := fun k => Nat.lt_of_lt_of_le (hm k) (by decide)
  rw [hd, P_and 64 (by omega) 256 f m hf hm64, P_shift_maskG 64 (by omega) 256 f m hf s 32 (by omega) hm,
    P_xor 64 (by omega) 256 _ _ (fun k => Nat.and_lt_two_pow _ (hm64 k))
      (fun k => Nat.and_lt_two_pow _ (hm64 k))]

theorem st_mm (f m : Nat → Nat) (c : Nat) (hf : ∀ k, f k * c < 2 ^ 64) (hm : ∀ k, m k < 2 ^ 64) :
    (P 64 f 256 * c) &&& P 64 m 256 = P 64 (fun k => (f k * c) &&& m k) 256 := by
  rw [P_mul, P_and 64 (by omega) 256 _ _ hf hm]

theorem lt_and32 (a b : Nat) (hb : b < 2 ^ 32) : a &&& b < 2 ^ 32 := Nat.and_lt_two_pow _ hb

theorem xor_and32 (a b m : Nat) (hm : m < 2 ^ 32) : (a &&& m) ^^^ (b &&& m) < 2 ^ 32 :=
  Nat.xor_lt_two_pow (lt_and32 _ _ hm) (lt_and32 _ _ hm)

theorem mul32 (a c : Nat) (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) : a * c < 2 ^ 64 := by
  have := Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hc) (by decide : 0 < 2 ^ 32)
  exact Nat.lt_of_lt_of_le this (by decide)

theorem lv_lt (seed K : Nat) (hs : seed < 2 ^ 32) : lv seed K < 2 ^ 64 := by
  unfold lv PHI C0
  have : (64 - K / 4) * 281472322274887 ≤ 64 * 281472322274887 := Nat.mul_le_mul_right _ (by omega)
  have : (66 + 64 * (K % 4)) * 0x9e3779b9 ≤ (66 + 64 * 3) * 0x9e3779b9 :=
    Nat.mul_le_mul_right _ (by have := Nat.mod_lt K (show 4 > 0 by omega); omega)
  omega

/-- Lane-wise value after the whole mixer and the bit extraction. -/
def gl (seed K : Nat) : Nat :=
  ((((((((lv seed K &&& msk1 K * M32) ^^^ ((lv seed K >>> 16) &&& msk1 K * M32)) * 0x7feb352d)
    &&& msk1 K * M32) &&& msk1 K * M32) ^^^
    ((((((lv seed K &&& msk1 K * M32) ^^^ ((lv seed K >>> 16) &&& msk1 K * M32)) * 0x7feb352d)
    &&& msk1 K * M32) >>> 15) &&& msk1 K * M32)) * 0x846ca68b) >>> 31) &&& msk1 K

theorem gl_lt (seed K : Nat) : gl seed K < 2 := by
  unfold gl; exact Nat.and_lt_two_pow (n := 1) _ (msk1_lt K)

/-- Mathematical form of the packed computation (mirrors `initRow`). -/
def rowMath2 (seed : Nat) : Nat :=
  let X := ((((seed * DD + KA) * (2 ^ 256 - 1) + (C0 * DD) * 2 ^ 256)) <<< (256 * 64)) /
      ((2 ^ 256 - 1) * (2 ^ 256 - 1))
  let L1 := (1 <<< (64 * 255)) / (2 ^ 64 - 1) - 1
  let L := L1 * M32
  let Y := (X ^^^ (X >>> 16)) &&& L
  let B := (Y * 0x7feb352d) &&& L
  let D := (B ^^^ (B >>> 15)) &&& L
  let E := D * 0x846ca68b
  let G := (E >>> 31) &&& L1
  ((G % (2 ^ 255 - 1)) <<< 1) ||| 1

theorem gl_zero (seed K : Nat) (h : msk1 K = 0) : gl seed K = 0 := by
  unfold gl; rw [h]; simp

def colS (seed : Nat) : Nat := P 64 (fun i => P 1 (fun q => gl seed (4 * q + i)) 64) 4

theorem testBit_colS (seed j : Nat) :
    (colS seed).testBit j = (decide (j < 256) && (gl seed (4 * (j % 64) + j / 64)).testBit 0) := by
  unfold colS
  have hc : ∀ i, P 1 (fun q => gl seed (4 * q + i)) 64 < 2 ^ 64 := fun i =>
    P_lt 1 64 _ (fun k => gl_lt seed _)
  rw [testBit_P_high 64 (by omega) 4 _ hc]
  have hb := testBit_P 1 64 (fun q => gl seed (4 * q + j / 64)) (fun k => gl_lt seed _) (j % 64) 0 (by omega)
  rw [Nat.one_mul, Nat.add_zero] at hb
  rw [hb]
  have : j % 64 < 64 := Nat.mod_lt _ (by omega)
  by_cases hj : j < 256
  · simp [hj, this, show j / 64 < 4 by omega]
  · simp [hj, show ¬ (j / 64 < 4) by omega]

theorem colS_lt (seed : Nat) : colS seed < 2 ^ 255 - 1 := by
  have h1 : colS seed < 2 ^ 255 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [testBit_colS]
    by_cases h : i < 256
    · have : i = 255 := by omega
      subst this
      rw [gl_zero seed _ (by simp [msk1])]; simp
    · simp [h]
  have h0 : (colS seed).testBit 0 = false := by
    rw [testBit_colS, gl_zero seed _ (by simp [msk1])]; simp
  have h2 : colS seed % 2 = 0 := by
    rw [Nat.testBit_zero] at h0; simpa using h0
  omega

theorem packed2 (seed : Nat) (hs : seed < 2 ^ 32) :
    rowMath2 seed = (colS seed <<< 1) ||| 1 := by
  dsimp only [rowMath2]
  rw [X_eq2 seed hs, Nat.one_shiftLeft, L1_eq, P_mul]
  rw [st_xs _ _ (fun k => lv_lt seed k hs) mk_lt 16 (by omega)]
  rw [st_mm _ _ _ (fun k => mul32 _ _ (xor_and32 _ _ _ (mk_lt k)) (by decide))
    (fun k => Nat.lt_of_lt_of_le (mk_lt k) (by decide))]
  rw [st_xs _ _ (fun k => Nat.lt_of_lt_of_le (lt_and32 _ _ (mk_lt k)) (by decide)) mk_lt 15 (by omega)]
  rw [P_mul, P_shift_maskG 64 (by omega) 256 _ _
    (fun k => mul32 _ _ (xor_and32 _ _ _ (mk_lt k)) (by decide)) 31 1 (by omega) msk1_lt]
  have hr := P_regroup 64 4 64 (gl seed)
  rw [show 4 * 64 = 256 from rfl] at hr
  unfold gl at hr
  rw [hr, P_mod 255 (by omega), P_swap]
  have hlt := colS_lt seed
  unfold colS gl at hlt
  rw [Nat.mod_eq_of_lt hlt]
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

theorem getD_initRowFor (seed j : Nat) : (initRowFor seed).getD j false =
    if j < 256 then (if j = 0 then true else if j = 1 then false
      else (caMix32 (seed + (j + 1) * 0x9e3779b9)).testBit 31) else false := by
  by_cases h : j < 256
  · rw [if_pos h, List.getD_eq_getElem?_getD]; simp [initRowFor, ruleWidth, h]
  · rw [if_neg h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [initRowFor, ruleWidth]; omega)]
    rfl

theorem row_eq2 (seed : Nat) (hs : seed < 2 ^ 32) :
    (colS seed <<< 1) ||| 1 = encodeRow (initRowFor seed) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_encodeRow, getD_initRowFor, Nat.testBit_or, Nat.testBit_shiftLeft]
  rcases j with _ | j
  · simp
  · have h1 : (1 : Nat).testBit (j + 1) = false := Nat.testBit_lt_two_pow (by
      have := Nat.one_lt_two_pow (n := j + 1) (by omega); omega)
    rw [h1, Bool.or_false, Nat.add_sub_cancel, testBit_colS]
    simp only [show j + 1 ≥ 1 by omega, decide_true, Bool.true_and]
    by_cases hj : j + 1 < 256
    · rw [if_pos hj, if_neg (by omega), decide_eq_true (by omega : j < 256), Bool.true_and]
      by_cases h0 : j = 0
      · subst h0; rw [gl_zero seed _ (by simp [msk1])]; simp
      · rw [if_neg (by omega)]
        have hK : msk1 (4 * (j % 64) + j / 64) = 1 := by
          unfold msk1; rw [if_pos]; omega
        have hlv : lv seed (4 * (j % 64) + j / 64) =
            2 ^ 48 * (64 - j % 64) + (seed + (j + 1 + 1) * 0x9e3779b9) := by
          unfold lv PHI C0
          have h1 : (4 * (j % 64) + j / 64) % 4 = j / 64 := by omega
          have h2 : (4 * (j % 64) + j / 64) / 4 = j % 64 := by omega
          rw [h1, h2]; omega
        have hx : seed + (j + 1 + 1) * 0x9e3779b9 < 2 ^ 48 := by omega
        have := lane_bit _ (64 - j % 64) hx
        unfold gl
        rw [hK, Nat.one_mul, hlv]
        unfold r4 r3 r2 r1 at this
        rw [← this]
        simp
    · rw [if_neg hj]
      by_cases h255 : j = 255
      · subst h255; rw [gl_zero seed _ (by simp [msk1])]; simp
      · simp [show ¬ (j < 256) by omega]

/-- The initial row, computed lane-parallel with kernel primitives (same as `rowMath2`). -/
def initRow (seed : Nat) : Nat :=
  let X := Nat.div (Nat.shiftLeft (Nat.add
      (Nat.mul (Nat.add (Nat.mul seed 0x1000000000000000100000000000000010000000000000001)
        0x9f73e8ac7200000077e60a3e3200000050582bcff200000028ca4d61b2)
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
      0xffff61c886470000ffff61c886470000ffff61c886470000ffff61c886470000000000000000000000000000000000000000000000000000000000000000)
      16384)
    0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000001
  let L1 := Nat.sub (Nat.div (Nat.shiftLeft 1 16320) 0xffffffffffffffff) 1
  let L := Nat.mul L1 0xffffffff
  let Y := Nat.land (Nat.xor X (Nat.shiftRight X 16)) L
  let B := Nat.land (Nat.mul Y 0x7feb352d) L
  let D := Nat.land (Nat.xor B (Nat.shiftRight B 15)) L
  let E := Nat.mul D 0x846ca68b
  let G := Nat.land (Nat.shiftRight E 31) L1
  Nat.lor (Nat.shiftLeft (Nat.mod G 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) 1) 1

theorem initRow_eq (seed : Nat) (hs : seed < 2 ^ 32) : initRow seed = encodeRow (initRowFor seed) := by
  rw [← row_eq2 seed hs, ← packed2 seed hs]
  show _ = rowMath2 seed
  unfold rowMath2 DD KA C0 M32
  rfl

/-! ## Evolution on a tripled row

The row is stored three times side by side (768 bits) and evolved with plain shifts (no
wrap-around). After `j ≤ 256` steps the bits in `[j, 768 - j)` still equal the cyclic evolution,
in particular the middle copy `[256, 512)`. -/

theorem length_iterRow : ∀ (k : Nat) (row : List Bool), row.length = 256 → (iterRow k row).length = 256 := by
  intro k
  induction k with
  | zero => intro row h; exact h
  | succ k ih => intro row h; exact ih _ (by rw [length_stepRow, h])

theorem iterRow_add : ∀ (a b : Nat) (row : List Bool), iterRow (a + b) row = iterRow b (iterRow a row) := by
  intro a
  induction a with
  | zero => intro b row; rw [Nat.zero_add]; rfl
  | succ a ih =>
    intro b row
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show iterRow (a + b) (stepRow row) = iterRow b (iterRow a (stepRow row))
    exact ih b _

/-- One Rule 110 step on a bit string (cells beyond the ends read as 0):
`new = (c ^ r) | (c & ~l)` with `a = c ^ r` and `a <<< 1 = l ^ c`. -/
def gfin (E a : Nat) : Nat := Nat.lor a (Nat.land E (Nat.shiftLeft a 1))
def gstep (E : Nat) : Nat := gfin E (Nat.xor E (Nat.shiftRight E 1))

theorem testBit_gstep (E p : Nat) (hp : 1 ≤ p) :
    (gstep E).testBit p = rule110 (E.testBit (p - 1)) (E.testBit p) (E.testBit (p + 1)) := by
  show ((E ^^^ (E >>> 1)) ||| (E &&& ((E ^^^ (E >>> 1)) <<< 1))).testBit p = _
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft, show p ≥ 1 from hp, decide_true, Bool.true_and]
  rw [show 1 + p = p + 1 by omega, show 1 + (p - 1) = p by omega]
  cases E.testBit (p - 1) <;> cases E.testBit p <;> cases E.testBit (p + 1) <;> rfl

/-- Steps in continuation-passing style: `giter (k+1) E = giter k (gstep E)`. -/
def giter (k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun E => E) (fun _ f E => f (gstep E)) k

def Inv (j E : Nat) (row : List Bool) : Prop :=
  ∀ p, j ≤ p → p + j < 768 → E.testBit p = row.getD (p % 256) false

theorem Inv_step (j E : Nat) (row : List Bool) (hlen : row.length = 256) (h : Inv j E row) :
    Inv (j + 1) (gstep E) (stepRow row) := by
  intro p hp1 hp2
  rw [testBit_gstep E p (by omega), h (p - 1) (by omega) (by omega), h p (by omega) (by omega),
    h (p + 1) (by omega) (by omega), getD_stepRow, hlen, if_pos (Nat.mod_lt _ (by omega))]
  congr 2 <;> omega

theorem Inv_giter : ∀ (k j E : Nat) (row : List Bool), row.length = 256 → Inv j E row →
    Inv (j + k) (giter k E) (iterRow k row) := by
  intro k
  induction k with
  | zero => intro j E row _ h; exact h
  | succ k ih =>
    intro j E row hlen h
    have := ih (j + 1) (gstep E) (stepRow row) (by rw [length_stepRow, hlen]) (Inv_step j E row hlen h)
    rw [show j + 1 + k = j + (k + 1) by omega] at this
    exact this

def M256 : Nat := 2 ^ 256 - 1

/-- `k ≤ 256` steps on the tripled row, then read the middle copy. -/
def chunk (k m : Nat) : Nat :=
  Nat.land (Nat.shiftRight (giter k (Nat.lor m (Nat.lor (Nat.shiftLeft m 256) (Nat.shiftLeft m 512)))) 256)
    M256

theorem chunk_eq (k : Nat) (hk : k ≤ 256) (row : List Bool) (hlen : row.length = 256) :
    chunk k (encodeRow row) = encodeRow (iterRow k row) := by
  have hm : encodeRow row < 2 ^ 256 := hlen ▸ encodeRow_lt row
  have h0 : Inv 0 (encodeRow row ||| ((encodeRow row <<< 256) ||| (encodeRow row <<< 512))) row := by
    intro p _ hp
    have hhi : ∀ q, 256 ≤ q → (encodeRow row).testBit q = false := fun q hq =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hq))
    rw [← testBit_encodeRow]
    simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases h1 : p < 256
    · rw [Nat.mod_eq_of_lt h1]; simp [show ¬ p ≥ 256 by omega, show ¬ p ≥ 512 by omega]
    · by_cases h2 : p < 512
      · rw [hhi p (by omega), show p % 256 = p - 256 by omega]
        simp [show p ≥ 256 by omega, show ¬ p ≥ 512 by omega]
      · rw [hhi p (by omega), show p % 256 = p - 512 by omega, hhi (p - 256) (by omega)]
        simp [show p ≥ 256 by omega, show p ≥ 512 by omega]
  have hI := Inv_giter k 0 _ row hlen h0
  rw [Nat.zero_add] at hI
  apply Nat.eq_of_testBit_eq
  intro i
  show ((giter k (encodeRow row ||| ((encodeRow row <<< 256) ||| (encodeRow row <<< 512))) >>> 256) &&& (2 ^ 256 - 1)).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, testBit_encodeRow]
  by_cases hi : i < 256
  · rw [hI (256 + i) (by omega) (by omega), show (256 + i) % 256 = i by omega]; simp [hi]
  · have hl := length_iterRow k row hlen
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp [hi]

/-- Full evolution: chunks of 256 steps, then the remaining `t % 256`. -/
def evolve (t m : Nat) : Nat :=
  chunk (Nat.mod t 256) (Nat.rec (motive := fun _ => Nat) m (fun _ acc => chunk 256 acc) (Nat.div t 256))

theorem evolve_eq (t : Nat) (row : List Bool) (hlen : row.length = 256) :
    evolve t (encodeRow row) = encodeRow (iterRow t row) := by
  have hq : ∀ q, (Nat.rec (motive := fun _ => Nat) (encodeRow row) (fun _ acc => chunk 256 acc) q : Nat)
      = encodeRow (iterRow (256 * q) row) := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
      show chunk 256 _ = _
      rw [ih, chunk_eq 256 (by omega) _ (length_iterRow _ _ hlen), ← iterRow_add]
      congr 1
  show chunk (t % 256) _ = _
  rw [hq, chunk_eq _ (by have := Nat.mod_lt t (show 256 > 0 by omega); omega) _ (length_iterRow _ _ hlen),
    ← iterRow_add, show Nat.div t 256 = t / 256 from rfl, Nat.div_add_mod]

def impl : Nat → Nat := fun n =>
  evolve (Nat.shiftRight n 32) (initRow (Nat.land n 4294967295))

theorem impl_correct : ∀ n, impl n = caSpecN n := by
  intro n
  show evolve (n >>> 32) (initRow (n &&& 4294967295)) =
    encodeRow (iterRow (caSteps n) (initRowFor (caSeed n)))
  have hs : n &&& 4294967295 < 2 ^ 32 := Nat.and_lt_two_pow _ (by decide)
  rw [initRow_eq _ hs]
  exact evolve_eq _ _ (by simp [initRowFor, ruleWidth])

end Submission
