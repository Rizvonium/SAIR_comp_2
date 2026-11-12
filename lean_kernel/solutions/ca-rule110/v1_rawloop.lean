import Spec

namespace Submission

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


/-- caMix32 with raw kernel primitives. -/
def mixRaw (x : Nat) : Nat :=
  let x := Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x (nat_lit 16))) (nat_lit 2146121005)) (nat_lit 4294967295)
  let x := Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x (nat_lit 15))) (nat_lit 2221713035)) (nat_lit 4294967295)
  Nat.land (Nat.xor x (Nat.shiftRight x (nat_lit 16))) (nat_lit 4294967295)

/-- bit 31 of the mix for cell `i`, as 0/1. -/
def cellBit (seed i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (mixRaw (Nat.add seed (Nat.mul (Nat.add i (nat_lit 1)) (nat_lit 2654435769)))) (nat_lit 31)) (nat_lit 1)

/-- `rowAux seed k` encodes cells `0 … k+1` of the initial row. -/
def rowAux (seed : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (cellBit seed (Nat.add k (nat_lit 2))) (Nat.add k (nat_lit 2)))) k

def impl : Nat → Nat := fun n =>
  biter (Nat.shiftRight n (nat_lit 32)) (rowAux (Nat.land n (nat_lit 4294967295)) (nat_lit 254))

theorem mixRaw_eq (x : Nat) : mixRaw x = caMix32 x := rfl

theorem bit_eq (x : Nat) : Nat.land (Nat.shiftRight x 31) 1 = if x.testBit 31 then 1 else 0 := by
  show (x >>> 31) &&& 1 = _
  rw [Nat.and_one_is_mod]
  have h : x.testBit 31 = ((x >>> 31) % 2 == 1) := by
    simp only [Nat.testBit, Nat.and_comm 1, Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one (x >>> 31) with h | h <;> simp [h]
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one (x >>> 31) with h | h <;> simp [h]

theorem cellBit_eq (seed i : Nat) :
    cellBit seed i = if (caMix32 (seed + (i + 1) * 0x9e3779b9)).testBit 31 then 1 else 0 :=
  bit_eq _

theorem getD_initRowFor (seed j : Nat) : (initRowFor seed).getD j false =
    if j < 256 then (if j = 0 then true else if j = 1 then false
      else (caMix32 (seed + (j + 1) * 0x9e3779b9)).testBit 31) else false := by
  by_cases h : j < 256
  · rw [if_pos h, List.getD_eq_getElem?_getD]; simp [initRowFor, ruleWidth, h]
  · rw [if_neg h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [initRowFor, ruleWidth]; omega)]
    rfl

theorem testBit_rowAux (seed : Nat) : ∀ k j, k ≤ 254 → (rowAux seed k).testBit j =
    if j < k + 2 then (initRowFor seed).getD j false else false := by
  intro k
  induction k with
  | zero =>
    intro j _
    show (1 : Nat).testBit j = _
    rw [getD_initRowFor]
    rcases j with _ | _ | j
    · rfl
    · rfl
    · have h1 : (1 : Nat).testBit (j + 2) = false := Nat.testBit_lt_two_pow (by
        have := Nat.one_lt_two_pow (n := j + 2) (by omega); omega)
      rw [h1]; simp; omega
  | succ k ih =>
    intro j hk
    show (rowAux seed k ||| (cellBit seed (k + 2) <<< (k + 2))).testBit j = _
    rw [Nat.testBit_or, ih j (by omega), Nat.testBit_shiftLeft, cellBit_eq, getD_initRowFor]
    by_cases hj : j < k + 2
    · have : ¬ (j ≥ k + 2) := by omega
      simp [hj, this, show j < k + 1 + 2 by omega]
    · by_cases hj2 : j = k + 2
      · subst hj2
        simp [show k + 2 < 256 by omega]
        split <;> simp_all
      · have h3 : ¬ j < k + 1 + 2 := by omega
        simp only [hj, h3, if_false, Bool.false_or]
        have : j - (k + 2) ≠ 0 := by omega
        have h1 : (1 : Nat).testBit (j - (k + 2)) = false := Nat.testBit_lt_two_pow (by
          have := Nat.one_lt_two_pow (n := j - (k + 2)) this; omega)
        split <;> simp [h1]

theorem rowAux_eq (seed : Nat) : rowAux seed 254 = encodeRow (initRowFor seed) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowAux seed 254 j (by omega), testBit_encodeRow]
  split
  · rfl
  · rw [getD_initRowFor, if_neg (by omega)]

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

theorem impl_correct : ∀ n, impl n = caSpecN n := by
  intro n
  show biter (n >>> 32) (rowAux (n &&& 4294967295) 254) =
    encodeRow (iterRow (caSteps n) (initRowFor (caSeed n)))
  rw [rowAux_eq]
  exact (iter_eq (caSteps n) (initRowFor (caSeed n))
    (by simp [initRowFor, ruleWidth])).symm

end Submission
