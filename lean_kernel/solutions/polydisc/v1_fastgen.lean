import Spec

/-!
# polydisc v1: fast coefficient generator

The polynomial generator of the specification is re-implemented with raw kernel
primitives (`Nat.add/mul/mod/shiftLeft/shiftRight/pow`, `nat_lit` numerals,
`Nat.rec` loops, `Bool.casesOn` selections). Coefficients are produced with an
offset `Ω = 2^(k-1)` (so they are naturals) and decoded by `dec`. The
discriminant itself is still computed by the specification's own algorithm.
-/

namespace Submission

/-! ## Offset representation -/

/-- Decode a list of naturals stored with offset `Ω`. -/
def dec (Ω : Nat) (L : List Nat) : List Int := L.map (fun (X : Nat) => (X : Int) - (Ω : Int))

/-! ## Generator, written with raw primitives -/

def lcgStep (s : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (nat_lit 6364136223846793005) s) (nat_lit 1442695040888963407))
    (nat_lit 18446744073709551616)

def seedF (n : Nat) : Nat := lcgStep (Nat.add n (nat_lit 1))

def kbitsF (n : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble (nat_lit 67108864) n) (nat_lit 15)
   (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (nat_lit 68719476736) n) (nat_lit 36)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (nat_lit 70368744177664) n) (nat_lit 205)
     (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (nat_lit 72057594037927936) n) (nat_lit 1001)
       (nat_lit 3484))))

def clampF (k w : Nat) : Nat :=
  let w2 := Bool.casesOn (motive := fun _ => Nat) (Nat.ble (nat_lit 2) w) (nat_lit 2) w
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble k w2) w2 k

def widthF (k i : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble k (nat_lit 64))
    (clampF k (Nat.add (nat_lit 3) (Nat.div (Nat.sub (Nat.add (Nat.mul (Nat.sub k (nat_lit 3))
        (Nat.sub (Nat.mul (nat_lit 2448) i) (Nat.mul (Nat.mul (nat_lit 2) i) i))) (nat_lit 57600))
        (nat_lit 1)) (nat_lit 57600))))
    (clampF k (Nat.add (Nat.div (Nat.mul (nat_lit 2) (Nat.sub (nat_lit 36) k)) (nat_lit 7))
      (Nat.div (Nat.mul (Nat.sub k (Nat.div (Nat.mul (nat_lit 2) (Nat.sub (nat_lit 36) k)) (nat_lit 7))) i)
        (Nat.add (nat_lit 10) (Nat.div (Nat.mul (nat_lit 2) (Nat.sub (nat_lit 36) k)) (nat_lit 7))))))

/-- Advance the generator `words` times, adding each new state shifted into `acc`;
then continue with `k word finalState`. -/
def wordLoop {R : Type} (k : Nat → Nat → R) (words : Nat) : Nat → Nat → Nat → R :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → R)
    (fun state acc _ => k acc state)
    (fun _ ih state acc shift =>
       let s' := lcgStep state
       ih s' (Nat.add acc (Nat.shiftLeft s' shift)) (Nat.add shift (nat_lit 64))) words

/-- The centred nonzero coefficient of width `w`, stored with offset `Ω`. -/
def coeffOff (Ω w words word : Nat) : Nat :=
  let top := Nat.shiftRight word (Nat.sub (Nat.mul (nat_lit 64) words) w)
  let half := Nat.pow (nat_lit 2) (Nat.sub w (nat_lit 1))
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq top half)
    (Nat.sub (Nat.add top Ω) half) (Nat.add Ω (nat_lit 1))

def coeffsLoop (K Ω : Nat) (count : Nat) : Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat)
    (fun _ _ => [])
    (fun _ ih index state =>
      let w := widthF K index
      let words := Nat.div (Nat.add w (nat_lit 63)) (nat_lit 64)
      wordLoop (fun word state' => coeffOff Ω w words word :: ih (Nat.add index (nat_lit 1)) state')
        words state (nat_lit 0) (nat_lit 0))
    count

/-- The generated polynomial, coefficients stored with offset `2^(K-1)`. -/
def genOff (n : Nat) : List Nat :=
  let K := kbitsF n
  let Ω := Nat.pow (nat_lit 2) (Nat.sub K (nat_lit 1))
  Nat.add Ω (nat_lit 1) :: coeffsLoop K Ω (nat_lit 24) (nat_lit 1) (seedF n)

/-! ## Proofs: generator -/

theorem lcgStep_eq (s : Nat) : lcgStep s = lcgNext s := rfl
theorem seedF_eq (n : Nat) : seedF n = lcgSeed n := rfl

/-- Selection on a Boolean, as written with `Bool.casesOn`. -/
theorem bcases_eq {α : Sort _} (b : Bool) (x y : α) :
    Bool.casesOn (motive := fun _ => α) b x y = if b = true then y else x := by
  cases b <;> rfl

theorem ble_true (a b : Nat) : (Nat.ble a b = true) ↔ a ≤ b := by simp [Nat.ble_eq]
theorem beq_true (a b : Nat) : (Nat.beq a b = true) ↔ a = b := by
  constructor
  · exact Nat.eq_of_beq_eq_true
  · intro h; subst h; exact Nat.beq_refl a

theorem kbitsF_eq (n : Nat) : kbitsF n = kbitsOf n := by
  unfold kbitsF kbitsOf difficultyLevel
  simp only [bcases_eq, ble_true]
  by_cases h1 : n < 67108864
  · simp [h1, show ¬ 67108864 ≤ n by omega]
  · by_cases h2 : n < 68719476736
    · simp [h1, h2, show 67108864 ≤ n by omega, show ¬ 68719476736 ≤ n by omega]
    · by_cases h3 : n < 70368744177664
      · simp [h1, h2, h3, show 67108864 ≤ n by omega, show 68719476736 ≤ n by omega,
          show ¬ 70368744177664 ≤ n by omega]
      · by_cases h4 : n < 72057594037927936
        · simp [h1, h2, h3, h4, show 67108864 ≤ n by omega, show 68719476736 ≤ n by omega,
            show 70368744177664 ≤ n by omega, show ¬ 72057594037927936 ≤ n by omega]
        · simp [h1, h2, h3, h4, show 67108864 ≤ n by omega, show 68719476736 ≤ n by omega,
            show 70368744177664 ≤ n by omega, show 72057594037927936 ≤ n by omega]

theorem clampF_eq (k w : Nat) : clampF k w = clampWidth k w := by
  unfold clampF clampWidth
  simp only [bcases_eq, ble_true, Nat.min_def, Nat.max_def]
  repeat' split
  all_goals omega

theorem widthF_eq (k i : Nat) : widthF k i = coefficientWidth k i := by
  unfold widthF coefficientWidth
  simp only [bcases_eq, ble_true, clampF_eq]
  by_cases h : k ≤ 64
  · simp only [h, if_true]; rfl
  · simp only [h, if_false]
    congr 2

theorem cCW_succ (w shift state : Nat) :
    collectCoeffWord (w + 1) shift state =
      (lcgNext state * 2 ^ shift + (collectCoeffWord w (shift + 64) (lcgNext state)).1,
       (collectCoeffWord w (shift + 64) (lcgNext state)).2) := by
  rw [collectCoeffWord.eq_2]

theorem wordLoop_eq {R : Type} (k : Nat → Nat → R) : ∀ (words state acc shift : Nat),
    wordLoop k words state acc shift =
      k (acc + (collectCoeffWord words shift state).1) (collectCoeffWord words shift state).2 := by
  intro words
  induction words with
  | zero => intro state acc shift; rfl
  | succ w ih =>
    intro state acc shift
    show wordLoop k w (lcgStep state) (acc + (lcgStep state) <<< shift) (shift + 64) = _
    rw [ih, lcgStep_eq, cCW_succ, Nat.shiftLeft_eq, Nat.add_assoc]

theorem coeffOff_eq (Ω w words word : Nat) (hw : 2 ^ (w - 1) ≤ Ω) :
    ((coeffOff Ω w words word : Nat) : Int) - Ω = centeredNonzeroCoeff w words word := by
  have e1 : coeffOff Ω w words word = if word >>> (64 * words - w) = 2 ^ (w - 1) then Ω + 1
      else word >>> (64 * words - w) + Ω - 2 ^ (w - 1) := by
    unfold coeffOff; simp only [bcases_eq, beq_true]; rfl
  rw [e1]
  clear e1
  unfold centeredNonzeroCoeff
  generalize word >>> (64 * words - w) = top
  by_cases h : top = 2 ^ (w - 1)
  · rw [if_pos h, h]
    simp only [Int.sub_self, BEq.rfl, if_true]
    omega
  · rw [if_neg h]
    dsimp only
    have h2 : ((Int.ofNat top - Int.ofNat (2 ^ (w - 1))) == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, Int.ofNat_eq_natCast]; omega
    rw [h2]
    simp only [Bool.false_eq_true, if_false, Int.ofNat_eq_natCast]
    omega

theorem coefficientWidth_le (k i : Nat) : coefficientWidth k i ≤ k := by
  unfold coefficientWidth clampWidth
  split <;> exact Nat.min_le_left _ _

theorem coeffsLoop_eq (K : Nat) : ∀ count index state,
    dec (2 ^ (K - 1)) (coeffsLoop K (2 ^ (K - 1)) count index state) =
      coefficientsFrom count K index state := by
  intro count
  induction count with
  | zero => intro index state; rfl
  | succ c ih =>
    intro index state
    show dec (2 ^ (K - 1)) (wordLoop (fun word state' => coeffOff (2 ^ (K - 1)) (widthF K index)
        ((widthF K index + 63) / 64) word :: coeffsLoop K (2 ^ (K - 1)) c (index + 1) state')
        ((widthF K index + 63) / 64) state 0 0) = _
    rw [wordLoop_eq, widthF_eq, coefficientsFrom.eq_2]
    rcases h : collectCoeffWord ((coefficientWidth K index + 63) / 64) 0 state with ⟨word, st⟩
    simp only [dec, List.map_cons]
    rw [Nat.zero_add]
    have hw : 2 ^ (coefficientWidth K index - 1) ≤ 2 ^ (K - 1) :=
      Nat.pow_le_pow_right (by decide) (by have := coefficientWidth_le K index; omega)
    rw [coeffOff_eq _ _ _ _ hw]
    congr 1
    exact ih (index + 1) st

theorem genOff_eq (n : Nat) : dec (2 ^ (kbitsF n - 1)) (genOff n) = polyOf n := by
  show dec (2 ^ (kbitsF n - 1)) ((2 ^ (kbitsF n - 1) + 1) ::
      coeffsLoop (kbitsF n) (2 ^ (kbitsF n - 1)) 24 1 (seedF n)) = _
  simp only [dec, List.map_cons]
  have h := coeffsLoop_eq (kbitsF n) 24 1 (seedF n)
  simp only [dec] at h
  rw [h, kbitsF_eq, seedF_eq]
  unfold polyOf
  simp only [List.cons.injEq, and_true]
  omega

/-! ## Implementation -/

/-- The generated polynomial as integers (fast generator, decoded). -/
def fastPoly (n : Nat) : List Int :=
  dec (Nat.pow (nat_lit 2) (Nat.sub (kbitsF n) (nat_lit 1))) (genOff n)

def impl (n : Nat) : Int := discriminantFromPoly (fastPoly n)

theorem impl_correct : ∀ n, impl n = discSpec n := by
  intro n
  show discriminantFromPoly (dec (2 ^ (kbitsF n - 1)) (genOff n)) = discriminantFromPoly (polyOf n)
  rw [genOff_eq]

end Submission
