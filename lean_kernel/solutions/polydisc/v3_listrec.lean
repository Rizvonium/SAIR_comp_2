import Spec

/-!
# polydisc v3: normal subresultant PRS on an offset representation

`impl n` runs a fast version of the specification's *normal* subresultant PRS and
falls back to `discSpec n` itself whenever the fast path reports a failure, so the
fallback (abnormal degree drops, failed exact divisions) needs no separate proof.

Fast path, written with raw kernel primitives (`Nat.add/sub/mul/div/pow/shiftLeft/
shiftRight`, `nat_lit` numerals, `Nat.rec` loops, `casesOn` selections):

* The generator is re-implemented step by step (`genOff`); every coefficient `x` is
  stored as the natural number `x + Ω` (`Ω = 2^(k-1)`), so no `Int` arithmetic is needed.
* The derivative is produced directly in offset form (offset `24 Ω`).
* One PRS step computes every coefficient of the next subresultant in a single pass:
  `h_i = (A f_{i+2} - B g_{i+2} - C g_{i+1}) / D` with signed scalars split into
  positive/negative parts and a constant `K` that turns the numerator into
  `true numerator + Ω' D` (a natural number).  The pass accumulates
  `Σ num`, `Σ q`, `Σ (neg - pos)`; a single final test `E = 0` certifies that no
  subtraction was truncated, every division was exact and all leading coefficients
  were nonzero.  Only then is the result used.

Proof structure: `genOff_eq` (generator), `dec_derivLoop` (derivative),
`rowLoop_eq` + `row_correct` + `stepA_spec` (one row equals the specification's
pseudo-remainder followed by exact division), `prs_main` (induction over the steps
against `normalResultantGo`), `fastDisc_sound`, `impl_correct`.
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

/-! ## Derivative (offset `24 Ω`) -/

/-- `derivLoop Ω m i l`: the coefficients `(24 - j) * X_j + j * Ω` for `j = i, i+1, …`. -/
def derivLoop (Ω : Nat) : Nat → Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat)
    (fun _ _ => [])
    (fun _ ih i l => List.casesOn (motive := fun _ => List Nat) l []
       (fun x xs => Nat.add (Nat.mul (Nat.sub (nat_lit 24) i) x) (Nat.mul i Ω) ::
          ih (Nat.add i (nat_lit 1)) xs))

/-! ## One PRS row on the offset representation

For `f` (offset `Ωf`) and `g` (offset `Ωg`), the next subresultant coefficients are
`h_i = (A f_{i+2} - B g_{i+2} - C g_{i+1}) / D` with `A = g0²`, `B = g0 f0`,
`C = g0 f1 - f0 g1`, `D = f0²` (or `1` at the first step).  Signed scalars are kept as
pairs `Bp - Bn`, `Cp - Cn`; the per-element numerator is `pos - neg` with
`pos = A F + Bn G2 + Cn G1 + K`, `neg = Bp G2 + Cp G1`, where `K` makes it the true
numerator plus `Ω' D`.  The loop accumulates `Σ num`, `Σ q` and `Σ (neg - pos)` so a
single final test certifies that no subtraction was truncated and every division was
exact. -/
/-- Compiled counterpart of `rowLoop` (same function, structural recursion); only used by
the code generator, never by the kernel. -/
def rowLoopC (A Bp Bn Cp Cn K D pad : Nat) {R : Type} (k : List Nat → Nat → Nat → Nat → R)
    (dl : List Nat → List Nat) : List Nat → Nat → List Nat → Nat → Nat → Nat → R
  | [], _, _, sn, sq, t => k (dl []) sn sq t
  | fa :: fs, cur, gs, sn, sq, t =>
    let nxt := gs.headD pad
    let pos := A * fa + Bn * nxt + Cn * cur + K
    let neg := Bp * nxt + Cp * cur
    let q := (pos - neg) / D
    rowLoopC A Bp Bn Cp Cn K D pad k (fun tl => dl (q :: tl)) fs nxt gs.tail
      (sn + (pos - neg)) (sq + q) (t + (neg - pos))

@[implemented_by rowLoopC]
def rowLoop (A Bp Bn Cp Cn K D pad : Nat) {R : Type} (k : List Nat → Nat → Nat → Nat → R)
    (dl : List Nat → List Nat) (fs : List Nat) (cur : Nat) (gs : List Nat) (sn sq t : Nat) : R :=
  List.rec (motive := fun _ => (List Nat → List Nat) → Nat → List Nat → Nat → Nat → Nat → R)
    (fun dl _ _ sn sq t => k (dl []) sn sq t)
    (fun fa _ ih dl cur gs sn sq t =>
      let step := fun (nxt : Nat) (gs' : List Nat) =>
        let pos := Nat.add (Nat.add (Nat.add (Nat.mul A fa) (Nat.mul Bn nxt)) (Nat.mul Cn cur)) K
        let neg := Nat.add (Nat.mul Bp nxt) (Nat.mul Cp cur)
        let num := Nat.sub pos neg
        let q := Nat.div num D
        ih (fun tl => dl (q :: tl)) nxt gs' (Nat.add sn num) (Nat.add sq q)
          (Nat.add t (Nat.sub neg pos))
      List.rec (motive := fun _ => R) (step pad []) (fun nxt gs' _ => step nxt gs') gs)
    fs dl cur gs sn sq t

/-- Error contribution of one step: nonzero iff a check failed. -/
def stepErr (D Cp Cn Ω' H0 sn sq t : Nat) : Nat :=
  Nat.add (Nat.add (Nat.sub sn (Nat.mul D sq)) t)
    (Nat.add (Nat.sub (nat_lit 1) (Nat.add Cp Cn))
      (Nat.sub (nat_lit 1) (Nat.add (Nat.sub H0 Ω') (Nat.sub Ω' H0))))

/-- Continuation after a row: check the head of the new remainder and recurse. -/
def stepK (ih : List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int)
    (g : List Nat) (Ωg Ω' A D Cp Cn E : Nat) (h : List Nat) (sn sq t : Nat) : Option Int :=
  List.casesOn (motive := fun _ => Option Int) h none
    (fun H0 _ => ih g h Ωg Ω' A (Nat.add E (stepErr D Cp Cn Ω' H0 sn sq t)))

def stepF (ih : List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int)
    (g fs : List Nat) (G1 : Nat) (gs : List Nat) (Ωg D E Cp Cn A Bp Bn Ω' K : Nat) : Option Int :=
  rowLoop A Bp Bn Cp Cn K D Ωg (stepK ih g Ωg Ω' A D Cp Cn E)
    (fun tl => tl) fs G1 gs (nat_lit 0) (nat_lit 0) (nat_lit 0)

def stepE (ih : List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int)
    (g fs : List Nat) (G1 : Nat) (gs : List Nat) (Ωf Ωg D E Cp Cn A Bp Bn Ω' : Nat) : Option Int :=
  stepF ih g fs G1 gs Ωg D E Cp Cn A Bp Bn Ω'
    (Nat.sub (Nat.add (Nat.mul Ω' D) (Nat.mul (Nat.add Bp Cp) Ωg))
      (Nat.add (Nat.mul A Ωf) (Nat.mul (Nat.add Bn Cn) Ωg)))

def stepD (ih : List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int)
    (g fs : List Nat) (G1 : Nat) (gs : List Nat) (Ωf Ωg D E Cp Cn A Bp Bn : Nat) : Option Int :=
  stepE ih g fs G1 gs Ωf Ωg D E Cp Cn A Bp Bn
    (Nat.add (Nat.div (Nat.add (Nat.mul A Ωf) (Nat.mul (Nat.add (Nat.add Bp Bn) (Nat.add Cp Cn)) Ωg)) D)
      (nat_lit 1))

def stepC (ih : List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int)
    (g fs : List Nat) (G1 : Nat) (gs : List Nat) (Ωf Ωg D E u v A Bp Bn : Nat) : Option Int :=
  stepD ih g fs G1 gs Ωf Ωg D E (Nat.sub u v) (Nat.sub v u) A Bp Bn

def stepB (ih : List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int)
    (g fs : List Nat) (G1 : Nat) (gs : List Nat) (Ωf Ωg D E f0p f0n f1p f1n g0p g0n g1p g1n : Nat) :
    Option Int :=
  stepC ih g fs G1 gs Ωf Ωg D E
    (Nat.add (Nat.add (Nat.mul g0p f1p) (Nat.mul g0n f1n)) (Nat.add (Nat.mul f0p g1n) (Nat.mul f0n g1p)))
    (Nat.add (Nat.add (Nat.mul g0p f1n) (Nat.mul g0n f1p)) (Nat.add (Nat.mul f0p g1p) (Nat.mul f0n g1n)))
    (Nat.pow (Nat.add g0p g0n) (nat_lit 2))
    (Nat.add (Nat.mul g0p f0p) (Nat.mul g0n f0n))
    (Nat.add (Nat.mul g0p f0n) (Nat.mul g0n f0p))

def stepA (ih : List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int)
    (g : List Nat) (F0 F1 : Nat) (fs : List Nat) (G0 G1 : Nat) (gs : List Nat) (Ωf Ωg D E : Nat) :
    Option Int :=
  stepB ih g fs G1 gs Ωf Ωg D E (Nat.sub F0 Ωf) (Nat.sub Ωf F0) (Nat.sub F1 Ωf) (Nat.sub Ωf F1)
    (Nat.sub G0 Ωg) (Nat.sub Ωg G0) (Nat.sub G1 Ωg) (Nat.sub Ωg G1)

/-- The PRS loop: `fuel` more steps from `(f, g)` with offsets `Ωf, Ωg`, divisor `D`
(the square of the previous leading coefficient, `1` at the start) and accumulated
error `E`.  Returns the last remainder's constant when every check passed. -/
def prsLoop : Nat → List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int :=
  Nat.rec (motive := fun _ => List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int)
    (fun _ g _ Ωg _ E =>
      List.casesOn (motive := fun _ => Option Int) g none (fun G0 _ =>
        Bool.casesOn (motive := fun _ => Option Int) (Nat.beq E (nat_lit 0)) none
          (some (Int.subNatNat G0 Ωg))))
    (fun _ ih f g Ωf Ωg D E =>
      List.casesOn (motive := fun _ => Option Int) f none (fun F0 ft =>
      List.casesOn (motive := fun _ => Option Int) ft none (fun F1 fs =>
      List.casesOn (motive := fun _ => Option Int) g none (fun G0 gt =>
      List.casesOn (motive := fun _ => Option Int) gt none (fun G1 gs =>
        stepA ih g F0 F1 fs G0 G1 gs Ωf Ωg D E)))))

/-- Offset of the generated polynomial. -/
def omegaOf (n : Nat) : Nat := Nat.pow (nat_lit 2) (Nat.sub (kbitsF n) (nat_lit 1))

/-- Fast path: the normal subresultant PRS on the offset representation. -/
def fastFrom (P : List Nat) (Ω : Nat) : Option Int :=
  prsLoop (nat_lit 23) P (derivLoop Ω (nat_lit 24) (nat_lit 0) P) Ω (Nat.mul (nat_lit 24) Ω) (nat_lit 1)
    (nat_lit 0)

def fastDisc (n : Nat) : Option Int := fastFrom (genOff n) (omegaOf n)

def impl (n : Nat) : Int :=
  match fastDisc n with
  | some r => r
  | none => discSpec n

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

/-! ## Proofs: row loop -/

/-- Triples `(F_{i+2}, G_{i+1}, G_{i+2})` visited by the row loop (`G_L` read as `pad`). -/
def trip (pad : Nat) : List Nat → Nat → List Nat → List (Nat × Nat × Nat)
  | [], _, _ => []
  | fa :: fs, cur, gs => (fa, cur, gs.headD pad) :: trip pad fs (gs.headD pad) gs.tail

def posN (A Bn Cn K : Nat) (x : Nat × Nat × Nat) : Nat := A * x.1 + Bn * x.2.2 + Cn * x.2.1 + K
def negN (Bp Cp : Nat) (x : Nat × Nat × Nat) : Nat := Bp * x.2.2 + Cp * x.2.1

theorem rowLoop_cons (A Bp Bn Cp Cn K D pad : Nat) {R : Type}
    (k : List Nat → Nat → Nat → Nat → R) (dl : List Nat → List Nat) (fa : Nat)
    (fs : List Nat) (cur : Nat) (gs : List Nat) (sn sq t : Nat) :
    rowLoop A Bp Bn Cp Cn K D pad k dl (fa :: fs) cur gs sn sq t =
      rowLoop A Bp Bn Cp Cn K D pad k
        (fun tl => dl ((posN A Bn Cn K (fa, cur, gs.headD pad) - negN Bp Cp (fa, cur, gs.headD pad)) / D :: tl))
        fs (gs.headD pad) gs.tail
        (sn + (posN A Bn Cn K (fa, cur, gs.headD pad) - negN Bp Cp (fa, cur, gs.headD pad)))
        (sq + (posN A Bn Cn K (fa, cur, gs.headD pad) - negN Bp Cp (fa, cur, gs.headD pad)) / D)
        (t + (negN Bp Cp (fa, cur, gs.headD pad) - posN A Bn Cn K (fa, cur, gs.headD pad))) := by
  cases gs <;> rfl

theorem rowLoop_eq (A Bp Bn Cp Cn K D pad : Nat) {R : Type} (k : List Nat → Nat → Nat → Nat → R) :
    ∀ (fs : List Nat) (dl : List Nat → List Nat) (cur : Nat) (gs : List Nat) (sn sq t : Nat),
    rowLoop A Bp Bn Cp Cn K D pad k dl fs cur gs sn sq t =
      k (dl ((trip pad fs cur gs).map (fun x => (posN A Bn Cn K x - negN Bp Cp x) / D)))
        (sn + ((trip pad fs cur gs).map (fun x => posN A Bn Cn K x - negN Bp Cp x)).sum)
        (sq + ((trip pad fs cur gs).map (fun x => (posN A Bn Cn K x - negN Bp Cp x) / D)).sum)
        (t + ((trip pad fs cur gs).map (fun x => negN Bp Cp x - posN A Bn Cn K x)).sum) := by
  intro fs
  induction fs with
  | nil => intro dl cur gs sn sq t; rfl
  | cons fa fs ih =>
    intro dl cur gs sn sq t
    rw [rowLoop_cons, ih]
    simp only [trip, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem trip_length (pad : Nat) : ∀ (fs : List Nat) (cur : Nat) (gs : List Nat),
    (trip pad fs cur gs).length = fs.length := by
  intro fs
  induction fs with
  | nil => intro cur gs; rfl
  | cons fa fs ih => intro cur gs; simp [trip, ih]

theorem sum_sub_zero {α : Type} (p n : α → Nat) : ∀ (L : List α),
    (L.map (fun x => n x - p x)).sum = 0 → ∀ x ∈ L, n x ≤ p x := by
  intro L h x hx
  have := List.sum_eq_zero_iff_forall_eq_nat.mp h (n x - p x) (List.mem_map_of_mem hx)
  omega

theorem sum_le_div (D : Nat) {α : Type} (a : α → Nat) : ∀ (L : List α),
    D * (L.map (fun x => a x / D)).sum ≤ (L.map a).sum := by
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    have h1 := Nat.div_add_mod (a x) D
    omega

theorem sum_div_exact (D : Nat) {α : Type} (a : α → Nat) : ∀ (L : List α),
    (L.map a).sum - D * (L.map (fun x => a x / D)).sum = 0 → ∀ x ∈ L, a x % D = 0 := by
  intro L
  induction L with
  | nil => intro _ x hx; simp at hx
  | cons y L ih =>
    intro h x hx
    simp only [List.map_cons, List.sum_cons, Nat.mul_add] at h
    have h1 := Nat.div_add_mod (a y) D
    have h2 := sum_le_div D a L
    have hy : a y % D = 0 := by omega
    have hL : (L.map a).sum - D * (L.map (fun x => a x / D)).sum = 0 := by omega
    rcases List.mem_cons.mp hx with h3 | h3
    · subst h3; exact hy
    · exact ih hL x h3

/-! ## Proofs: the specification's normal step -/

theorem trimLeading_cons {x : Int} (xs : List Int) (h : x ≠ 0) : trimLeading (x :: xs) = x :: xs :=
  trimLeading.eq_3 x xs h

theorem scalePolynomial_one : ∀ l : List Int, scalePolynomial 1 l = l
  | [] => rfl
  | a :: as => by rw [scalePolynomial.eq_2, Int.one_mul, scalePolynomial_one as]

/-- The normal-case pseudo-remainder, element by element. -/
def row2 (g0 f0 c : Int) : List Int → Int → List Int → List Int
  | [], _, _ => []
  | fa :: fs, cur, gs => (g0 * (g0 * fa - f0 * gs.headD 0) - c * cur) :: row2 g0 f0 c fs (gs.headD 0) gs.tail

theorem row2_length (g0 f0 c : Int) : ∀ (fs : List Int) (cur : Int) (gs : List Int),
    (row2 g0 f0 c fs cur gs).length = fs.length := by
  intro fs
  induction fs with
  | nil => intro cur gs; rfl
  | cons fa fs ih => intro cur gs; simp [row2, ih]

theorem cpl_length (a b : Int) : ∀ (xs ys : List Int), (cancelPseudoLeading a b xs ys).length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys; rw [cancelPseudoLeading.eq_3]
  | cons x xs ih =>
    intro ys
    cases ys with
    | nil => rw [cancelPseudoLeading.eq_2]; simp [ih]
    | cons y ys => rw [cancelPseudoLeading.eq_1]; simp [ih]

theorem cpl_row2 (g0 f0 c : Int) : ∀ (ft gt : List Int) (cur : Int), ft.length = gt.length + 1 →
    cancelPseudoLeading g0 c (cancelPseudoLeading g0 f0 ft gt) (cur :: gt) = row2 g0 f0 c ft cur gt := by
  intro ft
  induction ft with
  | nil => intro gt cur h; simp at h
  | cons fa ft ih =>
    intro gt cur h
    cases gt with
    | nil =>
      have hft : ft = [] := by simpa using h
      subst hft
      rw [cancelPseudoLeading.eq_2, cancelPseudoLeading.eq_3, cancelPseudoLeading.eq_1,
        cancelPseudoLeading.eq_3]
      simp [row2]
    | cons gb gt =>
      rw [cancelPseudoLeading.eq_1, cancelPseudoLeading.eq_1, ih gt gb (by simpa using h)]
      simp [row2]

theorem pseudoRemainder_normal (f0 f1 g0 g1 : Int) (ft gt : List Int)
    (hf0 : f0 ≠ 0) (hg0 : g0 ≠ 0) (hc : g0 * f1 - f0 * g1 ≠ 0) (hlen : ft.length = gt.length + 1)
    (hn : (row2 g0 f0 (g0 * f1 - f0 * g1) ft g1 gt).headD 0 ≠ 0) :
    pseudoRemainder (f0 :: f1 :: ft) (g0 :: g1 :: gt) =
      some (row2 g0 f0 (g0 * f1 - f0 * g1) ft g1 gt) := by
  have hN2 := cpl_row2 g0 f0 (g0 * f1 - f0 * g1) ft gt g1 hlen
  generalize hR : row2 g0 f0 (g0 * f1 - f0 * g1) ft g1 gt = N2 at hN2 hn
  have hN2len : N2.length = gt.length + 1 := by rw [← hR, row2_length, hlen]
  obtain ⟨b2, bs2, hb2⟩ : ∃ b bs, N2 = b :: bs := by
    cases N2 with
    | nil => simp at hN2len
    | cons b bs => exact ⟨b, bs, rfl⟩
  have hb2ne : b2 ≠ 0 := by rw [hb2] at hn; simpa using hn
  have hT2 : trimLeading N2 = N2 := by rw [hb2]; exact trimLeading_cons _ hb2ne
  have hN1len : (cancelPseudoLeading g0 f0 ft gt).length = gt.length + 1 := by
    rw [cpl_length, hlen]
  unfold pseudoRemainder
  simp only [trimLeading_cons _ hf0, trimLeading_cons _ hg0, List.isEmpty_cons, Bool.false_eq_true,
    if_false, List.length_cons]
  rw [if_neg (by omega)]
  -- first cancellation
  rw [pseudoRemainderGo.eq_2 _ _ _ _ _ _ _ (trimLeading_cons _ hf0)]
  rw [trimLeading_cons _ hf0, if_neg (by simp [hlen])]
  simp only []
  rw [cancelPseudoLeading.eq_1, trimLeading_cons _ hc]
  -- second cancellation
  rw [pseudoRemainderGo.eq_2 _ _ _ _ _ _ _ (trimLeading_cons _ hc)]
  rw [trimLeading_cons _ hc, if_neg (by simp [hN1len])]
  simp only []
  rw [hN2, hT2]
  -- final: the remainder is shorter than the divisor
  rw [hb2, pseudoRemainderGo.eq_2 _ _ _ _ _ _ _ (by rw [← hb2, hT2, hb2])]
  rw [← hb2, hT2, if_pos (by rw [hN2len]; simp)]
  have h0 : ft.length + 1 + 1 - (gt.length + 1 + 1) + 1 - 1 - 1 = 0 := by omega
  rw [h0, Int.pow_zero, scalePolynomial_one]

theorem exactDivide_ok (d : Int) (hd : d ≠ 0) : ∀ l : List Int, (∀ x ∈ l, x % d = 0) →
    exactDividePolynomial d l = some (l.map (· / d)) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    rw [exactDividePolynomial.eq_2, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
    have ha : a % d = 0 := h a (List.mem_cons_self)
    simp [hd, ha]

/-- What the specification does after a successful normal step producing `h`. -/
def nextOrStop (fuel : Nat) (g h : List Int) : Option Int :=
  match h with
  | [c] => some c
  | _ => normalResultantGo fuel false g h

theorem nrg_step (fuel : Nat) (initial : Bool) (f g h raw : List Int)
    (hpr : pseudoRemainder f g = some raw)
    (hdiv : (if initial = true then some raw else exactDividePolynomial (f.headD 0 ^ 2) raw) = some h)
    (hh : h.headD 0 ≠ 0) (hlen : h.length + 1 = g.length) :
    normalResultantGo (fuel + 1) initial f g = nextOrStop fuel g h := by
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, h = x :: xs := by
    cases h with
    | nil => simp at hh
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hx : x ≠ 0 := by simpa using hh
  rw [normalResultantGo.eq_2, hpr]
  simp only [hdiv, trimLeading_cons _ hx]
  rw [if_pos (by simp [← hlen])]
  rfl

/-! ## Proofs: one row on the offset representation is the specification's row -/

/-- The specification's numerator for one visited triple, on decoded values. -/
def trueNum (g0 f0 c : Int) (Ωf Ωg : Nat) (x : Nat × Nat × Nat) : Int :=
  g0 * (g0 * ((x.1 : Int) - Ωf) - f0 * ((x.2.2 : Int) - Ωg)) - c * ((x.2.1 : Int) - Ωg)

theorem row2_trip (g0 f0 c : Int) (Ωf Ωg : Nat) : ∀ (fs : List Nat) (cur : Nat) (gs : List Nat),
    row2 g0 f0 c (dec Ωf fs) ((cur : Int) - Ωg) (dec Ωg gs) =
      (trip Ωg fs cur gs).map (trueNum g0 f0 c Ωf Ωg) := by
  intro fs
  induction fs with
  | nil => intro cur gs; rfl
  | cons fa fs ih =>
    intro cur gs
    have e1 : (dec Ωg gs).headD 0 = ((gs.headD Ωg : Nat) : Int) - Ωg := by
      cases gs <;> simp [dec]
    have e2 : (dec Ωg gs).tail = dec Ωg gs.tail := by
      cases gs <;> simp [dec]
    simp only [dec, List.map_cons] at *
    rw [row2, trip, List.map_cons, e2, e1, ih]
    rfl

theorem elem_eq (A Bp Bn Cp Cn K D Ωf Ωg Ω' : Nat) (g0 f0 c : Int) (x : Nat × Nat × Nat)
    (hA : (A : Int) = g0 * g0) (hB : (Bp : Int) - Bn = g0 * f0) (hC : (Cp : Int) - Cn = c)
    (hK : (K : Int) = Ω' * D + (Bp + Cp) * Ωg - A * Ωf - (Bn + Cn) * Ωg)
    (hle : negN Bp Cp x ≤ posN A Bn Cn K x) :
    ((posN A Bn Cn K x - negN Bp Cp x : Nat) : Int) = trueNum g0 f0 c Ωf Ωg x + Ω' * D := by
  rw [Int.ofNat_sub hle]
  unfold posN negN trueNum
  push_cast
  rw [hK]
  grind

theorem quot_eq (num D Ω' : Nat) (t : Int) (hD : 0 < D) (hnum : (num : Int) = t + Ω' * D)
    (hmod : num % D = 0) : t % (D : Int) = 0 ∧ ((num / D : Nat) : Int) - Ω' = t / D := by
  have hD' : (D : Int) ≠ 0 := by omega
  have h1 : (num : Int) % D = 0 := by exact_mod_cast hmod
  rw [hnum, Int.add_mul_emod_self_right] at h1
  refine ⟨h1, ?_⟩
  have h2 : ((num / D : Nat) : Int) = (num : Int) / D := by push_cast; rfl
  rw [h2, hnum, Int.add_mul_ediv_right _ _ hD']
  omega

theorem row_correct (A Bp Bn Cp Cn K D Ωf Ωg Ω' : Nat) (g0 f0 c : Int) (L : List (Nat × Nat × Nat))
    (hA : (A : Int) = g0 * g0) (hB : (Bp : Int) - Bn = g0 * f0) (hC : (Cp : Int) - Cn = c)
    (hK : (K : Int) = Ω' * D + (Bp + Cp) * Ωg - A * Ωf - (Bn + Cn) * Ωg) (hD : 0 < D)
    (hT : (L.map (fun x => negN Bp Cp x - posN A Bn Cn K x)).sum = 0)
    (hS : (L.map (fun x => posN A Bn Cn K x - negN Bp Cp x)).sum -
      D * (L.map (fun x => (posN A Bn Cn K x - negN Bp Cp x) / D)).sum = 0) :
    (∀ y ∈ L.map (trueNum g0 f0 c Ωf Ωg), y % (D : Int) = 0) ∧
    dec Ω' (L.map (fun x => (posN A Bn Cn K x - negN Bp Cp x) / D)) =
      (L.map (trueNum g0 f0 c Ωf Ωg)).map (· / (D : Int)) := by
  have hle := sum_sub_zero (posN A Bn Cn K) (negN Bp Cp) L hT
  have hmod := sum_div_exact D (fun x => posN A Bn Cn K x - negN Bp Cp x) L hS
  have key : ∀ x ∈ L, trueNum g0 f0 c Ωf Ωg x % (D : Int) = 0 ∧
      (((posN A Bn Cn K x - negN Bp Cp x) / D : Nat) : Int) - Ω' = trueNum g0 f0 c Ωf Ωg x / D :=
    fun x hx => quot_eq _ D Ω' _ hD (elem_eq A Bp Bn Cp Cn K D Ωf Ωg Ω' g0 f0 c x hA hB hC hK (hle x hx))
      (hmod x hx)
  constructor
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact (key x hx).1
  · simp only [dec, List.map_map]
    apply List.map_congr_left
    intro x hx
    exact (key x hx).2

theorem stepF_spec (ih : List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int)
    (G fs : List Nat) (G1 : Nat) (gs : List Nat) (Ωf Ωg D E Cp Cn A Bp Bn Ω' K : Nat)
    (f0 f1 g0 : Int) (hlen : fs.length = gs.length + 1) (hfs : fs.length ≤ 30) :
    ∃ H err, stepF ih G fs G1 gs Ωg D E Cp Cn A Bp Bn Ω' K = ih G H Ωg Ω' A (E + err) ∧
      H.length = fs.length ∧
      ((A : Int) = g0 * g0 → (Bp : Int) - Bn = g0 * f0 →
        (Cp : Int) - Cn = g0 * f1 - f0 * ((G1 : Int) - Ωg) → (Cp = 0 ∨ Cn = 0) →
        (K : Int) = Ω' * D + (Bp + Cp) * Ωg - A * Ωf - (Bn + Cn) * Ωg → 0 < D →
        err = 0 → g0 * f1 - f0 * ((G1 : Int) - Ωg) ≠ 0 ∧ (dec Ω' H).headD 0 ≠ 0 ∧
        (∀ y ∈ row2 g0 f0 (g0 * f1 - f0 * ((G1 : Int) - Ωg)) (dec Ωf fs) ((G1 : Int) - Ωg) (dec Ωg gs),
          y % (D : Int) = 0) ∧
        dec Ω' H = (row2 g0 f0 (g0 * f1 - f0 * ((G1 : Int) - Ωg)) (dec Ωf fs) ((G1 : Int) - Ωg)
          (dec Ωg gs)).map (· / (D : Int))) := by
  have hrow := rowLoop_eq A Bp Bn Cp Cn K D Ωg (stepK ih G Ωg Ω' A D Cp Cn E) fs (fun tl => tl) G1 gs
    0 0 0
  generalize hL : trip Ωg fs G1 gs = L at hrow
  have hLlen : L.length = fs.length := by rw [← hL, trip_length]
  obtain ⟨H0, Hs, hH0⟩ : ∃ H0 Hs, L.map (fun x => (posN A Bn Cn K x - negN Bp Cp x) / D) = H0 :: Hs := by
    cases hc : L.map (fun x => (posN A Bn Cn K x - negN Bp Cp x) / D) with
    | nil =>
      have := congrArg List.length hc
      simp only [List.length_map, List.length_nil] at this
      omega
    | cons H0 Hs => exact ⟨H0, Hs, rfl⟩
  refine ⟨L.map (fun x => (posN A Bn Cn K x - negN Bp Cp x) / D), stepErr D Cp Cn Ω' H0
      (0 + (L.map (fun x => posN A Bn Cn K x - negN Bp Cp x)).sum)
      (0 + (L.map (fun x => (posN A Bn Cn K x - negN Bp Cp x) / D)).sum)
      (0 + (L.map (fun x => negN Bp Cp x - posN A Bn Cn K x)).sum), ?_, by simp [hLlen], ?_⟩
  · show rowLoop A Bp Bn Cp Cn K D Ωg (stepK ih G Ωg Ω' A D Cp Cn E) (fun tl => tl) fs G1 gs 0 0 0 = _
    rw [hrow]
    generalize hs1 : (0 + (L.map (fun x => posN A Bn Cn K x - negN Bp Cp x)).sum) = s1
    generalize hs2 : (0 + (L.map (fun x => (posN A Bn Cn K x - negN Bp Cp x) / D)).sum) = s2
    generalize hs3 : (0 + (L.map (fun x => negN Bp Cp x - posN A Bn Cn K x)).sum) = s3
    rw [hH0]
    rfl
  · intro hA hB hC hCpn hK hD herr
    unfold stepErr at herr
    simp only [Nat.zero_add, Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at herr
    have hT : (L.map (fun x => negN Bp Cp x - posN A Bn Cn K x)).sum = 0 := by omega
    have hS : (L.map (fun x => posN A Bn Cn K x - negN Bp Cp x)).sum -
        D * (L.map (fun x => (posN A Bn Cn K x - negN Bp Cp x) / D)).sum = 0 := by omega
    have hc0 : 1 - (Cp + Cn) = 0 := by omega
    have hh0 : 1 - ((H0 - Ω') + (Ω' - H0)) = 0 := by omega
    have hrc := row_correct A Bp Bn Cp Cn K D Ωf Ωg Ω' g0 f0 _ L hA hB hC hK hD hT hS
    rw [← hL, ← row2_trip] at hrc
    rw [hL] at hrc
    refine ⟨?_, ?_, hrc.1, hrc.2⟩
    · rw [← hC]; omega
    · rw [hH0]; simp [dec]; omega

theorem stepA_spec (ih : List Nat → List Nat → Nat → Nat → Nat → Nat → Option Int)
    (F0 F1 G0 G1 : Nat) (fs gs : List Nat) (Ωf Ωg D E : Nat)
    (hlen : fs.length = gs.length + 1) (hfs : fs.length ≤ 30) :
    ∃ H Ω' A err, stepA ih (G0 :: G1 :: gs) F0 F1 fs G0 G1 gs Ωf Ωg D E =
        ih (G0 :: G1 :: gs) H Ωg Ω' A (E + err) ∧
      H.length = fs.length ∧ (A : Int) = ((G0 : Int) - Ωg) * ((G0 : Int) - Ωg) ∧
      (0 < D → err = 0 →
        ((G0 : Int) - Ωg) * ((F1 : Int) - Ωf) - ((F0 : Int) - Ωf) * ((G1 : Int) - Ωg) ≠ 0 ∧
        (dec Ω' H).headD 0 ≠ 0 ∧
        (∀ y ∈ row2 ((G0 : Int) - Ωg) ((F0 : Int) - Ωf)
            (((G0 : Int) - Ωg) * ((F1 : Int) - Ωf) - ((F0 : Int) - Ωf) * ((G1 : Int) - Ωg))
            (dec Ωf fs) ((G1 : Int) - Ωg) (dec Ωg gs), y % (D : Int) = 0) ∧
        dec Ω' H = (row2 ((G0 : Int) - Ωg) ((F0 : Int) - Ωf)
            (((G0 : Int) - Ωg) * ((F1 : Int) - Ωf) - ((F0 : Int) - Ωf) * ((G1 : Int) - Ωg))
            (dec Ωf fs) ((G1 : Int) - Ωg) (dec Ωg gs)).map (· / (D : Int))) := by
  unfold stepA stepB stepC stepD stepE
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  generalize hf0p : F0 - Ωf = f0p
  generalize hf0n : Ωf - F0 = f0n
  generalize hf1p : F1 - Ωf = f1p
  generalize hf1n : Ωf - F1 = f1n
  generalize hg0p : G0 - Ωg = g0p
  generalize hg0n : Ωg - G0 = g0n
  generalize hg1p : G1 - Ωg = g1p
  generalize hg1n : Ωg - G1 = g1n
  have ef0 : (f0p : Int) - f0n = (F0 : Int) - Ωf := by omega
  have ef1 : (f1p : Int) - f1n = (F1 : Int) - Ωf := by omega
  have eg0 : (g0p : Int) - g0n = (G0 : Int) - Ωg := by omega
  have eg1 : (g1p : Int) - g1n = (G1 : Int) - Ωg := by omega
  have hg0z : g0p * g0n = 0 := by
    rcases Nat.le_total G0 Ωg with h | h
    · have : g0p = 0 := by omega
      simp [this]
    · have : g0n = 0 := by omega
      simp [this]
  generalize hu : g0p * f1p + g0n * f1n + (f0p * g1n + f0n * g1p) = u
  generalize hv : g0p * f1n + g0n * f1p + (f0p * g1p + f0n * g1n) = v
  generalize hA : Nat.pow (g0p + g0n) 2 = A
  generalize hBp : g0p * f0p + g0n * f0n = Bp
  generalize hBn : g0p * f0n + g0n * f0p = Bn
  have eA : (A : Int) = ((G0 : Int) - Ωg) * ((G0 : Int) - Ωg) := by
    rw [← hA, ← eg0]
    have : ((g0p * g0n : Nat) : Int) = 0 := by rw [hg0z]; rfl
    have hp : Nat.pow (g0p + g0n) 2 = (g0p + g0n) * (g0p + g0n) := Nat.pow_two (g0p + g0n)
    rw [hp]
    push_cast at this ⊢
    grind
  have eB : (Bp : Int) - Bn = ((G0 : Int) - Ωg) * ((F0 : Int) - Ωf) := by
    rw [← hBp, ← hBn, ← eg0, ← ef0]; push_cast; grind
  have euv : (u : Int) - v = ((G0 : Int) - Ωg) * ((F1 : Int) - Ωf) - ((F0 : Int) - Ωf) * ((G1 : Int) - Ωg) := by
    rw [← hu, ← hv, ← eg0, ← ef0, ← ef1, ← eg1]; push_cast; grind
  have eC : ((u - v : Nat) : Int) - ((v - u : Nat) : Int) =
      ((G0 : Int) - Ωg) * ((F1 : Int) - Ωf) - ((F0 : Int) - Ωf) * ((G1 : Int) - Ωg) := by
    rw [← euv]; omega
  have hCpn : u - v = 0 ∨ v - u = 0 := by omega
  generalize hX : A * Ωf + (Bp + Bn + (u - v + (v - u))) * Ωg = X
  obtain ⟨H, err, h1, h2, h3⟩ := stepF_spec ih (G0 :: G1 :: gs) fs G1 gs Ωf Ωg D E (u - v) (v - u) A Bp Bn
    (X / D + 1) ((X / D + 1) * D + (Bp + (u - v)) * Ωg - (A * Ωf + (Bn + (v - u)) * Ωg))
    ((F0 : Int) - Ωf) ((F1 : Int) - Ωf) ((G0 : Int) - Ωg) hlen hfs
  refine ⟨H, X / D + 1, A, err, h1, h2, eA, ?_⟩
  intro hD herr
  have hXdiv := Nat.div_add_mod X D
  have hXmod := Nat.mod_lt X hD
  have hle : A * Ωf + (Bn + (v - u)) * Ωg ≤ (X / D + 1) * D + (Bp + (u - v)) * Ωg := by
    have h1 : (X / D + 1) * D = D * (X / D) + D := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    have h2 : (Bp + Bn + (u - v + (v - u))) * Ωg = (Bp + (u - v)) * Ωg + (Bn + (v - u)) * Ωg := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  have eK : (((X / D + 1) * D + (Bp + (u - v)) * Ωg - (A * Ωf + (Bn + (v - u)) * Ωg) : Nat) : Int) =
      ((X / D + 1 : Nat) : Int) * D + ((Bp : Int) + ((u - v : Nat) : Int)) * Ωg - A * Ωf -
        ((Bn : Int) + ((v - u : Nat) : Int)) * Ωg := by
    rw [Int.ofNat_sub hle]; push_cast; omega
  exact h3 eA eB eC hCpn eK hD herr

theorem prsLoop_succ (k : Nat) (F0 F1 : Nat) (fs : List Nat) (G0 G1 : Nat) (gs : List Nat)
    (Ωf Ωg D E : Nat) :
    prsLoop (k + 1) (F0 :: F1 :: fs) (G0 :: G1 :: gs) Ωf Ωg D E =
      stepA (prsLoop k) (G0 :: G1 :: gs) F0 F1 fs G0 G1 gs Ωf Ωg D E := rfl

theorem prsLoop_E : ∀ (k : Nat) (F G : List Nat) (Ωf Ωg D E : Nat) (r : Int),
    G.length = k + 1 → F.length = G.length + 1 → G.length ≤ 25 →
    prsLoop k F G Ωf Ωg D E = some r → E = 0 := by
  intro k
  induction k with
  | zero =>
    intro F G Ωf Ωg D E r hG _ _ hrun
    match G, hG with
    | [G0], _ =>
      have : Nat.beq E 0 = true := by
        cases hb : Nat.beq E 0
        · have : prsLoop 0 F [G0] Ωf Ωg D E = none := by
            show Bool.casesOn (motive := fun _ => Option Int) (Nat.beq E 0) none _ = none
            rw [hb]
          rw [this] at hrun; cases hrun
        · rfl
      exact Nat.eq_of_beq_eq_true this
  | succ k ih =>
    intro F G Ωf Ωg D E r hG hF hG25 hrun
    match F, G, hF, hG with
    | F0 :: F1 :: fs, G0 :: G1 :: gs, hF, hG =>
      simp only [List.length_cons] at hF hG hG25
      obtain ⟨H, Ω', A, err, heq, hHlen, _, _⟩ :=
        stepA_spec (prsLoop k) F0 F1 G0 G1 fs gs Ωf Ωg D E (by omega) (by omega)
      rw [prsLoop_succ, heq] at hrun
      have := ih (G0 :: G1 :: gs) H Ωg Ω' A (E + err) r (by omega) (by simp; omega) (by omega) hrun
      omega

theorem int_sq (x : Int) : x ^ 2 = x * x := by
  rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

theorem int_sq_pos (x : Int) (h : x ≠ 0) : 0 < x * x := by
  rcases Int.lt_or_gt_of_ne h with h | h
  · exact Int.mul_pos_of_neg_of_neg h h
  · exact Int.mul_pos h h

theorem two_cons {α : Type} (L : List α) (h : 2 ≤ L.length) : ∃ a b t, L = a :: b :: t := by
  match L, h with
  | a :: b :: t, _ => exact ⟨a, b, t, rfl⟩

theorem dec_cons (Ω X : Nat) (L : List Nat) : dec Ω (X :: L) = ((X : Int) - Ω) :: dec Ω L := rfl
theorem dec_length (Ω : Nat) (L : List Nat) : (dec Ω L).length = L.length := by simp [dec]

theorem prs_step (k : Nat) (F0 F1 G0 G1 : Nat) (fs gs : List Nat) (Ωf Ωg D E : Nat) (initial : Bool)
    (r : Int) (hlen : fs.length = gs.length + 1) (hfs : fs.length ≤ 30)
    (hf0 : (F0 : Int) - Ωf ≠ 0) (hg0 : (G0 : Int) - Ωg ≠ 0)
    (hD : initial = true ∧ D = 1 ∨ initial = false ∧ (D : Int) = ((F0 : Int) - Ωf) ^ 2)
    (hrun : prsLoop (k + 1) (F0 :: F1 :: fs) (G0 :: G1 :: gs) Ωf Ωg D E = some r)
    (hE : ∀ H Ω' A E', H.length = fs.length → prsLoop k (G0 :: G1 :: gs) H Ωg Ω' A E' = some r → E' = 0) :
    ∃ H Ω' A, prsLoop k (G0 :: G1 :: gs) H Ωg Ω' A 0 = some r ∧ H.length = fs.length ∧
      (A : Int) = ((G0 : Int) - Ωg) ^ 2 ∧ (dec Ω' H).headD 0 ≠ 0 ∧
      ∀ fuel, normalResultantGo (fuel + 1) initial (dec Ωf (F0 :: F1 :: fs)) (dec Ωg (G0 :: G1 :: gs)) =
        nextOrStop fuel (dec Ωg (G0 :: G1 :: gs)) (dec Ω' H) := by
  obtain ⟨H, Ω', A, err, heq, hHlen, hA, hsem⟩ := stepA_spec (prsLoop k) F0 F1 G0 G1 fs gs Ωf Ωg D E hlen hfs
  rw [prsLoop_succ, heq] at hrun
  have hE0 := hE H Ω' A (E + err) hHlen hrun
  have herr : err = 0 := by omega
  have hEz : E + err = 0 := hE0
  rw [hEz] at hrun
  have hDpos : 0 < D := by
    rcases hD with ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · have : (0 : Int) < ((F0 : Int) - Ωf) ^ 2 := by
        rw [int_sq]; exact int_sq_pos _ hf0
      omega
  obtain ⟨hc, hh0, hdiv, hHeq⟩ := hsem hDpos herr
  refine ⟨H, Ω', A, hrun, hHlen, by rw [hA, int_sq], hh0, ?_⟩
  intro fuel
  generalize hR : row2 ((G0 : Int) - Ωg) ((F0 : Int) - Ωf)
      (((G0 : Int) - Ωg) * ((F1 : Int) - Ωf) - ((F0 : Int) - Ωf) * ((G1 : Int) - Ωg))
      (dec Ωf fs) ((G1 : Int) - Ωg) (dec Ωg gs) = R at hdiv hHeq
  have hR0 : R.headD 0 ≠ 0 := by
    intro h0
    apply hh0
    rw [hHeq]
    cases R with
    | nil => rfl
    | cons r0 rs => simp at h0 ⊢; rw [h0]; simp
  have hpr : pseudoRemainder (dec Ωf (F0 :: F1 :: fs)) (dec Ωg (G0 :: G1 :: gs)) = some R := by
    rw [dec_cons, dec_cons, dec_cons, dec_cons, ← hR]
    exact pseudoRemainder_normal _ _ _ _ _ _ hf0 hg0 hc (by simp [dec_length, hlen]) (by rw [hR]; exact hR0)
  apply nrg_step fuel initial _ _ _ R hpr _ hh0 (by simp [dec_length, hHlen, hlen])
  rcases hD with ⟨hi, hD1⟩ | ⟨hi, hD2⟩
  · subst hi; subst hD1
    rw [hHeq]
    simp
  · subst hi
    simp only [Bool.false_eq_true, if_false, dec_cons, List.headD_cons]
    rw [hHeq, ← hD2]
    exact exactDivide_ok _ (by omega) R hdiv

theorem nextOrStop_long (fuel : Nat) (g h : List Int) (hlen : 2 ≤ h.length) :
    nextOrStop fuel g h = normalResultantGo fuel false g h := by
  match h, hlen with
  | _ :: _ :: _, _ => rfl

theorem prs_main : ∀ (k : Nat) (F G : List Nat) (Ωf Ωg D E : Nat) (initial : Bool) (r : Int),
    G.length = k + 2 → F.length = G.length + 1 → G.length ≤ 25 →
    (dec Ωf F).headD 0 ≠ 0 → (dec Ωg G).headD 0 ≠ 0 →
    (initial = true ∧ D = 1 ∨ initial = false ∧ (D : Int) = (dec Ωf F).headD 0 ^ 2) →
    prsLoop (k + 1) F G Ωf Ωg D E = some r →
    ∀ fuel, k + 1 ≤ fuel → normalResultantGo (fuel + 1) initial (dec Ωf F) (dec Ωg G) = some r := by
  intro k
  induction k with
  | zero =>
    intro F G Ωf Ωg D E initial r hG hF hG25 hf0 hg0 hD hrun fuel _
    obtain ⟨G0, G1, gs, rfl⟩ := two_cons G (by omega)
    obtain ⟨F0, F1, fs, rfl⟩ := two_cons F (by omega)
    · simp only [List.length_cons] at hF hG hG25
      obtain ⟨H, Ω', A, hrun', hHlen, _, _, hnrg⟩ := prs_step 0 F0 F1 G0 G1 fs gs Ωf Ωg D E initial r
        (by omega) (by omega) (by simpa [dec] using hf0) (by simpa [dec] using hg0)
        (by simpa [dec] using hD) hrun
        (fun H Ω' A E' hl h => prsLoop_E 0 (G0 :: G1 :: gs) H Ωg Ω' A E' r (by omega) (by simp; omega)
          (by omega) h)
      rw [hnrg]
      have hH1 : H.length = 1 := by omega
      obtain ⟨H0, rfl⟩ : ∃ H0, H = [H0] := by
        match H, hH1 with
        | [H0], _ => exact ⟨H0, rfl⟩
      have : prsLoop 0 (G0 :: G1 :: gs) [H0] Ωg Ω' A 0 = some (Int.subNatNat H0 Ω') := rfl
      rw [this] at hrun'
      cases hrun'
      rw [Int.subNatNat_eq_coe]
      rfl
  | succ k ih =>
    intro F G Ωf Ωg D E initial r hG hF hG25 hf0 hg0 hD hrun fuel hfuel
    obtain ⟨G0, G1, gs, rfl⟩ := two_cons G (by omega)
    obtain ⟨F0, F1, fs, rfl⟩ := two_cons F (by omega)
    · simp only [List.length_cons] at hF hG hG25
      obtain ⟨H, Ω', A, hrun', hHlen, hA, hh0, hnrg⟩ := prs_step (k + 1) F0 F1 G0 G1 fs gs Ωf Ωg D E
        initial r (by omega) (by omega) (by simpa [dec] using hf0) (by simpa [dec] using hg0)
        (by simpa [dec] using hD) hrun
        (fun H Ω' A E' hl h => prsLoop_E (k + 1) (G0 :: G1 :: gs) H Ωg Ω' A E' r (by omega) (by simp; omega)
          (by omega) h)
      rw [hnrg, nextOrStop_long _ _ _ (by rw [dec_length]; omega)]
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      exact ih (G0 :: G1 :: gs) H Ωg Ω' A 0 false r (by omega) (by simp; omega) (by omega) hg0 hh0
        (Or.inr ⟨rfl, by simpa [dec] using hA⟩) hrun' fuel' (by omega)

/-! ## Proofs: derivative -/

theorem derivLoop_eq (Ω : Nat) : ∀ (m i : Nat) (l : List Nat), m ≤ l.length → i + m ≤ 24 →
    dec (24 * Ω) (derivLoop Ω m i l) =
      (List.range m).map (fun j => Int.ofNat (24 - (i + j)) * (dec Ω l).getD j 0) := by
  intro m
  induction m with
  | zero => intro i l _ _; rfl
  | succ m ih =>
    intro i l hl hi
    match l, hl with
    | x :: xs, hl =>
      show dec (24 * Ω) (((24 - i) * x + i * Ω) :: derivLoop Ω m (i + 1) xs) = _
      rw [dec_cons, ih (i + 1) xs (by simp at hl; omega) (by omega), List.range_succ_eq_map,
        List.map_cons, List.map_map]
      congr 1
      · simp only [Nat.add_zero, dec_cons, List.getD_cons_zero, Int.ofNat_eq_natCast]
        rw [Int.ofNat_sub (by omega : i ≤ 24)]
        push_cast
        grind
      · apply List.map_congr_left
        intro j _
        simp only [Function.comp, Nat.succ_eq_add_one, dec_cons, List.getD_cons_succ]
        congr 3
        omega

theorem dec_derivLoop (Ω : Nat) (P : List Nat) (hP : P.length = 25) :
    dec (24 * Ω) (derivLoop Ω 24 0 P) = derivHL (dec Ω P) := by
  rw [derivLoop_eq Ω 24 0 P (by omega) (by omega)]
  unfold derivHL
  rw [dec_length, hP]
  simp

/-! ## Proofs: assembling the discriminant -/

theorem coefficientsFrom_length : ∀ (count k index state : Nat),
    (coefficientsFrom count k index state).length = count := by
  intro count
  induction count with
  | zero => intro k index state; rfl
  | succ c ih =>
    intro k index state
    rw [coefficientsFrom.eq_2]
    rcases h : collectCoeffWord ((coefficientWidth k index + 63) / 64) 0 state with ⟨word, st⟩
    simp [ih]

theorem polyOf_length (n : Nat) : (polyOf n).length = 25 := by
  unfold polyOf
  simp [coefficientsFrom_length]

theorem fastDisc_sound (n : Nat) (r : Int) (h : fastDisc n = some r) : discSpec n = r := by
  have hP := genOff_eq n
  have hPlen : (genOff n).length = 25 := by
    rw [← dec_length (2 ^ (kbitsF n - 1)), hP, polyOf_length]
  have hΩ : omegaOf n = 2 ^ (kbitsF n - 1) := rfl
  have hD0 := dec_derivLoop (2 ^ (kbitsF n - 1)) (genOff n) hPlen
  have hD : dec (24 * 2 ^ (kbitsF n - 1)) (derivLoop (2 ^ (kbitsF n - 1)) 24 0 (genOff n)) =
      derivHL (polyOf n) := by rw [hD0, hP]
  have hDlen : (derivLoop (2 ^ (kbitsF n - 1)) 24 0 (genOff n)).length = 24 := by
    rw [← dec_length (24 * 2 ^ (kbitsF n - 1)), hD]
    unfold derivHL
    simp [polyOf_length]
  -- heads
  obtain ⟨P1, Ps, hPeq⟩ : ∃ P1 Ps, genOff n = (2 ^ (kbitsF n - 1) + 1) :: P1 :: Ps := by
    have : genOff n = (2 ^ (kbitsF n - 1) + 1) ::
        coeffsLoop (kbitsF n) (2 ^ (kbitsF n - 1)) 24 1 (seedF n) := rfl
    rw [this] at hPlen ⊢
    match coeffsLoop (kbitsF n) (2 ^ (kbitsF n - 1)) 24 1 (seedF n), hPlen with
    | P1 :: Ps, _ => exact ⟨P1, Ps, rfl⟩
  have hf0 : (dec (2 ^ (kbitsF n - 1)) (genOff n)).headD 0 ≠ 0 := by
    rw [hPeq]; simp [dec]; omega
  have hg0 : (dec (24 * 2 ^ (kbitsF n - 1)) (derivLoop (2 ^ (kbitsF n - 1)) 24 0 (genOff n))).headD 0 ≠ 0 := by
    rw [hPeq]
    show (dec (24 * 2 ^ (kbitsF n - 1)) (((24 - 0) * (2 ^ (kbitsF n - 1) + 1) + 0 * 2 ^ (kbitsF n - 1)) ::
      derivLoop (2 ^ (kbitsF n - 1)) 23 (0 + 1) (P1 :: Ps))).headD 0 ≠ 0
    simp [dec]
    omega
  have hmain := prs_main 22 (genOff n) (derivLoop (2 ^ (kbitsF n - 1)) 24 0 (genOff n))
    (2 ^ (kbitsF n - 1)) (24 * 2 ^ (kbitsF n - 1)) 1 0 true r (by omega) (by omega) (by omega)
    hf0 hg0 (Or.inl ⟨rfl, rfl⟩) h 24 (by omega)
  rw [hP, hD] at hmain
  -- the specification
  have hpl := polyOf_length n
  have hnr : normalResultant (polyOf n) (derivHL (polyOf n)) = some r := by
    have hdlen : (derivHL (polyOf n)).length = 24 := by rw [← hD, dec_length, hDlen]
    have hd0 : (derivHL (polyOf n)).headD 0 ≠ 0 := by rw [← hD]; exact hg0
    have hp0 : (polyOf n).headD 0 ≠ 0 := by rw [← hP]; exact hf0
    generalize derivHL (polyOf n) = dd at hdlen hd0 hmain ⊢
    generalize polyOf n = pp at hpl hp0 hmain ⊢
    obtain ⟨p0, ps, rfl⟩ : ∃ p0 ps, pp = p0 :: ps := by
      cases pp with
      | nil => simp at hpl
      | cons p0 ps => exact ⟨p0, ps, rfl⟩
    obtain ⟨d0, ds, rfl⟩ : ∃ d0 ds, dd = d0 :: ds := by
      cases dd with
      | nil => simp at hdlen
      | cons d0 ds => exact ⟨d0, ds, rfl⟩
    simp only [List.headD_cons] at hp0 hd0
    simp only [List.length_cons] at hpl hdlen
    unfold normalResultant
    simp only [trimLeading_cons _ hp0, trimLeading_cons _ hd0, List.length_cons, List.isEmpty_cons,
      hpl, hdlen]
    simpa using hmain
  unfold discSpec discriminantFromPoly resultantFromPoly
  dsimp only
  rw [hnr, hpl]
  simp

theorem impl_correct : ∀ n, impl n = discSpec n := by
  intro n
  unfold impl
  cases h : fastDisc n with
  | none => rfl
  | some r => exact (fastDisc_sound n r h).symm

end Submission
