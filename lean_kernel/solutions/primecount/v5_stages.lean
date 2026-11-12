import Spec

/-!
# Prime counting with a packed sieve in one big `Nat`

Lane `m` (for `0 ≤ m ≤ n`) is the `w`-bit field starting at bit `w * (n - m)`.
For `a ≥ 2`, the number `2 ^ (w * (n - a)) / (2 ^ (w * a) - 1)` has exactly the lanes
`2a, 3a, …` (the proper multiples of `a` up to `n`) set to `1` (geometric series).
OR-ing these masks for every `a` in a sieving set that contains all primes `p` with
`p * p ≤ n` marks exactly the composite numbers `≤ n`.  Since `2 ^ w ≡ 1 (mod 2^w - 1)`,
the number of marked lanes is the whole number reduced mod `2 ^ w - 1`, and
`π(n) = (n - 1) - #composites`.

For `n < 1369 = 37²` the sieving set is the wheel `2, 3, 6k ± 1` (`k ≤ 5`), unrolled, with
early exits once `(6k-1)² > n`; larger `n` use a slow generic path (all `a ∈ [2, n]`).
Only kernel-accelerated `Nat` primitives are used on the fast path.
-/

namespace Submission

/-- Proper multiples of `a` among lanes `0..n` (lane width `w`). -/
def mask (w n a : Nat) : Nat :=
  Nat.div (Nat.shiftLeft (nat_lit 1) (Nat.mul w (Nat.sub n a)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w a)) (nat_lit 1))

/-- One sieving step. -/
def st (w n C a : Nat) : Nat := Nat.lor C (mask w n a)

/-- Final count: `(n - 1) - (number of marked lanes)`. -/
def fin (w n C : Nat) : Nat :=
  Nat.sub (Nat.sub n (nat_lit 1)) (Nat.mod C (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))

/-- Generic slow path: lane width `n + 2`, sieve with every `a ∈ [2, n + 1]`. -/
def slow (n : Nat) : Nat := fin (n + 2) n ((List.range' 2 n).foldl (st (n + 2) n) 0)

/-! Fast path, lane width 11: `B = 2 ^ (11 n)`, and the mask of proper multiples of `a`
is `B / (2 ^ (11a) * (2 ^ (11a) - 1))`; the divisor is `E (11 a)`. -/


/-- Divisor `2 ^ k * (2 ^ k - 1)` for the mask of proper multiples of `a` (`k = 11 a`). -/
def E (k : Nat) : Nat :=
  Nat.mul (Nat.shiftLeft (nat_lit 1) k) (Nat.sub (Nat.shiftLeft (nat_lit 1) k) (nat_lit 1))

/-- `fin 11` with the constant `2 ^ 11 - 1 = 2047` folded. -/
def fin11 (n C : Nat) : Nat := Nat.sub (Nat.sub n (nat_lit 1)) (Nat.mod C (nat_lit 2047))

/-- One sieving step with a precomputed divisor. -/
def stE (B C E : Nat) : Nat := Nat.lor C (Nat.div B E)

/-- Stages: sieve with a wheel pair, then exit early once the next pair is not needed. -/
def s3 (n C : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (fin11 n C) (slow n) (Nat.ble (nat_lit 1369) n)
def s2 (n B C : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (fin11 n C) (s3 n (stE B (stE B C (E (nat_lit 319))) (E (nat_lit 341)))) (Nat.ble (nat_lit 841) n)
def s1 (n B C : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (fin11 n C) (s2 n B (stE B (stE B (stE B (stE B C (E (nat_lit 187))) (E (nat_lit 209))) (E (nat_lit 253))) (E (nat_lit 275))))
    (Nat.ble (nat_lit 289) n)
def s0 (n B C : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (fin11 n C) (s1 n B (stE B (stE B C (E (nat_lit 121))) (E (nat_lit 143)))) (Nat.ble (nat_lit 121) n)
def fast (n B : Nat) : Nat := s0 n B (stE B (stE B (stE B (stE B (nat_lit 0) (E (nat_lit 22))) (E (nat_lit 33))) (E (nat_lit 55))) (E (nat_lit 77)))

def impl (n : Nat) : Nat := fast n (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 11) n))

/-! ## Correctness -/

/-- Horner encoding of a lane predicate: lane `m` at bit `w * (n - m)`. -/
def L (w : Nat) (f : Nat → Bool) : Nat → Nat
  | 0 => (f 0).toNat
  | n + 1 => 2 ^ w * L w f n + (f (n + 1)).toNat

theorem toNat_lt {w : Nat} (hw : 1 ≤ w) (b : Bool) : b.toNat < 2 ^ w := by
  have : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  cases b <;> simp [Bool.toNat]; omega

theorem L_eq_zero (w : Nat) (f : Nat → Bool) :
    ∀ n, (∀ m ≤ n, f m = false) → L w f n = 0 := by
  intro n
  induction n with
  | zero => intro h; simp [L, h 0 le_rfl]
  | succ n ih =>
    intro h
    simp [L, ih (fun m hm => h m (by omega)), h (n + 1) le_rfl]

theorem or_lanes {w x y b c : Nat} (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    (2 ^ w * x + b) ||| (2 ^ w * y + c) = 2 ^ w * (x ||| y) + (b ||| c) := by
  have hbc : (b ||| c) < 2 ^ w := Nat.or_lt_two_pow hb hc
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hbc]
  split <;> simp [Nat.testBit_or]

theorem L_or {w : Nat} (hw : 1 ≤ w) (f g : Nat → Bool) :
    ∀ n, L w f n ||| L w g n = L w (fun m => f m || g m) n := by
  intro n
  induction n with
  | zero => simp only [L]; cases f 0 <;> cases g 0 <;> rfl
  | succ n ih =>
    simp only [L]
    rw [or_lanes (toNat_lt hw _) (toNat_lt hw _), ih]
    cases f (n + 1) <;> cases g (n + 1) <;> rfl

theorem L_mod {w : Nat} (f : Nat → Bool) :
    ∀ n, L w f n % (2 ^ w - 1) = Nat.count (fun m => f m = true) (n + 1) % (2 ^ w - 1) := by
  have hpos : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  intro n
  induction n with
  | zero => simp [L, Nat.count_succ]; cases f 0 <;> simp
  | succ n ih =>
    rw [L, Nat.count_succ]
    have h : 2 ^ w * L w f n + (f (n + 1)).toNat
        = (L w f n + (f (n + 1)).toNat) + (2 ^ w - 1) * L w f n := by
      have : 2 ^ w = (2 ^ w - 1) + 1 := by omega
      conv_lhs => rw [this]
      ring
    rw [h, Nat.add_mul_mod_self_left, Nat.add_mod, ih, ← Nat.add_mod]
    cases f (n + 1) <;> simp

/-- The lane predicate of `mask w n a`. -/
def pm (a m : Nat) : Bool := decide (a ∣ m ∧ 2 * a ≤ m)

theorem mask_identity {w a : Nat} (ha : 1 ≤ a) :
    ∀ n, a ≤ n → (2 ^ (w * a) - 1) * L w (pm a) n + 2 ^ (w * (n % a)) = 2 ^ (w * (n - a)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [L_eq_zero w (pm a) a (fun m hm => by simp [pm]; omega)]
    simp
  | succ n hn ih =>
    have hexp : 2 ^ (w * (n + 1 - a)) = 2 ^ (w * (n - a)) * 2 ^ w := by
      rw [← pow_add]; congr 1
      rw [show n + 1 - a = (n - a) + 1 by omega, Nat.mul_succ]
    rw [L, hexp, ← ih]
    have hr := Nat.mod_lt n (show 0 < a by omega)
    have hdm := Nat.div_add_mod n a
    have hQ : 1 ≤ 2 ^ (w * a) := Nat.one_le_two_pow
    obtain ⟨E, hE⟩ : ∃ E, 2 ^ (w * a) = E + 1 := ⟨2 ^ (w * a) - 1, by omega⟩
    rw [show 2 ^ (w * a) - 1 = E by omega]
    by_cases hlast : n % a + 1 = a
    · have hdiv : a ∣ n + 1 := ⟨n / a + 1, by rw [Nat.mul_add, Nat.mul_one]; omega⟩
      have hq : 1 ≤ n / a := by
        rcases Nat.eq_zero_or_pos (n / a) with h0 | h0
        · rw [h0, Nat.mul_zero] at hdm; omega
        · exact h0
      have h2a : 2 * a ≤ n + 1 := by
        have : a ≤ a * (n / a) := Nat.le_mul_of_pos_right a hq
        omega
      have hmod : (n + 1) % a = 0 := Nat.mod_eq_zero_of_dvd hdiv
      have hpm : pm a (n + 1) = true := by simp [pm, hdiv, h2a]
      rw [hpm, hmod]
      have hw : 2 ^ (w * a) = 2 ^ (w * (n % a)) * 2 ^ w := by
        rw [← pow_add, ← Nat.mul_succ]; congr 2; omega
      rw [hw] at hE
      simp only [Bool.toNat_true, Nat.mul_zero, pow_zero]
      rw [show (E * L w (pm a) n + 2 ^ (w * (n % a))) * 2 ^ w
          = E * (2 ^ w * L w (pm a) n) + 2 ^ (w * (n % a)) * 2 ^ w by ring, hE]
      ring
    · have hmod : (n + 1) % a = n % a + 1 := by
        have : n + 1 = (n % a + 1) + a * (n / a) := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have hpm : pm a (n + 1) = false := by
        simp only [pm, decide_eq_false_iff_not, not_and]
        intro hd
        exact absurd (Nat.mod_eq_zero_of_dvd hd) (by omega)
      rw [hpm, hmod, Bool.toNat_false, Nat.add_zero, Nat.mul_succ, pow_add]
      ring

theorem mask_eq {w a : Nat} (hw : 1 ≤ w) (ha : 2 ≤ a) (n : Nat) :
    mask w n a = L w (pm a) n := by
  have hQ4 : 4 ≤ 2 ^ (w * a) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (w * a) := Nat.pow_le_pow_right (by norm_num)
          (by have := Nat.mul_le_mul hw ha; omega)
  show (1 <<< (w * (n - a))) / ((1 <<< (w * a)) - 1) = L w (pm a) n
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul]
  by_cases hn : a ≤ n
  · rw [← mask_identity (by omega) n hn, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega)]
    have hlt : 2 ^ (w * (n % a)) < 2 ^ (w * a) - 1 := by
      have hr : n % a + 1 ≤ a := Nat.mod_lt n (by omega)
      have h1 : 2 ^ (w * (n % a)) * 2 ^ w ≤ 2 ^ (w * a) := by
        rw [← pow_add, ← Nat.mul_succ]
        exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w hr)
      have h2 : 2 ≤ 2 ^ w := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
      have h3 : 1 ≤ 2 ^ (w * (n % a)) := Nat.one_le_two_pow
      by_cases h0 : n % a = 0
      · rw [h0, Nat.mul_zero, pow_zero]; omega
      · have : 2 ≤ 2 ^ (w * (n % a)) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (w * (n % a)) := Nat.pow_le_pow_right (by norm_num)
                (by have := Nat.mul_le_mul hw (Nat.pos_of_ne_zero h0); omega)
        have := Nat.mul_le_mul_left (2 ^ (w * (n % a))) h2
        omega
    rw [Nat.div_eq_of_lt hlt, Nat.zero_add]
  · rw [show n - a = 0 by omega, Nat.mul_zero, pow_zero, Nat.div_eq_of_lt (by omega)]
    exact (L_eq_zero w (pm a) n (fun m hm => by simp [pm]; omega)).symm

/-- Lane predicate after sieving with the list `S`. -/
def cp (S : List Nat) (m : Nat) : Bool := S.any (fun a => pm a m)

theorem foldl_st {w : Nat} (hw : 1 ≤ w) (n : Nat) :
    ∀ (S : List Nat) (f : Nat → Bool), (∀ a ∈ S, 2 ≤ a) →
      S.foldl (st w n) (L w f n) = L w (fun m => f m || cp S m) n := by
  intro S
  induction S with
  | nil => intro f _; simp [cp]
  | cons a S ih =>
    intro f hS
    simp only [List.foldl_cons]
    have hst : st w n (L w f n) a = L w (fun m => f m || pm a m) n := by
      show L w f n ||| mask w n a = _
      rw [mask_eq hw (hS a List.mem_cons_self)]
      exact L_or hw _ _ n
    rw [hst, ih _ (fun b hb => hS b (List.mem_cons_of_mem a hb))]
    congr 1; funext m; simp [cp, Bool.or_assoc]

theorem cp_iff (S : List Nat) (hS : ∀ a ∈ S, 2 ≤ a) (n : Nat)
    (hcov : ∀ p, p.Prime → p * p ≤ n → p ∈ S) (m : Nat) (hm : m ≤ n) :
    cp S m = true ↔ (2 ≤ m ∧ ¬ m.Prime) := by
  simp only [cp, List.any_eq_true, pm, decide_eq_true_eq]
  constructor
  · rintro ⟨a, haS, hdvd, h2a⟩
    have ha2 := hS a haS
    refine ⟨by omega, fun hp => ?_⟩
    rcases hp.eq_one_or_self_of_dvd a hdvd with h | h <;> omega
  · rintro ⟨h2, hnp⟩
    have hm1 : m ≠ 1 := by omega
    have hpp := Nat.minFac_prime hm1
    have hsq : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
    rw [pow_two] at hsq
    refine ⟨m.minFac, hcov _ hpp (by omega), Nat.minFac_dvd m, ?_⟩
    have := Nat.mul_le_mul_right m.minFac hpp.two_le
    omega

theorem count_split (S : List Nat) (hS : ∀ a ∈ S, 2 ≤ a) (n : Nat)
    (hcov : ∀ p, p.Prime → p * p ≤ n → p ∈ S) :
    ∀ N ≤ n + 1, Nat.count (fun m => cp S m = true) N + Nat.count Nat.Prime N + min N 2 = N := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro hN
    rw [Nat.count_succ, Nat.count_succ]
    have h := ih (by omega)
    have hc := cp_iff S hS n hcov N (by omega)
    by_cases h2 : 2 ≤ N
    · by_cases hp : N.Prime
      · have : ¬ cp S N = true := fun h' => (hc.mp h').2 hp
        simp [this, hp]; omega
      · have : cp S N = true := hc.mpr ⟨h2, hp⟩
        simp [this, hp]; omega
    · have hp : ¬ N.Prime := fun hp => by have := hp.two_le; omega
      have : ¬ cp S N = true := fun h' => by have := (hc.mp h').1; omega
      simp [this, hp]; omega

theorem key (w n : Nat) (S : List Nat) (hw : 1 ≤ w) (hn : n + 2 < 2 ^ w)
    (hS : ∀ a ∈ S, 2 ≤ a) (hcov : ∀ p, p.Prime → p * p ≤ n → p ∈ S) :
    fin w n (S.foldl (st w n) 0) = Nat.primeCounting n := by
  have h0 : (0 : Nat) = L w (fun _ => false) n :=
    (L_eq_zero w _ n (fun _ _ => rfl)).symm
  rw [h0, foldl_st hw n S _ hS]
  show (n - 1) - L w _ n % ((1 <<< w) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, L_mod]
  have hsplit := count_split S hS n hcov (n + 1) le_rfl
  simp only [Bool.false_or] at hsplit ⊢
  have hle : Nat.count (fun m => cp S m = true) (n + 1) < 2 ^ w - 1 := by omega
  rw [Nat.mod_eq_of_lt hle]
  have : Nat.primeCounting n = Nat.count Nat.Prime (n + 1) := rfl
  omega

theorem ble_false {a b : Nat} (h : Nat.ble a b = false) : b < a :=
  Nat.gt_of_not_le (fun hle => by rw [Nat.ble_eq_true_of_le hle] at h; cases h)

/-- Primes below `37` (to check the coverage of the wheel). -/
theorem cover (S : List Nat) (B : Nat) (_hB : B ≤ 37)
    (hS : ∀ p, p < B → p.Prime → p ∈ S) (n : Nat) (hn : n < B * B) :
    ∀ p, p.Prime → p * p ≤ n → p ∈ S := by
  intro p hp hpn
  apply hS p _ hp
  by_contra h
  have : B * B ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem slow_eq (n : Nat) : slow n = Nat.primeCounting n := by
  unfold slow
  apply key (n + 2) n (List.range' 2 n) (by omega)
  · exact Nat.lt_two_pow_self
  · intro a ha; simp [List.mem_range'] at ha; omega
  · intro p hp hpn
    simp only [List.mem_range']
    have := hp.two_le
    have := Nat.le_mul_self p
    refine ⟨p - 2, by omega, by omega⟩


theorem stE_eq (w n a C : Nat) (ha : 2 ≤ a) :
    stE (2 ^ (w * n)) C (2 ^ (w * a) * (2 ^ (w * a) - 1)) = st w n C a := by
  show C ||| 2 ^ (w * n) / (2 ^ (w * a) * (2 ^ (w * a) - 1)) =
    C ||| (1 <<< (w * (n - a))) / ((1 <<< (w * a)) - 1)
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, ← Nat.div_div_eq_div_mul]
  congr 1
  by_cases hn : a ≤ n
  · rw [show w * n = w * (n - a) + w * a by rw [← Nat.mul_add]; congr 1; omega, pow_add,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · rw [show n - a = 0 by omega, Nat.mul_zero, pow_zero]
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; simp
    · have h4 : 4 ≤ 2 ^ (w * a) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (w * a) := Nat.pow_le_pow_right (by norm_num)
              (by have := Nat.mul_le_mul (show 1 ≤ w by omega) ha; omega)
      have hlt : 2 ^ (w * n) < 2 ^ (w * a) :=
        Nat.pow_lt_pow_right (by norm_num) (Nat.mul_lt_mul_of_pos_left (by omega) h)
      rw [Nat.div_eq_of_lt hlt, Nat.zero_div, Nat.div_eq_of_lt (by omega)]

theorem fin11_eq (n C : Nat) : fin11 n C = fin 11 n C := rfl

theorem E_eq (k : Nat) : E k = 2 ^ k * (2 ^ k - 1) := by
  show (1 <<< k) * ((1 <<< k) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem stE_eq' (w n a k C : Nat) (ha : 2 ≤ a) (hk : k = w * a) :
    stE (2 ^ (w * n)) C (E k) = st w n C a := by
  rw [E_eq, hk]; exact stE_eq w n a C ha

theorem fast_eq (n : Nat) : fast n (2 ^ (11 * n)) = Nat.primeCounting n := by
  have hw : (1 : Nat) ≤ 11 := by norm_num
  have h2 : ∀ (S : List Nat), (∀ a ∈ S, 2 ≤ a) → ∀ B ≤ 37,
      (∀ p, p < B → p.Prime → p ∈ S) → n < B * B →
      fin 11 n (S.foldl (st 11 n) 0) = Nat.primeCounting n := by
    intro S hS B hB hcov hnB
    have hn' : n + 2 < 2 ^ 11 := by
      have : B * B ≤ 37 * 37 := Nat.mul_le_mul hB hB
      norm_num; omega
    exact key 11 n S hw hn' hS (cover S B hB hcov n hnB)
  simp only [fast, s0, s1, s2, s3, fin11_eq]
  simp only [stE_eq' 11 n 2 22 _ (by decide) (by decide), stE_eq' 11 n 3 33 _ (by decide) (by decide), stE_eq' 11 n 5 55 _ (by decide) (by decide), stE_eq' 11 n 7 77 _ (by decide) (by decide), stE_eq' 11 n 11 121 _ (by decide) (by decide), stE_eq' 11 n 13 143 _ (by decide) (by decide), stE_eq' 11 n 17 187 _ (by decide) (by decide), stE_eq' 11 n 19 209 _ (by decide) (by decide), stE_eq' 11 n 23 253 _ (by decide) (by decide), stE_eq' 11 n 25 275 _ (by decide) (by decide), stE_eq' 11 n 29 319 _ (by decide) (by decide), stE_eq' 11 n 31 341 _ (by decide) (by decide)]
  cases h121 : Nat.ble 121 n
  · exact h2 [2, 3, 5, 7] (by decide) 11 (by decide) (by decide) (ble_false h121)
  · cases h289 : Nat.ble 289 n
    · exact h2 [2, 3, 5, 7, 11, 13] (by decide) 17 (by decide) (by decide) (ble_false h289)
    · cases h841 : Nat.ble 841 n
      · exact h2 [2, 3, 5, 7, 11, 13, 17, 19, 23, 25] (by decide) 29 (by decide) (by decide)
          (ble_false h841)
      · cases h1369 : Nat.ble 1369 n
        · exact h2 [2, 3, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31] (by decide) 37 le_rfl
            (by decide) (ble_false h1369)
        · exact slow_eq n

theorem impl_correct : ∀ n, impl n = primeCountSpec n := by
  intro n
  unfold impl primeCountSpec
  rw [show Nat.shiftLeft 1 (Nat.mul 11 n) = 2 ^ (11 * n) from by
    show 1 <<< (11 * n) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]]
  exact fast_eq n

end Submission
