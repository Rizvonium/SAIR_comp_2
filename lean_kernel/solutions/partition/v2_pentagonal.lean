import Spec

/-!
# Partition numbers via Euler's pentagonal number theorem

* `fast n` (used for `n ≤ 39`): one big-number division by the in-kernel-computed reversed
  pentagonal polynomial `F` (Horner form, ~14 primitive ops), then a lane mask.  Its correctness
  for `n ≤ 39` is a finite, kernel-checked verification against the general algorithm.
* `slow n` (used for `n ≥ 40`, and as the reference): a fully proven packed-polynomial DP — the row
  `(partAux k 0..n)` lives in one `Nat` with `2n+1`-bit lanes; each part size multiplies by a
  closed-form geometric series and truncates (bound `partAux k m ≤ 2^(k+m)` keeps lanes exact).
-/

namespace Submission

/-! ## Computation (raw kernel primitives) -/

/-- One DP step for part size `c`: multiply the packed row `X` by
`G = Σ_{j ≤ n/c} 2^(W*c*j) = (2^(W*c*(n/c+1)) - 1) / (2^(W*c) - 1)` and truncate mod `M`. -/
def step (W n M c X : Nat) : Nat :=
  Nat.mod
    (Nat.mul X
      (Nat.div
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (Nat.mul W c) (Nat.add (Nat.div n c) (nat_lit 1))))
          (nat_lit 1))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul W c)) (nat_lit 1))))
    M

/-- `rowLoop W n M k`: the packed row after processing part sizes `1, …, k`. -/
def rowLoop (W n M : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun k X => step W n M (Nat.add k (nat_lit 1)) X) k

def slow (n : Nat) : Nat :=
  let W := Nat.add (Nat.add n n) (nat_lit 1)
  Nat.shiftRight (rowLoop W n (Nat.shiftLeft (nat_lit 1) (Nat.mul W (Nat.add n (nat_lit 1)))) n)
    (Nat.mul W n)

/-! ## Packed numbers -/

/-- `pk W f L = Σ_{i < L} f i * 2^(W*i)`. -/
def pk (W : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | L + 1 => pk W f L + f L * 2 ^ (W * L)

theorem pk_zero (W : Nat) (f : Nat → Nat) : pk W f 0 = 0 := rfl
theorem pk_succ (W : Nat) (f : Nat → Nat) (L : Nat) :
    pk W f (L + 1) = pk W f L + f L * 2 ^ (W * L) := rfl

theorem pk_congr (W : Nat) {f g : Nat → Nat} : ∀ L, (∀ i, i < L → f i = g i) → pk W f L = pk W g L
  | 0, _ => rfl
  | L + 1, h => by
    rw [pk_succ, pk_succ, pk_congr W L (fun i hi => h i (by omega)), h L (by omega)]

theorem pk_add (W : Nat) (f g : Nat → Nat) :
    ∀ L, pk W f L + pk W g L = pk W (fun i => f i + g i) L
  | 0 => rfl
  | L + 1 => by
    rw [pk_succ, pk_succ, pk_succ, ← pk_add W f g L, Nat.add_mul]
    ac_rfl

theorem pk_const_zero (W : Nat) : ∀ L, pk W (fun _ => 0) L = 0
  | 0 => rfl
  | L + 1 => by rw [pk_succ, pk_const_zero W L]; simp

theorem pk_lt (W : Nat) (f : Nat → Nat) :
    ∀ L, (∀ i, i < L → f i < 2 ^ W) → pk W f L < 2 ^ (W * L)
  | 0, _ => by simp [pk_zero]
  | L + 1, h => by
    rw [pk_succ]
    have h1 := pk_lt W f L (fun i hi => h i (by omega))
    have h2 : f L + 1 ≤ 2 ^ W := h L (by omega)
    have h3 : (f L + 1) * 2 ^ (W * L) ≤ 2 ^ W * 2 ^ (W * L) := Nat.mul_le_mul_right _ h2
    have h4 : 2 ^ (W * (L + 1)) = 2 ^ W * 2 ^ (W * L) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [h4]
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

theorem pk_shift (W c : Nat) (f : Nat → Nat) :
    ∀ L, 2 ^ (W * c) * pk W f L = pk W (fun i => if c ≤ i then f (i - c) else 0) (L + c)
  | 0 => by
    rw [pk_zero, Nat.mul_zero, Nat.zero_add,
      pk_congr W (L := c) (g := fun _ => 0) (fun i hi => by simp; omega), pk_const_zero]
  | L + 1 => by
    rw [pk_succ, Nat.mul_add, pk_shift W c f L, show L + 1 + c = (L + c) + 1 by omega, pk_succ]
    congr 1
    simp only [show c ≤ L + c from Nat.le_add_left c L, if_true, show L + c - c = L by omega]
    rw [Nat.mul_add W L c, Nat.pow_add]
    ac_rfl

theorem pk_mod (W : Nat) (f : Nat → Nat) (L : Nat) :
    ∀ t, pk W f (L + t) % 2 ^ (W * L) = pk W f L % 2 ^ (W * L)
  | 0 => rfl
  | t + 1 => by
    rw [show L + (t + 1) = (L + t) + 1 by omega, pk_succ, Nat.mul_add W L t, Nat.pow_add,
      show f (L + t) * (2 ^ (W * L) * 2 ^ (W * t)) = 2 ^ (W * L) * (f (L + t) * 2 ^ (W * t)) by ac_rfl,
      Nat.add_mul_mod_self_left, pk_mod W f L t]

theorem pk_div (W : Nat) (f : Nat → Nat) (L : Nat) (h : pk W f L < 2 ^ (W * L)) :
    pk W f (L + 1) / 2 ^ (W * L) = f L := by
  rw [pk_succ, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt h, Nat.zero_add]

/-! ## The recurrence for `partAux` -/

theorem foldl_add (l : List Nat) : ∀ a, l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l with
  | nil => intro a; rfl
  | cons x xs ih =>
    intro a
    rw [List.foldl_cons, List.foldl_cons, ih (a + x), ih (0 + x)]
    omega

theorem partAux_succ (k m : Nat) :
    partAux (k + 1) m = partAux k m + (if k + 1 ≤ m then partAux (k + 1) (m - (k + 1)) else 0) := by
  rw [partAux]
  split
  · next h =>
    rw [partAux, Nat.div_eq_sub_div (by omega) h, List.range_succ_eq_map, List.map_cons,
      List.foldl_cons, foldl_add, List.map_map]
    simp only [Nat.zero_mul, Nat.sub_zero, Nat.zero_add]
    congr 2
    apply List.map_congr_left
    intro j _
    simp only [Function.comp, Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
    congr 1
    omega
  · next h =>
    rw [Nat.div_eq_of_lt (by omega)]
    simp

theorem partAux_zero_left (m : Nat) : partAux 0 m = if m = 0 then 1 else 0 := by
  cases m <;> simp [partAux]

theorem partAux_le : ∀ k m, partAux k m ≤ 2 ^ (k + m)
  | 0, m => by
    rw [partAux_zero_left]
    split
    · exact Nat.one_le_two_pow
    · exact Nat.zero_le _
  | k + 1, m => by
    rw [partAux_succ]
    have h1 := partAux_le k m
    split
    · next h =>
      have h2 := partAux_le (k + 1) (m - (k + 1))
      have h3 : 2 ^ (k + 1 + (m - (k + 1))) ≤ 2 ^ (k + m) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : 2 ^ (k + 1 + m) = 2 ^ (k + m) + 2 ^ (k + m) := by
        rw [show k + 1 + m = (k + m) + 1 by omega, Nat.pow_succ]; omega
      omega
    · have h4 : 2 ^ (k + m) ≤ 2 ^ (k + 1 + m) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
termination_by k m => (k, m)


/-! ## One DP step -/

/-- Geometric series in Horner form: `geo P t = Σ_{j < t} P^j`. -/
def geo (P : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => 1 + P * geo P t

theorem geo_mul (P : Nat) (hP : 1 ≤ P) : ∀ t, (P - 1) * geo P t = P ^ t - 1
  | 0 => by simp [geo]
  | t + 1 => by
    have ih := geo_mul P hP t
    have h1 : 1 ≤ P ^ t := Nat.one_le_pow _ _ hP
    have h2 : P * (P ^ t - 1) = P ^ (t + 1) - P := by
      rw [Nat.mul_sub_one, Nat.pow_succ, Nat.mul_comm]
    have h3 : P ≤ P ^ (t + 1) := by
      rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_left P (Nat.pos_of_ne_zero (by omega))
    show (P - 1) * (1 + P * geo P t) = P ^ (t + 1) - 1
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm (P - 1) P, Nat.mul_assoc, ih, h2]
    omega

theorem geo_eq (P : Nat) (hP : 2 ≤ P) (t : Nat) : geo P t = (P ^ t - 1) / (P - 1) := by
  symm
  apply Nat.div_eq_of_eq_mul_left (by omega)
  rw [← geo_mul P (by omega) t, Nat.mul_comm]

theorem mod_mul_congr (Y P Z M : Nat) : (Y + P * Z) % M = (Y + P * (Z % M)) % M := by
  have h : P * Z = P * (Z % M) + M * (P * (Z / M)) := by
    conv => lhs; rw [← Nat.mod_add_div Z M]
    rw [Nat.mul_add, Nat.mul_left_comm]
  rw [h, ← Nat.add_assoc, Nat.add_mul_mod_self_left]

theorem geo_iter (X Y P M : Nat) (h : X = Y + (P * X) % M) :
    ∀ t, X % M = (Y * geo P t + P ^ t * X) % M
  | 0 => by simp [geo]
  | t + 1 => by
    have ih := geo_iter X Y P M h t
    have e : Y * geo P (t + 1) + P ^ (t + 1) * X = Y + P * (Y * geo P t + P ^ t * X) := by
      show Y * (1 + P * geo P t) + P ^ (t + 1) * X = _
      rw [Nat.pow_succ, Nat.mul_add, Nat.mul_add, Nat.mul_one]
      ac_rfl
    rw [e, mod_mul_congr, ← ih, ← mod_mul_congr, ← Nat.add_mod_mod, ← h]

/-- The key identity behind one DP step:
`row_{k+1} = row_k + (2^(W(k+1)) * row_{k+1}) mod 2^(W(n+1))`. -/
theorem row_shift (W n k : Nat) (hb : ∀ m, m ≤ n → partAux (k + 1) m < 2 ^ W) :
    pk W (partAux (k + 1)) (n + 1)
      = pk W (partAux k) (n + 1) + (2 ^ (W * (k + 1)) * pk W (partAux (k + 1)) (n + 1)) % 2 ^ (W * (n + 1)) := by
  rw [pk_shift, pk_mod]
  have hlt : pk W (fun i => if k + 1 ≤ i then partAux (k + 1) (i - (k + 1)) else 0) (n + 1)
      < 2 ^ (W * (n + 1)) := by
    apply pk_lt
    intro i hi
    split
    · exact hb _ (by omega)
    · exact Nat.two_pow_pos _
  rw [Nat.mod_eq_of_lt hlt, pk_add]
  apply pk_congr
  intro i _
  exact partAux_succ k i

theorem row_step (W n k : Nat) (hW : 1 ≤ W) (hb : ∀ m, m ≤ n → partAux (k + 1) m < 2 ^ W) :
    (pk W (partAux k) (n + 1) *
        ((2 ^ (W * (k + 1) * (n / (k + 1) + 1)) - 1) / (2 ^ (W * (k + 1)) - 1))) % 2 ^ (W * (n + 1))
      = pk W (partAux (k + 1)) (n + 1) := by
  have hP : 2 ≤ 2 ^ (W * (k + 1)) := by
    have h1 : 1 ≤ W * (k + 1) := by
      have := Nat.mul_le_mul hW (show 1 ≤ k + 1 by omega)
      simpa using this
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (W * (k + 1)) := Nat.pow_le_pow_right (by omega) h1
  have hiter := geo_iter _ _ _ _ (row_shift W n k hb) (n / (k + 1) + 1)
  rw [Nat.pow_mul 2 (W * (k + 1)) (n / (k + 1) + 1), ← geo_eq _ hP]
  have hX : pk W (partAux (k + 1)) (n + 1) < 2 ^ (W * (n + 1)) :=
    pk_lt W _ _ (fun i hi => hb i (by omega))
  rw [Nat.mod_eq_of_lt hX] at hiter
  have hdvd : 2 ^ (W * (n + 1)) ∣ (2 ^ (W * (k + 1))) ^ (n / (k + 1) + 1) := by
    rw [← Nat.pow_mul]
    apply Nat.pow_dvd_pow
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    exact Nat.lt_mul_div_succ n (by omega)
  obtain ⟨d, hd⟩ := hdvd
  rw [hd, Nat.mul_assoc, Nat.add_mul_mod_self_left] at hiter
  exact hiter.symm

/-! ## The loop -/

theorem pk_delta (W : Nat) : ∀ L, pk W (fun i => if i = 0 then 1 else 0) (L + 1) = 1
  | 0 => by simp [pk_succ, pk_zero]
  | L + 1 => by
    rw [pk_succ, pk_delta W L]
    simp


theorem step_eq (W n M c X : Nat) :
    step W n M c X = (X * ((2 ^ (W * c * (n / c + 1)) - 1) / (2 ^ (W * c) - 1))) % M := by
  show (X * ((1 <<< (W * c * (n / c + 1)) - 1) / (1 <<< (W * c) - 1))) % M = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]

theorem rowLoop_succ (W n M k : Nat) : rowLoop W n M (k + 1) = step W n M (k + 1) (rowLoop W n M k) := rfl

theorem rowLoop_eq (n : Nat) : ∀ k, k ≤ n →
    rowLoop (2 * n + 1) n (2 ^ ((2 * n + 1) * (n + 1))) k = pk (2 * n + 1) (partAux k) (n + 1)
  | 0, _ => by
    show 1 = _
    rw [pk_congr (2 * n + 1) (g := fun i => if i = 0 then 1 else 0) (n + 1)
      (fun i _ => partAux_zero_left i)]
    exact (pk_delta _ n).symm
  | k + 1, hk => by
    rw [rowLoop_succ, rowLoop_eq n k (by omega), step_eq]
    apply row_step _ _ _ (by omega)
    intro m hm
    calc partAux (k + 1) m ≤ 2 ^ (k + 1 + m) := partAux_le _ _
      _ < 2 ^ (2 * n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)

theorem slow_correct : ∀ n, slow n = partitionSpec n := by
  intro n
  have h1 : slow n = rowLoop (2 * n + 1) n (2 ^ ((2 * n + 1) * (n + 1))) n >>> ((2 * n + 1) * n) := by
    show Nat.shiftRight (rowLoop (n + n + 1) n (1 <<< ((n + n + 1) * (n + 1))) n) ((n + n + 1) * n) = _
    rw [Nat.one_shiftLeft, show n + n + 1 = 2 * n + 1 by omega]
    rfl
  rw [h1, rowLoop_eq n n (Nat.le_refl n), Nat.shiftRight_eq_div_pow, pk_div]
  · rfl
  · apply pk_lt
    intro i hi
    calc partAux n i ≤ 2 ^ (n + i) := partAux_le _ _
      _ < 2 ^ (2 * n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)



/-! ## Fast path: Euler's pentagonal number theorem

`Π_{k≥1} (1 - x^k) = Σ_j (-1)^j x^(j(3j-1)/2)` (generalized pentagonal numbers 0,1,2,5,7,12,15,22,26,35,…).
With lanes of 16 bits (`B = 2^16`), the series truncated at degree 35 and reversed is
`F = B^35 E(1/B) = B^35 - B^34 - B^33 + B^30 + B^28 - B^23 - B^20 + B^13 + B^9 - 1`,
i.e. five sign-alternating blocks `B^a (B^d - 1)`, `d = 1,3,5,7,9`, written in Horner form
`F = B^13 (B^10 (B^7 (B^4 M1 - M3) + M5) - M7) + M9` with `M_d = B^d - 1 = M9 >>> 16(9-d)`.
Then `⌊B^(35+n) / F⌋ = Σ_{m ≤ n} p(m) B^(n-m)` (power-series inversion of `E`), whose lowest
lane is `p(n)`.  This is checked against the general algorithm for all `n ≤ 39` below; larger
`n` use the general algorithm. -/

/-- The reversed pentagonal polynomial `F`, built from the all-ones mask `m9 = 2^144 - 1`. -/
def pentF (m9 : Nat) : Nat :=
  Nat.add
    (Nat.shiftLeft
      (Nat.sub
        (Nat.shiftLeft
          (Nat.add
            (Nat.shiftLeft
              (Nat.sub (Nat.shiftLeft (Nat.shiftRight m9 (nat_lit 128)) (nat_lit 64))
                (Nat.shiftRight m9 (nat_lit 96)))
              (nat_lit 112))
            (Nat.shiftRight m9 (nat_lit 64)))
          (nat_lit 160))
        (Nat.shiftRight m9 (nat_lit 32)))
      (nat_lit 208))
    m9

/-- `p(n)` for `n ≤ 39`: lowest 16-bit lane of `⌊2^(16(35+n)) / F⌋`. -/
def fast (n : Nat) : Nat :=
  Nat.land (Nat.div (Nat.pow (nat_lit 65536) (Nat.add (nat_lit 35) n))
    (pentF (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 144)) (nat_lit 1)))) (nat_lit 65535)

def impl (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (fast n) (fun _ _ => slow n) (Nat.sub n (nat_lit 39))

theorem fast_eq_slow : ∀ n, n < 40 → fast n = slow n := by decide +kernel

theorem impl_correct : ∀ n, impl n = partitionSpec n := by
  intro n
  rcases Nat.lt_or_ge n 40 with h | h
  · have e : impl n = fast n := by
      show Nat.rec (motive := fun _ => Nat) (fast n) (fun _ _ => slow n) (n - 39) = fast n
      rw [show n - 39 = 0 by omega]
      rfl
    rw [e, fast_eq_slow n h, slow_correct]
  · have e : impl n = slow n := by
      show Nat.rec (motive := fun _ => Nat) (fast n) (fun _ _ => slow n) (n - 39) = slow n
      rw [show n - 39 = (n - 40) + 1 by omega]
    rw [e, slow_correct]

end Submission

