import Spec

/-!
# SHA-256 hash chain, written for cheap kernel reduction

The evaluated path uses only kernel-accelerated `Nat` primitives (`Nat.add`, `Nat.mul`,
`Nat.xor`, `Nat.land`, `Nat.shiftRight`, ...) on raw literals, so the kernel never
unfolds type-class arithmetic, and it never builds lists or structures:

* `impl` runs the chain as a `Nat.rec` loop in continuation-passing style; the eight
  digest words are plain arguments.
* `compressR` runs the 64 rounds as a `Nat.rec` loop whose state is the eight working
  words and a rolling 16-word message-schedule window.  The round constants are the
  spec's own list `K`, packed once into one number (`packK K`, a closed term the kernel
  evaluates once) and consumed 32 bits per round.
* Word-level identities (proved below): a rotation is read off `x * (2^32 + 1)` (two
  copies of `x` side by side) with a single shift; sums are masked once instead of after
  every `add32`; `Ch` and `Maj` use three-operation forms.
* Each compression forces its first output word before continuing, which keeps the
  kernel's evaluation depth bounded along long chains.
-/

namespace Submission

/-! ## Implementation -/

/-- `2^32 + 1`, built from the spec's mask `w32 = 2^32 - 1`. -/
local macro "DBL" : term => `(Nat.add w32 (nat_lit 2))

/-- `Σ₀ a` in the low 32 bits (the bits above are discarded by the final mask). -/
local macro "SIG0" a:term:max : term =>
  `(Nat.xor (Nat.xor (Nat.shiftRight (Nat.mul $a DBL) (nat_lit 2))
      (Nat.shiftRight (Nat.mul $a DBL) (nat_lit 13))) (Nat.shiftRight (Nat.mul $a DBL) (nat_lit 22)))

/-- `Σ₁ e` in the low 32 bits. -/
local macro "SIG1" e:term:max : term =>
  `(Nat.xor (Nat.xor (Nat.shiftRight (Nat.mul $e DBL) (nat_lit 6))
      (Nat.shiftRight (Nat.mul $e DBL) (nat_lit 11))) (Nat.shiftRight (Nat.mul $e DBL) (nat_lit 25)))

/-- `σ₀ x` in the low 32 bits. -/
local macro "SSIG0" x:term:max : term =>
  `(Nat.xor (Nat.xor (Nat.shiftRight (Nat.mul $x DBL) (nat_lit 7))
      (Nat.shiftRight (Nat.mul $x DBL) (nat_lit 18))) (Nat.shiftRight $x (nat_lit 3)))

/-- `σ₁ x` in the low 32 bits. -/
local macro "SSIG1" x:term:max : term =>
  `(Nat.xor (Nat.xor (Nat.shiftRight (Nat.mul $x DBL) (nat_lit 17))
      (Nat.shiftRight (Nat.mul $x DBL) (nat_lit 19))) (Nat.shiftRight $x (nat_lit 10)))

/-- `T₁ = h + K + W + Σ₁ e + Ch e f g`, unmasked (`kv` holds the round constant in its low
32 bits). -/
local macro "T1R" kv:term:max h:term:max e:term:max f:term:max g:term:max x:term:max : term =>
  `(Nat.add (Nat.add $h (Nat.add $kv $x))
      (Nat.add (SIG1 $e) (Nat.xor $g (Nat.land $e (Nat.xor $f $g)))))

/-- `T₂ = Σ₀ a + Maj a b c`, unmasked. -/
local macro "T2R" a:term:max b:term:max c:term:max : term =>
  `(Nat.add (SIG0 $a) (Nat.xor $b (Nat.land (Nat.xor $a $b) (Nat.xor $b $c))))

/-- Next schedule word `σ₁ x14 + x9 + σ₀ x1 + x0`, masked. -/
local macro "NWR" x0:term:max x1:term:max x9:term:max x14:term:max : term =>
  `(Nat.land (Nat.add (Nat.add (SSIG1 $x14) $x9) (Nat.add (SSIG0 $x1) $x0)) w32)

/-- `acc * 2^32 + w`. -/
local macro "SHL32ADD" acc:term:max w:term:max : term =>
  `(Nat.add (Nat.shiftLeft $acc (nat_lit 32)) $w)

/-- A continuation receiving the eight words of a digest. -/
abbrev Cont : Type := Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

/-- State of the round loop: packed round constants, eight working words, sixteen
schedule words, and the continuation for the resulting digest. -/
abbrev RS : Type := Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
  Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
  Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Cont → Nat

/-- Pass a digest on, after forcing its first word (`a &&& 0 = 0` is evaluated first). -/
def finish (a b c d e f g h : Nat) (k : Cont) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k a b c d e f g h) (fun _ _ => k a b c d e f g h)
    (Nat.land a (nat_lit 0))

/-- `n` SHA-256 rounds; each round also slides the schedule window by one word.  At the end
the chaining value `iv` is added. -/
def loopR (n : Nat) : RS :=
  Nat.rec (motive := fun _ => RS)
    (fun _ a b c d e f g h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k =>
      finish (Nat.land (Nat.add iv.a a) w32) (Nat.land (Nat.add iv.b b) w32)
        (Nat.land (Nat.add iv.c c) w32) (Nat.land (Nat.add iv.d d) w32)
        (Nat.land (Nat.add iv.e e) w32) (Nat.land (Nat.add iv.f f) w32)
        (Nat.land (Nat.add iv.g g) w32) (Nat.land (Nat.add iv.h h) w32) k)
    (fun _ ih kv a b c d e f g h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k =>
      ih (Nat.shiftRight kv (nat_lit 32))
        (Nat.land (Nat.add (T1R (Nat.land kv w32) h e f g x0) (T2R a b c)) w32) a b c
        (Nat.land (Nat.add d (T1R (Nat.land kv w32) h e f g x0)) w32) e f g
        x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (NWR x0 x1 x9 x14) k)
    n

/-- Round constants packed 32 bits apart, first constant lowest. -/
def packK (ks : List Nat) : Nat :=
  ks.foldr (fun k acc => SHL32ADD acc k) (nat_lit 0)

/-- One SHA-256 compression of the padded single-block message `m0 … m7`. -/
def compressR (m0 m1 m2 m3 m4 m5 m6 m7 : Nat) (k : Cont) : Nat :=
  loopR (nat_lit 64) (packK K) iv.a iv.b iv.c iv.d iv.e iv.f iv.g iv.h
    m0 m1 m2 m3 m4 m5 m6 m7 (Nat.shiftLeft (nat_lit 1) (nat_lit 31))
    (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 256) k

/-- Big-endian encoding of the eight digest words. -/
def encodeR (a b c d e f g h : Nat) : Nat :=
  SHL32ADD (SHL32ADD (SHL32ADD (SHL32ADD (SHL32ADD (SHL32ADD (SHL32ADD a b) c) d) e) f) g) h

/-- `t` chain steps, then encode. -/
def chain (t : Nat) : Cont :=
  Nat.rec (motive := fun _ => Cont) encodeR
    (fun _ ih a b c d e f g h => compressR a b c d e f g h ih) t

def impl (n : Nat) : Nat :=
  chain (Nat.shiftRight n (nat_lit 32))
    (seedDigest (sha256Seed n)).a (seedDigest (sha256Seed n)).b
    (seedDigest (sha256Seed n)).c (seedDigest (sha256Seed n)).d
    (seedDigest (sha256Seed n)).e (seedDigest (sha256Seed n)).f
    (seedDigest (sha256Seed n)).g (seedDigest (sha256Seed n)).h

/-! ## Correctness -/

/-! ### Word-level identities -/

theorem w32_eq : w32 = 2^32 - 1 := rfl

theorem land_w32 (x : Nat) : x &&& w32 = x % 2^32 := by
  rw [w32_eq, Nat.and_two_pow_sub_one_eq_mod]

theorem add32_eq (x y : Nat) : add32 x y = (x + y) % 2^32 := land_w32 _

theorem mod_lt32 (x : Nat) : x % 2^32 < 2^32 := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem add32_lt (x y : Nat) : add32 x y < 2^32 := by
  rw [add32_eq]; exact mod_lt32 _

theorem dbl_eq (x : Nat) : x * (w32 + 2) = 2^32 * x + x := by
  rw [show w32 + 2 = 2^32 + 1 from rfl, Nat.mul_add, Nat.mul_one, Nat.mul_comm]

/-- A rotation read off the doubled word. -/
theorem rotr_dbl (x r : Nat) (hx : x < 2^32) (hr : r ≤ 32) :
    (x * (w32 + 2)) >>> r % 2^32 = rotr32 x r := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [rotr32, land_w32, dbl_eq, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_mul_add x hx]
  by_cases hi : i < 32
  · by_cases h2 : r + i < 32
    · have h3 : ¬ (i ≥ 32 - r) := by omega
      simp [hi, h2, h3]
    · have h3 : i ≥ 32 - r := by omega
      have h4 : x.testBit (r + i) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      have h5 : i - (32 - r) = r + i - 32 := by omega
      simp [hi, h2, h3, h4, h5]
  · simp [hi]

theorem bigSigma0_eq (a : Nat) (ha : a < 2^32) :
    ((a * (w32 + 2)) >>> 2 ^^^ (a * (w32 + 2)) >>> 13 ^^^ (a * (w32 + 2)) >>> 22) % 2^32
      = bigSigma0 a := by
  rw [Nat.xor_mod_two_pow, Nat.xor_mod_two_pow, rotr_dbl a 2 ha (by decide),
    rotr_dbl a 13 ha (by decide), rotr_dbl a 22 ha (by decide)]
  rfl

theorem bigSigma1_eq (e : Nat) (he : e < 2^32) :
    ((e * (w32 + 2)) >>> 6 ^^^ (e * (w32 + 2)) >>> 11 ^^^ (e * (w32 + 2)) >>> 25) % 2^32
      = bigSigma1 e := by
  rw [Nat.xor_mod_two_pow, Nat.xor_mod_two_pow, rotr_dbl e 6 he (by decide),
    rotr_dbl e 11 he (by decide), rotr_dbl e 25 he (by decide)]
  rfl

theorem smallSigma0_eq (x : Nat) (hx : x < 2^32) :
    ((x * (w32 + 2)) >>> 7 ^^^ (x * (w32 + 2)) >>> 18 ^^^ x >>> 3) % 2^32 = smallSigma0 x := by
  rw [Nat.xor_mod_two_pow, Nat.xor_mod_two_pow, rotr_dbl x 7 hx (by decide),
    rotr_dbl x 18 hx (by decide), Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le x 3) hx)]
  rfl

theorem smallSigma1_eq (x : Nat) (hx : x < 2^32) :
    ((x * (w32 + 2)) >>> 17 ^^^ (x * (w32 + 2)) >>> 19 ^^^ x >>> 10) % 2^32 = smallSigma1 x := by
  rw [Nat.xor_mod_two_pow, Nat.xor_mod_two_pow, rotr_dbl x 17 hx (by decide),
    rotr_dbl x 19 hx (by decide), Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le x 10) hx)]
  rfl

theorem ch_eq (e f g : Nat) (he : e < 2^32) (hf : f < 2^32) (hg : g < 2^32) :
    g ^^^ (e &&& (f ^^^ g)) = ch e f g := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [ch, Nat.testBit_xor, Nat.testBit_and, w32_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 32
  · simp only [hi, decide_true]
    cases e.testBit i <;> cases f.testBit i <;> cases g.testBit i <;> rfl
  · have h : 2^32 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le he h),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hf h),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hg h)]
    simp

theorem maj_eq (a b c : Nat) : b ^^^ ((a ^^^ b) &&& (b ^^^ c)) = maj a b c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [maj, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

/-! ### One round -/

/-- All eight words of a digest are 32-bit. -/
def DOK (s : Digest) : Prop :=
  s.a < 2^32 ∧ s.b < 2^32 ∧ s.c < 2^32 ∧ s.d < 2^32 ∧
  s.e < 2^32 ∧ s.f < 2^32 ∧ s.g < 2^32 ∧ s.h < 2^32

theorem round_ok (s : Digest) (kt x : Nat) (hs : DOK s) : DOK (round s kt x) := by
  obtain ⟨ha, hb, hc, _, he, hf, hg, _⟩ := hs
  exact ⟨add32_lt _ _, ha, hb, hc, add32_lt _ _, he, hf, hg⟩

/-- `T₁` before masking (notation form of `T1R`). -/
def T1n (kv h e f g x : Nat) : Nat :=
  h + (kv + x) + (((e * (w32 + 2)) >>> 6 ^^^ (e * (w32 + 2)) >>> 11 ^^^ (e * (w32 + 2)) >>> 25)
    + (g ^^^ (e &&& (f ^^^ g))))

/-- `T₂` before masking (notation form of `T2R`). -/
def T2n (a b c : Nat) : Nat :=
  ((a * (w32 + 2)) >>> 2 ^^^ (a * (w32 + 2)) >>> 13 ^^^ (a * (w32 + 2)) >>> 22)
    + (b ^^^ ((a ^^^ b) &&& (b ^^^ c)))

theorem T1n_mod (kv kt x : Nat) (s : Digest) (hk : kv % 2^32 = kt % 2^32) (hs : DOK s) :
    T1n kv s.h s.e s.f s.g x % 2^32
      = (s.h + (bigSigma1 s.e + (ch s.e s.f s.g + (kt + x) % 2^32) % 2^32) % 2^32) % 2^32 := by
  obtain ⟨_, _, _, _, he, hf, hg, _⟩ := hs
  rw [T1n, ← bigSigma1_eq s.e he, ← ch_eq s.e s.f s.g he hf hg]
  generalize (s.e * (w32 + 2)) >>> 6 ^^^ (s.e * (w32 + 2)) >>> 11 ^^^ (s.e * (w32 + 2)) >>> 25 = S
  generalize s.g ^^^ (s.e &&& (s.f ^^^ s.g)) = C
  simp only [Nat.reducePow] at hk ⊢
  omega

theorem round_a (kv kt x : Nat) (s : Digest) (hk : kv % 2^32 = kt % 2^32) (hs : DOK s) :
    (T1n kv s.h s.e s.f s.g x + T2n s.a s.b s.c) &&& w32 = (round s kt x).a := by
  have h1 := T1n_mod kv kt x s hk hs
  obtain ⟨ha, _, _, _, _, _, _, _⟩ := hs
  show _ = add32 (add32 s.h (add32 (bigSigma1 s.e) (add32 (ch s.e s.f s.g) (add32 kt x))))
      (add32 (bigSigma0 s.a) (maj s.a s.b s.c))
  simp only [land_w32, add32_eq]
  rw [← bigSigma0_eq s.a ha, ← maj_eq s.a s.b s.c, ← h1, T2n]
  generalize T1n kv s.h s.e s.f s.g x = T
  generalize (s.a * (w32 + 2)) >>> 2 ^^^ (s.a * (w32 + 2)) >>> 13 ^^^ (s.a * (w32 + 2)) >>> 22 = S
  generalize s.b ^^^ ((s.a ^^^ s.b) &&& (s.b ^^^ s.c)) = M
  simp only [Nat.reducePow]
  omega

theorem round_e (kv kt x : Nat) (s : Digest) (hk : kv % 2^32 = kt % 2^32) (hs : DOK s) :
    (s.d + T1n kv s.h s.e s.f s.g x) &&& w32 = (round s kt x).e := by
  have h1 := T1n_mod kv kt x s hk hs
  show _ = add32 s.d (add32 s.h (add32 (bigSigma1 s.e) (add32 (ch s.e s.f s.g) (add32 kt x))))
  simp only [land_w32, add32_eq]
  rw [← h1]
  generalize T1n kv s.h s.e s.f s.g x = T
  simp only [Nat.reducePow]
  omega

/-! ### The schedule window -/

structure Window where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat
  x5 : Nat
  x6 : Nat
  x7 : Nat
  x8 : Nat
  x9 : Nat
  x10 : Nat
  x11 : Nat
  x12 : Nat
  x13 : Nat
  x14 : Nat
  x15 : Nat

def Window.toList (w : Window) : List Nat :=
  [w.x0, w.x1, w.x2, w.x3, w.x4, w.x5, w.x6, w.x7,
   w.x8, w.x9, w.x10, w.x11, w.x12, w.x13, w.x14, w.x15]

def Window.nextWord (w : Window) : Nat :=
  add32 (add32 (smallSigma1 w.x14) w.x9) (add32 (smallSigma0 w.x1) w.x0)

def Window.push (w : Window) (x : Nat) : Window :=
  ⟨w.x1, w.x2, w.x3, w.x4, w.x5, w.x6, w.x7, w.x8,
   w.x9, w.x10, w.x11, w.x12, w.x13, w.x14, w.x15, x⟩

def generate : Nat → Window → List Nat
  | 0, _ => []
  | k + 1, w =>
      let x := w.nextWord
      x :: generate k (w.push x)

/-- All sixteen words of a window are 32-bit. -/
def WOK (w : Window) : Prop :=
  w.x0 < 2^32 ∧ w.x1 < 2^32 ∧ w.x2 < 2^32 ∧ w.x3 < 2^32 ∧ w.x4 < 2^32 ∧ w.x5 < 2^32 ∧
  w.x6 < 2^32 ∧ w.x7 < 2^32 ∧ w.x8 < 2^32 ∧ w.x9 < 2^32 ∧ w.x10 < 2^32 ∧ w.x11 < 2^32 ∧
  w.x12 < 2^32 ∧ w.x13 < 2^32 ∧ w.x14 < 2^32 ∧ w.x15 < 2^32

theorem push_ok (w : Window) (hw : WOK w) : WOK (w.push w.nextWord) := by
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hw
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, add32_lt _ _⟩

/-- Notation form of `NWR`. -/
def NWn (x0 x1 x9 x14 : Nat) : Nat :=
  (((x14 * (w32 + 2)) >>> 17 ^^^ (x14 * (w32 + 2)) >>> 19 ^^^ x14 >>> 10) + x9
    + (((x1 * (w32 + 2)) >>> 7 ^^^ (x1 * (w32 + 2)) >>> 18 ^^^ x1 >>> 3) + x0)) &&& w32

theorem nextWord_eq (w : Window) (hw : WOK w) : NWn w.x0 w.x1 w.x9 w.x14 = w.nextWord := by
  obtain ⟨_, h1, _, _, _, _, _, _, _, _, _, _, _, _, h14, _⟩ := hw
  rw [NWn, Window.nextWord, land_w32, add32_eq, add32_eq, add32_eq,
    ← smallSigma1_eq _ h14, ← smallSigma0_eq _ h1]
  generalize (w.x14 * (w32 + 2)) >>> 17 ^^^ (w.x14 * (w32 + 2)) >>> 19 ^^^ w.x14 >>> 10 = A
  generalize (w.x1 * (w32 + 2)) >>> 7 ^^^ (w.x1 * (w32 + 2)) >>> 18 ^^^ w.x1 >>> 3 = B
  simp only [Nat.reducePow]
  omega

theorem stream_succ (w : Window) (n : Nat) :
    w.toList ++ generate (n + 1) w
      = w.x0 :: ((w.push w.nextWord).toList ++ generate n (w.push w.nextWord)) := by
  simp [Window.toList, generate, Window.push]

theorem length_generate : ∀ (n : Nat) (w : Window), (generate n w).length = n
  | 0, _ => rfl
  | n + 1, w => by simp [generate, length_generate n]

theorem generate_prefix : ∀ (m n : Nat) (w : Window), ∃ r, generate (m + n) w = generate m w ++ r
  | 0, n, w => ⟨generate n w, by simp [generate]⟩
  | m + 1, n, w => by
      obtain ⟨r, hr⟩ := generate_prefix m n (w.push w.nextWord)
      exact ⟨r, by rw [Nat.add_right_comm]; simp [generate, hr]⟩

theorem zip_append_of_le : ∀ (ks l1 l2 : List Nat), ks.length ≤ l1.length →
    ks.zip (l1 ++ l2) = ks.zip l1
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | k :: ks, x :: l1, l2, h => by
      simp only [List.cons_append, List.zip_cons_cons]
      rw [zip_append_of_le ks l1 l2 (by simpa using h)]

/-! The spec's growing schedule equals the window stream (as in the official example). -/

theorem drop_last16 (pre : List Nat) (w : Window) :
    (pre ++ w.toList).drop ((pre ++ w.toList).length - 16) = w.toList := by
  simp [Window.toList]

theorem nextWord_spec (w : Window) :
    add32 (add32 (smallSigma1 (w.toList.getD 14 0)) (w.toList.getD 9 0))
      (add32 (smallSigma0 (w.toList.getD 1 0)) (w.toList.getD 0 0)) =
      w.nextWord := by
  rfl

theorem append_push (pre : List Nat) (w : Window) :
    (pre ++ w.toList) ++ [w.nextWord] =
      (pre ++ [w.x0]) ++ (w.push w.nextWord).toList := by
  simp [Window.toList, Window.push]

theorem extend_eq : ∀ k pre w,
    extendW k (pre ++ w.toList) =
      pre ++ w.toList ++ generate k w
  | 0, pre, w => by
      simp [extendW, generate]
  | k + 1, pre, w => by
      rw [extendW, drop_last16, nextWord_spec, append_push]
      rw [extend_eq k (pre ++ [w.x0]) (w.push w.nextWord)]
      simp [generate, Window.toList, Window.push, List.append_assoc]

/-! ### The round loop -/

/-- Add the chaining value `iv` to the round result. -/
def addIV (f : Digest) : Digest :=
  ⟨add32 iv.a f.a, add32 iv.b f.b, add32 iv.c f.c, add32 iv.d f.d,
   add32 iv.e f.e, add32 iv.f f.f, add32 iv.g f.g, add32 iv.h f.h⟩

/-- Feed a digest to a continuation. -/
def pass (d : Digest) (k : Cont) : Nat := k d.a d.b d.c d.d d.e d.f d.g d.h

theorem finish_eq (a b c d e f g h : Nat) (k : Cont) :
    finish a b c d e f g h k = k a b c d e f g h := by
  show Nat.rec (motive := fun _ => Nat) (k a b c d e f g h) (fun _ _ => k a b c d e f g h)
    (a &&& 0) = _
  rw [Nat.and_zero]
  rfl

theorem packK_cons (kt : Nat) (ks : List Nat) : packK (kt :: ks) = kt + packK ks * 2^32 := by
  show (packK ks) <<< 32 + kt = _
  rw [Nat.shiftLeft_eq, Nat.add_comm]

theorem packK_mod (kt : Nat) (ks : List Nat) : packK (kt :: ks) % 2^32 = kt % 2^32 := by
  rw [packK_cons, Nat.add_mul_mod_self_right]

theorem packK_shr (kt : Nat) (ks : List Nat) (h : kt < 2^32) : packK (kt :: ks) >>> 32 = packK ks := by
  rw [packK_cons, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 32),
    Nat.div_eq_of_lt h, Nat.zero_add]

theorem rec_succ {C : Nat → Sort _} (z : C 0) (s : (n : Nat) → C n → C (n + 1)) (n : Nat) :
    Nat.rec (motive := C) z s (n + 1) = s n (Nat.rec (motive := C) z s n) := rfl

/-- One unfolding of the round loop, in raw form. -/
theorem loop_raw (n kv a b c d e f g h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat)
    (k : Cont) :
    loopR (n + 1) kv a b c d e f g h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k =
    loopR n (Nat.shiftRight kv (nat_lit 32))
        (Nat.land (Nat.add (T1R (Nat.land kv w32) h e f g x0) (T2R a b c)) w32) a b c
        (Nat.land (Nat.add d (T1R (Nat.land kv w32) h e f g x0)) w32) e f g
        x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (NWR x0 x1 x9 x14) k := by
  unfold loopR
  exact rfl

theorem raw_a (kv kt x : Nat) (s : Digest) (hk : kv % 2^32 = kt % 2^32) (hs : DOK s) :
    Nat.land (Nat.add (T1R kv s.h s.e s.f s.g x) (T2R s.a s.b s.c)) w32 = (round s kt x).a := by
  show (T1n kv s.h s.e s.f s.g x + T2n s.a s.b s.c) &&& w32 = _
  exact round_a kv kt x s hk hs

theorem raw_e (kv kt x : Nat) (s : Digest) (hk : kv % 2^32 = kt % 2^32) (hs : DOK s) :
    Nat.land (Nat.add s.d (T1R kv s.h s.e s.f s.g x)) w32 = (round s kt x).e := by
  show (s.d + T1n kv s.h s.e s.f s.g x) &&& w32 = _
  exact round_e kv kt x s hk hs

theorem raw_w (w : Window) (hw : WOK w) : (NWR w.x0 w.x1 w.x9 w.x14) = w.nextWord := by
  show NWn w.x0 w.x1 w.x9 w.x14 = _
  exact nextWord_eq w hw

theorem loop_succ (n kv kt : Nat) (s : Digest) (w : Window) (k : Cont)
    (hk : kv % 2^32 = kt % 2^32) (hs : DOK s) (hw : WOK w) :
    loopR (n + 1) kv s.a s.b s.c s.d s.e s.f s.g s.h
      w.x0 w.x1 w.x2 w.x3 w.x4 w.x5 w.x6 w.x7 w.x8 w.x9 w.x10 w.x11 w.x12 w.x13 w.x14 w.x15 k =
    loopR n (kv >>> 32)
      (round s kt w.x0).a s.a s.b s.c (round s kt w.x0).e s.e s.f s.g
      w.x1 w.x2 w.x3 w.x4 w.x5 w.x6 w.x7 w.x8 w.x9 w.x10 w.x11 w.x12 w.x13 w.x14 w.x15
      w.nextWord k := by
  have hk' : Nat.land kv w32 % 2^32 = kt % 2^32 := by
    show (kv &&& w32) % 2^32 = _
    rw [land_w32, Nat.mod_mod]
    exact hk
  rw [loop_raw, raw_a (Nat.land kv w32) kt w.x0 s hk' hs, raw_e (Nat.land kv w32) kt w.x0 s hk' hs,
    raw_w w hw]
  rfl

theorem loop_spec (k : Cont) : ∀ (ks : List Nat) (s : Digest) (w : Window),
    (∀ x ∈ ks, x < 2^32) → DOK s → WOK w →
    loopR ks.length (packK ks) s.a s.b s.c s.d s.e s.f s.g s.h
      w.x0 w.x1 w.x2 w.x3 w.x4 w.x5 w.x6 w.x7 w.x8 w.x9 w.x10 w.x11 w.x12 w.x13 w.x14 w.x15 k =
    pass (addIV (rounds (ks.zip (w.toList ++ generate ks.length w)) s)) k
  | [], s, w, _, _, _ => by
      show finish (add32 iv.a s.a) (add32 iv.b s.b) (add32 iv.c s.c) (add32 iv.d s.d)
        (add32 iv.e s.e) (add32 iv.f s.f) (add32 iv.g s.g) (add32 iv.h s.h) k = _
      rw [finish_eq]
      rfl
  | kt :: ks, s, w, hks, hs, hw => by
      have hkt : kt < 2^32 := hks kt (List.mem_cons_self ..)
      have ih := loop_spec k ks (round s kt w.x0) (w.push w.nextWord)
        (fun x hx => hks x (List.mem_cons_of_mem _ hx)) (round_ok s kt w.x0 hs) (push_ok w hw)
      rw [List.length_cons, loop_succ ks.length (packK (kt :: ks)) kt s w k
        (packK_mod kt ks) hs hw, packK_shr kt ks hkt, stream_succ]
      exact ih

/-! ### Compression, chain, encoding -/

theorem K_ok : ∀ x ∈ K, x < 2^32 := by decide

/-- The initial schedule window of a one-block message. -/
def W0 (d : Digest) : Window :=
  ⟨d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h, 0x80000000, 0, 0, 0, 0, 0, 0, 256⟩

theorem compress_spec (d : Digest) (hd : DOK d) (k : Cont) :
    compressR d.a d.b d.c d.d d.e d.f d.g d.h k = pass (sha256step d) k := by
  obtain ⟨ha, hb, hc, hd', he, hf, hg, hh⟩ := hd
  have h0 : (0 : Nat) < 2^32 := by decide
  have hw : WOK (W0 d) :=
    ⟨ha, hb, hc, hd', he, hf, hg, hh, (by decide : (0x80000000 : Nat) < 2^32), h0, h0, h0, h0,
      h0, h0, (by decide : (256 : Nat) < 2^32)⟩
  have hiv : DOK iv := ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩
  show loopR K.length (packK K) iv.a iv.b iv.c iv.d iv.e iv.f iv.g iv.h
    (W0 d).x0 (W0 d).x1 (W0 d).x2 (W0 d).x3 (W0 d).x4 (W0 d).x5 (W0 d).x6 (W0 d).x7
    (W0 d).x8 (W0 d).x9 (W0 d).x10 (W0 d).x11 (W0 d).x12 (W0 d).x13 (W0 d).x14 (W0 d).x15 k = _
  rw [loop_spec k K iv (W0 d) K_ok hiv hw]
  obtain ⟨r, hr⟩ := generate_prefix 48 16 (W0 d)
  have hsched : extendW 48 (W0 d).toList = (W0 d).toList ++ generate 48 (W0 d) := by
    simpa using extend_eq 48 [] (W0 d)
  have hzip : K.zip ((W0 d).toList ++ generate K.length (W0 d))
      = K.zip ((W0 d).toList ++ generate 48 (W0 d)) := by
    rw [show K.length = 48 + 16 from rfl, hr, ← List.append_assoc,
      zip_append_of_le K _ r (by simp [Window.toList, length_generate]; decide)]
  rw [hzip, ← hsched]
  rfl

theorem sha256step_ok (d : Digest) : DOK (sha256step d) :=
  ⟨add32_lt _ _, add32_lt _ _, add32_lt _ _, add32_lt _ _,
   add32_lt _ _, add32_lt _ _, add32_lt _ _, add32_lt _ _⟩

theorem encode_spec (d : Digest) :
    encodeR d.a d.b d.c d.d d.e d.f d.g d.h = encodeDigest d := by
  show ((((((d.a <<< 32 + d.b) <<< 32 + d.c) <<< 32 + d.d) <<< 32 + d.e) <<< 32 + d.f)
    <<< 32 + d.g) <<< 32 + d.h = _
  simp [encodeDigest, Nat.shiftLeft_eq]

theorem iter_zero (step : Digest → Digest) (d : Digest) : iterDigest step 0 d = d := rfl

theorem iter_succ (step : Digest → Digest) (t : Nat) (d : Digest) :
    iterDigest step (t + 1) d = iterDigest step t (step d) := rfl

theorem chain_spec : ∀ (t : Nat) (d : Digest), DOK d →
    chain t d.a d.b d.c d.d d.e d.f d.g d.h = encodeDigest (iterSha t d)
  | 0, d, _ => by
      have h : chain 0 d.a d.b d.c d.d d.e d.f d.g d.h = encodeR d.a d.b d.c d.d d.e d.f d.g d.h := by
        unfold chain
        exact rfl
      rw [h, encode_spec]
      exact congrArg encodeDigest (iter_zero sha256step d).symm
  | t + 1, d, hd => by
      have h : chain (t + 1) d.a d.b d.c d.d d.e d.f d.g d.h
          = compressR d.a d.b d.c d.d d.e d.f d.g d.h (chain t) := by
        unfold chain
        exact rfl
      have h2 : iterSha (t + 1) d = iterSha t (sha256step d) := iter_succ sha256step t d
      rw [h, compress_spec d hd, h2]
      exact chain_spec t (sha256step d) (sha256step_ok d)

theorem seed_ok (s : Nat) : DOK (seedDigest s) := by
  have h : ∀ x, seedStep32 x < 2^32 := fun x => by
    rw [seedStep32, land_w32]; exact mod_lt32 _
  exact ⟨h _, h _, h _, h _, h _, h _, h _, h _⟩

theorem impl_correct : ∀ n, impl n = sha256Spec n := by
  intro n
  unfold impl sha256Spec
  exact chain_spec (sha256Steps n) (seedDigest (sha256Seed n)) (seed_ok _)

end Submission
