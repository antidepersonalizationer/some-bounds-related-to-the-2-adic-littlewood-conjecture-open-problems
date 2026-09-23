import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import VV.Definitions
import VV.CylinderGeometry

/-!
# Problem 7: the Hausdorff-cover part of the argument

The finite-cover arguments in this file are Lean proofs with no `sorry`
and no added axioms. Their arithmetic/entropy inputs are explicit hypotheses
of these reusable reductions. `VV.BBEKFinal` supplies them internally and
exports `VV.problem7`; that final theorem depends on the one explicitly
admitted EL low-entropy core, which is theory rather than finite computation.

The source chat uses BBEK, Theorem 4.2, followed by a countable family of finite
continued-fraction dictionaries.  This file verifies the latter cover argument
in an arbitrary metric coding.  Its hypotheses record precisely the cylinder
diameter and dictionary-size estimates that the preceding argument must supply.
-/

open Filter Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology BigOperators

namespace VV.Problem7

/-- The exact real-number target from the paper, using the definitions of
continued-fraction digits in `VV.Definitions`. -/
def Statement : Prop := dimH VV.BExceptional = 0

/-! ## A quantifier step needed before the p-adic limit argument -/

/-- A fixed linear combination of convergent denominators cannot acquire
arbitrarily large powers of two, provided its ordinary approximation product
stays bounded and each fixed dyadic layer has the stated eventual lower bound.

The hypothesis fixes `h` before taking an eventual limit; the proof does not
interchange the two quantifiers.  The continued-fraction derivation of these
two hypotheses is a separate theoretical obligation. -/
theorem eventually_not_dvd_of_layer_lower_bounds
    (q : ℕ → ℕ) (err : ℕ → ℝ) (δ M : ℝ) (hδ : 0 < δ)
    (hbounded : ∀ᶠ n in atTop, (q n : ℝ) * err n ≤ M)
    (hlayers : ∀ h : ℕ, ∀ᶠ n in atTop,
      2 ^ h ∣ q n → δ ≤ (q n : ℝ) * err n / (2 : ℝ) ^ h) :
    ∃ h : ℕ, ∀ᶠ n in atTop, ¬ 2 ^ h ∣ q n := by
  obtain ⟨h, hh⟩ := exists_nat_gt (M / δ)
  have hpow : (h : ℝ) < (2 : ℝ) ^ h := by
    exact_mod_cast Nat.lt_two_pow_self
  have hlarge : M < δ * (2 : ℝ) ^ h := by
    have := (div_lt_iff₀ hδ).mp (hh.trans hpow)
    simpa only [mul_comm] using this
  refine ⟨h, ?_⟩
  filter_upwards [hbounded, hlayers h] with n hn hl
  intro hdvd
  have hlower := (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ h)).mp (hl hdvd)
  exact (hlarge.trans_le (hlower.trans hn)).false

section Covers

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Cover mass tends to zero when the number of cells is at most `m^n`,
their diameters are at most `r^n`, and `m * r^s < 1`. -/
theorem hausdorffMeasure_zero_of_geometric_covers
    (E : Set X) (s : ℝ) (hs : 0 ≤ s)
    (r : ℝ≥0∞) (hr : r < 1) (m : ℕ)
    (hm : (m : ℝ≥0∞) * r ^ s < 1)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (U : ∀ n, ι n → Set X)
    (hcard : ∀ n, Fintype.card (ι n) ≤ m ^ n)
    (hdiam : ∀ᶠ n in atTop, ∀ i, EMetric.diam (U n i) ≤ r ^ n)
    (hcover : ∀ᶠ n in atTop, E ⊆ ⋃ i, U n i) :
    hausdorffMeasure s E = 0 := by
  have hmass : ∀ᶠ n in atTop,
      (∑ i, EMetric.diam (U n i) ^ s) ≤
        ((m : ℝ≥0∞) * r ^ s) ^ n := by
    filter_upwards [hdiam] with n hn
    calc
      (∑ i, EMetric.diam (U n i) ^ s) ≤
          ∑ _i : ι n, (r ^ n) ^ s :=
        Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hn i) hs
      _ = (Fintype.card (ι n) : ℝ≥0∞) * (r ^ n) ^ s := by simp
      _ ≤ (m ^ n : ℕ) * (r ^ n) ^ s := by
        exact mul_le_mul_right' (by exact_mod_cast hcard n) _
      _ = ((m : ℝ≥0∞) * r ^ s) ^ n := by
        rw [Nat.cast_pow, mul_pow]
        congr 1
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          mul_comm (n : ℝ) s, ENNReal.rpow_mul, ENNReal.rpow_natCast]
  have hmass_zero : Tendsto (fun n => ∑ i, EMetric.diam (U n i) ^ s)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hm)
      (Eventually.of_forall fun _ => zero_le _) hmass
  have hle := hausdorffMeasure_le_liminf_sum s E (fun n => r ^ n)
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) U hdiam hcover
  rw [hmass_zero.liminf_eq] at hle
  exact le_antisymm hle (zero_le _)

/-- Vanishing Hausdorff measures in every positive dimension imply dimension zero. -/
theorem dimH_zero_of_all_positive_measures_zero (E : Set X)
    (h : ∀ s : ℝ≥0, 0 < s → hausdorffMeasure (s : ℝ) E = 0) :
    dimH E = 0 := by
  apply le_antisymm (dimH_le ?_) (zero_le _)
  intro s hs
  by_cases hz : s = 0
  · simp [hz]
  · have hzero := h s (pos_iff_ne_zero.mpr hz)
    rw [hzero] at hs
    exact False.elim (ENNReal.zero_ne_top hs)

/-- The dictionary can vary between points: use a countable union, separately
for every positive exponent.  No uniform dictionary is assumed. -/
theorem dimH_zero_of_countable_small_covers (E : Set X)
    {J : Type*} [Countable J]
    (pieces : ℝ≥0 → J → Set X)
    (hcover : ∀ s : ℝ≥0, 0 < s → E ⊆ ⋃ j, pieces s j)
    (hzero : ∀ s : ℝ≥0, 0 < s → ∀ j,
      hausdorffMeasure (s : ℝ) (pieces s j) = 0) :
    dimH E = 0 := by
  apply dimH_zero_of_all_positive_measures_zero E
  intro s hs
  apply measure_mono_null (hcover s hs)
  exact measure_iUnion_null (hzero s hs)

end Covers

section Dictionary

variable {X A : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A cylinder prescribing `n` consecutive blocks of length `L`, inside a
fixed domain (which may specify an integer part and a finite prefix). -/
def blockCylinder (domain : Set X) (digit : X → ℕ → A) (L n : ℕ)
    (word : Fin n → Fin L → A) : Set X :=
  {x | x ∈ domain ∧ ∀ j : Fin n, ∀ i : Fin L,
    digit x (j.val * L + i.val) = word j i}

/-- Every disjoint length-`L` block of the digit string belongs to `W`. -/
def allowedBlocks (domain : Set X) (digit : X → ℕ → A) (L : ℕ)
    (W : Finset (Fin L → A)) : Set X :=
  {x | x ∈ domain ∧ ∀ j : ℕ,
    (fun i : Fin L => digit x (j * L + i.val)) ∈ W}

omit [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem allowedBlocks_subset_cylinders
    (domain : Set X) (digit : X → ℕ → A) (L : ℕ)
    (W : Finset (Fin L → A)) (n : ℕ) :
    allowedBlocks domain digit L W ⊆
      ⋃ word : Fin n → W,
        blockCylinder domain digit L n (fun j => (word j).val) := by
  intro x hx
  let word : Fin n → W := fun j =>
    ⟨fun i => digit x (j.val * L + i.val), hx.2 j.val⟩
  apply mem_iUnion.mpr
  refine ⟨word, hx.1, ?_⟩
  intro j i
  rfl

/-- The analytic bridge used after a finite dictionary has been found.
There are exactly `W.card^n` choices of `n` blocks. -/
theorem hausdorffMeasure_allowedBlocks_zero
    (domain : Set X) (digit : X → ℕ → A) (L : ℕ)
    (W : Finset (Fin L → A))
    (s : ℝ) (hs : 0 ≤ s) (r : ℝ≥0∞) (hr : r < 1)
    (hsmall : (W.card : ℝ≥0∞) * r ^ s < 1)
    (hdiam : ∀ᶠ n in atTop, ∀ word : Fin n → W,
      EMetric.diam (blockCylinder domain digit L n (fun j => (word j).val)) ≤ r ^ n) :
    hausdorffMeasure s (allowedBlocks domain digit L W) = 0 := by
  classical
  apply hausdorffMeasure_zero_of_geometric_covers
    (allowedBlocks domain digit L W) s hs r hr W.card hsmall
    (fun n (word : Fin n → W) => blockCylinder domain digit L n (fun j => (word j).val))
  · intro n
    simp
  · exact hdiam
  · exact Eventually.of_forall (allowedBlocks_subset_cylinders domain digit L W)

end Dictionary

/-! ## Removing the finitely occurring words

This is an essential quantifier step: the cutoff may depend on the chosen
block length.  It need not be uniform in the block length or in the real
number being encoded.
-/

def RecurrentValue {A : Type*} (stream : ℕ → A) (a : A) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ stream n = a

theorem eventually_recurrent_value {A : Type*} [Finite A] (stream : ℕ → A) :
    ∀ᶠ n in atTop, RecurrentValue stream (stream n) := by
  classical
  have h : ∀ a : A, ∀ᶠ n in atTop,
      stream n = a → RecurrentValue stream a := by
    intro a
    by_cases ha : RecurrentValue stream a
    · exact Eventually.of_forall fun _ _ => ha
    · simp only [RecurrentValue, not_forall, not_exists, not_and] at ha
      obtain ⟨N, hN⟩ := ha
      refine eventually_atTop.mpr ⟨N, ?_⟩
      intro n hn heq
      exact False.elim (hN n hn heq)
  filter_upwards [eventually_all.mpr h] with n hn
  exact hn (stream n) rfl

def wordAt {A : Type*} (stream : ℕ → A) (L n : ℕ) : Fin L → A :=
  fun i => stream (n + i.val)

/-- For a fixed block length over a finite alphabet, after some point all
blocks belong to the recurrent dictionary. -/
theorem eventually_recurrent_words {A : Type*} [Finite A]
    (stream : ℕ → A) (L : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      RecurrentValue (wordAt stream L) (wordAt stream L n) :=
  eventually_atTop.mp (eventually_recurrent_value (wordAt stream L))

/-! ## An explicit dependency boundary for the real-number target -/

/-- A countable family of analytic presentations.  `domain` can fix an
integer part and any finite continued-fraction prefix.  The digits below are
the actual digits of the real number, with an allowed finite offset. -/
structure CFDictionaryPresentation where
  domain : Set ℝ
  offset : ℕ
  blockLength : ℕ
  dictionary : Finset (Fin blockLength → ℤ)

noncomputable def CFDictionaryPresentation.digit (P : CFDictionaryPresentation) (x : ℝ) (n : ℕ) : ℤ :=
  VV.partialQuotient x (P.offset + n + 1)

def CFDictionaryPresentation.carrier (P : CFDictionaryPresentation) : Set ℝ :=
  allowedBlocks P.domain P.digit P.blockLength P.dictionary

/-- A precisely stated analytic certificate; supplying one is a theoretical
obligation, not a finite computation.  Its cells are actual CF digit cylinders. -/
def CFDictionaryPresentation.SmallAt (P : CFDictionaryPresentation) (s : ℝ≥0) : Prop :=
  ∃ r : ℝ≥0∞, r < 1 ∧
    (P.dictionary.card : ℝ≥0∞) * r ^ (s : ℝ) < 1 ∧
    ∀ᶠ n in atTop, ∀ word : Fin n → P.dictionary,
      EMetric.diam
        (blockCylinder P.domain P.digit P.blockLength n (fun j => (word j).val)) ≤ r ^ n

theorem CFDictionaryPresentation.measure_zero
    (P : CFDictionaryPresentation) (s : ℝ≥0) (h : P.SmallAt s) :
    hausdorffMeasure (s : ℝ) P.carrier = 0 := by
  obtain ⟨r, hr, hsize, hdiam⟩ := h
  exact hausdorffMeasure_allowedBlocks_zero
    P.domain P.digit P.blockLength P.dictionary s s.coe_nonneg r hr hsize hdiam

/-- All possible integer parts, finite prefixes and finite dictionaries.
Unlike the set of all infinite digit strings, this type is countable. -/
abbrev CFPresentationIndex :=
  Σ N : ℕ, Σ L : ℕ, ℤ × (Fin N → ℤ) × Finset (Fin L → ℤ)

instance : Countable CFPresentationIndex := by infer_instance

def presentationOfIndex (i : CFPresentationIndex) : CFDictionaryPresentation where
  domain := {x | Irrational x ∧ VV.partialQuotient x 0 = i.2.2.1 ∧
    ∀ j : Fin i.1, VV.partialQuotient x (j.val + 1) = i.2.2.2.1 j}
  offset := i.1
  blockLength := i.2.1
  dictionary := i.2.2.2.2

/-- The arithmetic covering interface used by the reductions below.
It is a proposition, not an added axiom or an admission in this module.
This is pointwise in `x`: its finite prefix and finite dictionary need not
be uniform across the exceptional set or across the positive exponent. -/
def ArithmeticCoverInput : Prop :=
  ∀ s : ℝ≥0, 0 < s → ∀ x ∈ VV.BExceptional,
    ∃ i : CFPresentationIndex,
      x ∈ (presentationOfIndex i).carrier ∧ (presentationOfIndex i).SmallAt s

/-- Reduction of the exact Problem 7 statement to the arithmetic covering
interface. Later modules supply this interface from the internally
constructed BBEK theorem; the cover and countable-union steps are proved here. -/
theorem problem7_of_arithmetic_cover (h : ArithmeticCoverInput) : Statement := by
  classical
  let pieces : ℝ≥0 → CFPresentationIndex → Set ℝ := fun s i =>
    {x | (presentationOfIndex i).SmallAt s ∧ x ∈ (presentationOfIndex i).carrier}
  apply dimH_zero_of_countable_small_covers VV.BExceptional pieces
  · intro s hs x hx
    obtain ⟨i, hxi, hi⟩ := h s hs x hx
    exact mem_iUnion.mpr ⟨i, hi, hxi⟩
  · intro s _hs i
    by_cases hi : (presentationOfIndex i).SmallAt s
    · exact measure_mono_null (fun _ hx => hx.2)
        ((presentationOfIndex i).measure_zero s hi)
    · have hempty : pieces s i = ∅ := by
        ext x
        simp only [pieces, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun hcontra => False.elim (hi hcontra)
      rw [hempty, measure_empty]

/-! ## Discharging the cylinder geometry for even block lengths -/

/-- The finite prefix and the prescribed blocks really determine the first
`n*L` digits.  This lemma is elementary index arithmetic, not an oracle. -/
theorem index_cylinder_same_digits
    (i : CFPresentationIndex) (hL : 0 < i.2.1) (n : ℕ)
    (word : Fin n → (presentationOfIndex i).dictionary)
    {x y : ℝ}
    (hx : x ∈ blockCylinder (presentationOfIndex i).domain
      (presentationOfIndex i).digit i.2.1 n (fun j => (word j).val))
    (hy : y ∈ blockCylinder (presentationOfIndex i).domain
      (presentationOfIndex i).digit i.2.1 n (fun j => (word j).val)) :
    Irrational x ∧ Irrational y ∧
    VV.partialQuotient x 0 = VV.partialQuotient y 0 ∧
    ∀ k : ℕ, k < n * i.2.1 →
      VV.partialQuotient x (k + 1) = VV.partialQuotient y (k + 1) := by
  simp only [blockCylinder, mem_setOf_eq, presentationOfIndex,
    CFDictionaryPresentation.digit] at hx hy
  refine ⟨hx.1.1, hy.1.1, hx.1.2.1.trans hy.1.2.1.symm, ?_⟩
  intro k hk
  by_cases hkN : k < i.1
  · exact (hx.1.2.2 ⟨k, hkN⟩).trans (hy.1.2.2 ⟨k, hkN⟩).symm
  · have hsub : k - i.1 < n * i.2.1 := (Nat.sub_le k i.1).trans_lt hk
    let j : Fin n := ⟨(k - i.1) / i.2.1, (Nat.div_lt_iff_lt_mul hL).mpr hsub⟩
    let b : Fin i.2.1 := ⟨(k - i.1) % i.2.1, Nat.mod_lt _ hL⟩
    have hindex : i.1 + (j.val * i.2.1 + b.val) + 1 = k + 1 := by
      dsimp [j, b]
      have hdiv := Nat.div_add_mod (k - i.1) i.2.1
      rw [Nat.mul_comm i.2.1] at hdiv
      omega
    have heq := (hx.2 j b).trans (hy.2 j b).symm
    simpa only [hindex] using heq

/-- Actual CF cylinders with `n` prescribed blocks of even length `2*L`
have diameter at most `(4^(-L))^n`. -/
theorem index_cylinder_diameter
    (i : CFPresentationIndex) (L : ℕ) (hL : 0 < L) (hlen : i.2.1 = 2 * L)
    (n : ℕ) (word : Fin n → (presentationOfIndex i).dictionary) :
    EMetric.diam
      (blockCylinder (presentationOfIndex i).domain (presentationOfIndex i).digit
        i.2.1 n (fun j => (word j).val)) ≤ ((1 / 4 : ℝ≥0∞) ^ L) ^ n := by
  have hb : EMetric.diam
      (blockCylinder (presentationOfIndex i).domain (presentationOfIndex i).digit
        i.2.1 n (fun j => (word j).val)) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ (n * L)) := by
    apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    obtain ⟨hxi, hyi, hzero, hdigits⟩ :=
      index_cylinder_same_digits i (by omega) n word hx hy
    apply VV.CylinderGeometry.same_prefix_distance x y hxi hyi (n * L) hzero
    intro k hk
    apply hdigits k
    simpa only [hlen, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hk
  convert hb using 1
  rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 4 : ℝ))]
  have hquarter : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hquarter, ← pow_mul, Nat.mul_comm n L]

theorem index_smallAt_of_card_bound
    (i : CFPresentationIndex) (L : ℕ) (hL : 0 < L) (hlen : i.2.1 = 2 * L)
    (s : ℝ≥0)
    (hcard : ((presentationOfIndex i).dictionary.card : ℝ≥0∞) *
      ((1 / 4 : ℝ≥0∞) ^ L) ^ (s : ℝ) < 1) :
    (presentationOfIndex i).SmallAt s := by
  refine ⟨(1 / 4 : ℝ≥0∞) ^ L, ?_, hcard, ?_⟩
  · exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  · exact Eventually.of_forall fun n word => index_cylinder_diameter i L hL hlen n word

/-- This intermediate interface concerns only arithmetic/entropy: every
exceptional point has, for every positive exponent, an eventually valid
finite dictionary of sufficiently small cardinality.  All CF cylinder
diameter estimates are proved above and are no longer hypotheses. -/
def EntropyDictionaryInput : Prop :=
  ∀ s : ℝ≥0, 0 < s → ∀ x ∈ VV.BExceptional,
    ∃ (i : CFPresentationIndex) (L : ℕ), 0 < L ∧ i.2.1 = 2 * L ∧
      x ∈ (presentationOfIndex i).carrier ∧
      ((presentationOfIndex i).dictionary.card : ℝ≥0∞) *
        ((1 / 4 : ℝ≥0∞) ^ L) ^ (s : ℝ) < 1

theorem arithmeticCoverInput_of_entropyDictionaryInput
    (h : EntropyDictionaryInput) : ArithmeticCoverInput := by
  intro s hs x hx
  obtain ⟨i, L, hL, hlen, hmem, hcard⟩ := h s hs x hx
  exact ⟨i, hmem, index_smallAt_of_card_bound i L hL hlen s hcard⟩

/-- Problem 7 reduced solely to the arithmetic/entropy dictionary input;
the finite-prefix, cylinder geometry and Hausdorff-cover parts are complete. -/
theorem problem7_of_entropy_dictionary (h : EntropyDictionaryInput) : Statement :=
  problem7_of_arithmetic_cover (arithmeticCoverInput_of_entropyDictionaryInput h)

/-! ## From small recurrent dictionaries to eventual dictionaries -/

theorem eventually_recurrent_words_of_finite_range {A : Type*}
    (stream : ℕ → A) (hfin : (Set.range stream).Finite) (L : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      RecurrentValue (wordAt stream L) (wordAt stream L n) := by
  classical
  letI : Fintype (Set.range stream) := hfin.fintype
  let lifted : ℕ → Set.range stream := fun n => ⟨stream n, ⟨n, rfl⟩⟩
  obtain ⟨N, hN⟩ := eventually_recurrent_words lifted L
  refine ⟨N, fun n hn M => ?_⟩
  obtain ⟨j, hj, hword⟩ := hN n hn M
  refine ⟨j, hj, ?_⟩
  funext k
  exact congrArg Subtype.val (congrFun hword k)

/-- An irrational number with an eventual CF digit bound has a finite
alphabet even after its finite exceptional prefix is included. -/
theorem finite_range_cf_digits {x : ℝ} (hx : Irrational x)
    {C : ℕ} (hC : VV.EventualBound x C) :
    (Set.range fun n : ℕ => VV.partialQuotient x (n + 1)).Finite := by
  classical
  obtain ⟨N, hN⟩ := hC
  let head : Finset ℤ := (Finset.range N).image (fun n => VV.partialQuotient x (n + 1))
  let tail : Finset ℤ := Finset.Icc 1 (C : ℤ)
  apply (head.finite_toSet.union tail.finite_toSet).subset
  rintro z ⟨n, rfl⟩
  by_cases hn : n < N
  · exact Or.inl (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩)
  · exact Or.inr (Finset.mem_Icc.mpr
      ⟨VV.one_le_partialQuotient_succ hx n, hN n (by omega)⟩)

/-- The consequence supplied in later modules by the joint-limit
and BBEK rigidity argument: recurrent words admit finite dictionaries of
subexponential cardinality, expressed at each positive exponent. -/
def RecurrentDictionaryInput : Prop :=
  ∀ s : ℝ≥0, 0 < s → ∀ x ∈ VV.BExceptional,
    ∃ (L : ℕ) (W : Finset (Fin (2 * L) → ℤ)), 0 < L ∧
      (∀ w : Fin (2 * L) → ℤ,
        RecurrentValue (wordAt (fun n => VV.partialQuotient x (n + 1)) (2 * L)) w → w ∈ W) ∧
      (W.card : ℝ≥0∞) * ((1 / 4 : ℝ≥0∞) ^ L) ^ (s : ℝ) < 1

theorem entropyDictionaryInput_of_recurrentDictionaryInput
    (h : RecurrentDictionaryInput) : EntropyDictionaryInput := by
  intro s hs x hx
  obtain ⟨L, W, hL, hW, hcard⟩ := h s hs x hx
  obtain ⟨C, hC⟩ := hx.2
  have hbound : VV.EventualBound x C := by simpa using hC 0
  obtain ⟨N, hN⟩ := eventually_recurrent_words_of_finite_range
    (fun n => VV.partialQuotient x (n + 1)) (finite_range_cf_digits hx.1 hbound) (2 * L)
  let i : CFPresentationIndex :=
    ⟨N, 2 * L, VV.partialQuotient x 0, (fun j => VV.partialQuotient x (j.val + 1)), W⟩
  refine ⟨i, L, hL, rfl, ?_, hcard⟩
  change x ∈ allowedBlocks (presentationOfIndex i).domain
    (presentationOfIndex i).digit (2 * L) W
  refine ⟨⟨hx.1, rfl, fun _ => rfl⟩, ?_⟩
  intro j
  have hw := hW _ (hN (N + j * (2 * L)) (Nat.le_add_right _ _))
  change (fun b : Fin (2 * L) =>
    VV.partialQuotient x (N + j * (2 * L) + b.val + 1)) ∈ W at hw
  simpa only [CFDictionaryPresentation.digit, presentationOfIndex, i,
    Nat.add_assoc] using hw

/-- The strongest reduction in this module: finite exceptional words,
continued-fraction geometry and the dimension argument are all proved.
The small-recurrent-dictionary consequence of arithmetic rigidity is the
explicit hypothesis of this reusable reduction. -/
theorem problem7_of_recurrent_dictionary (h : RecurrentDictionaryInput) : Statement :=
  problem7_of_entropy_dictionary (entropyDictionaryInput_of_recurrentDictionaryInput h)

end VV.Problem7
