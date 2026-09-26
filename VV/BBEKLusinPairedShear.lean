import VV.BBEKPairedShear
import VV.BBEKLusin

/-! Actual compact Lusin selection followed by simultaneous shearing returns. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal MatrixGroups
namespace VV.BBEKLusinPairedShear
open BBEKPairedReturnTimes BBEKQuadraticScale BBEKPairedShear

variable {F Z : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
  [ProperSpace F] [SecondCountableTopology F]
  [TopologicalSpace Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
  {μ : Measure Z} [IsProbabilityMeasure μ] [μ.InnerRegularCompactLTTop]
  {T : Z → Z}

/-- Both the compact test-continuity set and the simultaneous return set are
constructed. No Lusin set or uniform polynomial lower bound is supplied as
an assumption. The final root bad-set bound remains the exact input needed
from the separate leaf maximal theorem. -/
theorem exists_compact_paired_shear (hT : MeasurePreserving T μ μ)
    (η : Z → Measure F) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnorm : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hnoatom : ∀ᵐ q ∂μ, NoAtoms (η q)) {a : F} (ha : ‖a‖ = 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ S Q G : Set Z,
      IsCompact S ∧
      (∀ j : ℕ, ContinuousOn
        (fun q => ∫ u, BBEKLeafMeasureTests.testFunction j u ∂η q) S) ∧
      MeasurableSet Q ∧ Q ⊆ S ∧ MeasurableSet G ∧ (99 / 100 : ℝ) < μ.real G ∧
      ∀ x ∈ G, ∀ y ∈ G, ∀ g : SL(2,F),
        ‖g 0 0-g 1 1‖ ≤ 1 → ‖g 0 1‖ ≤ 1 →
        (¬∀ u : F, BBEKFiniteQuotients.lower u*g = g*BBEKFiniteQuotients.lower u) →
        ∃ s t k : ℕ, k < min s (t / 2) / 4+1 ∧
          T^[k] x ∈ Q ∧ T^[k] y ∈ Q ∧
          T^[shearTime s t k] x ∈ Q ∧ T^[shearTime s t k] y ∈ Q ∧
          ‖linearCoefficient a g (extraTime s t k)‖ ≤ 1 ∧
          ‖quadraticCoefficient a g k (extraTime s t k)‖ ≤ 1 ∧
          ∀ D : Set F, η (T^[k] x) D ≤ (1/2 : ℝ≥0∞) →
            ∃ v : F, ‖v‖ < r ∧ v ∉ D ∧
              δ < ‖linearCoefficient a g (extraTime s t k)*v +
                quadraticCoefficient a g k (extraTime s t k)*v^2‖ := by
  obtain ⟨S,hS,hSbad,hcont⟩ := BBEKLusin.exists_compact_test_continuity μ η hη
    (by positivity : ENNReal.ofReal (1/20000 : ℝ) ≠ 0)
  have hSsmall : μ.real Sᶜ < (1/20000 : ℝ) := by
    have he := (ENNReal.toReal_lt_toReal (measure_ne_top μ Sᶜ)
      ENNReal.ofReal_ne_top).mpr hSbad
    simpa using he
  obtain ⟨δ,hδ,Q,G,hQ,hQS,hG,hGmass,hselect⟩ :=
    exists_paired_shear_good_set hT S hS.isClosed.measurableSet hSsmall
      η hη hr hnorm hnoatom ha
  exact ⟨δ,hδ,S,Q,G,hS,hcont,hQ,hQS,hG,hGmass,hselect⟩



/-- The same choices of return times and root parameters feed the actual
nonidentity-root limit theorem. The root bad sets are arbitrary measurable
or nonmeasurable sets; only their explicit half-mass bound is required.
This bound is not asserted here for the leaf-return bad sets. -/
theorem exists_compact_paired_shear_sequence (hT : MeasurePreserving T μ μ)
    (η : Z → Measure F) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnorm : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hnoatom : ∀ᵐ q ∂μ, NoAtoms (η q)) {a : F} (ha : ‖a‖ = 2) (ha0 : a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ S Q G : Set Z,
      IsCompact S ∧
      (∀ j : ℕ, ContinuousOn
        (fun q => ∫ u, BBEKLeafMeasureTests.testFunction j u ∂η q) S) ∧
      MeasurableSet Q ∧ Q ⊆ S ∧ MeasurableSet G ∧ (99 / 100 : ℝ) < μ.real G ∧
      ∀ x y : ℕ → Z, (∀ i, x i ∈ G) → (∀ i, y i ∈ G) →
      ∀ g : ℕ → SL(2,F), Tendsto g atTop (𝓝 1) →
        (∀ i, ‖g i 0 0-g i 1 1‖ ≤ 1) → (∀ i, ‖g i 0 1‖ ≤ 1) →
        (∀ i, ¬∀ u : F, BBEKFiniteQuotients.lower u*g i = g i*BBEKFiniteQuotients.lower u) →
      ∀ D : ℕ → ℕ → ℕ → Set F,
        (∀ i k n, T^[k] (x i) ∈ Q → η (T^[k] (x i)) (D i k n) ≤ (1/2 : ℝ≥0∞)) →
        ∃ s t k : ℕ → ℕ, ∃ v : ℕ → F,
          (∀ i, k i < min (s i) (t i / 2) / 4+1 ∧
            T^[k i] (x i) ∈ Q ∧ T^[k i] (y i) ∈ Q ∧
            T^[shearTime (s i) (t i) (k i)] (x i) ∈ Q ∧
            T^[shearTime (s i) (t i) (k i)] (y i) ∈ Q ∧
            ‖v i‖ < r ∧ v i ∉ D i (k i) (extraTime (s i) (t i) (k i))) ∧
          ∃ u : F, u ≠ 0 ∧ δ ≤ ‖u‖ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto ((fun i => BBEKSl2Shear.lowerShear
              (a^(2*extraTime (s i) (t i) (k i))*v i)
              (BBEKEntropyExpansive.diagConjugate (a^k i) (pow_ne_zero (k i) ha0) (g i))) ∘ φ)
              atTop (𝓝 (BBEKFiniteQuotients.lower u)) := by
  classical
  obtain ⟨δ,hδ,S,Q,G,hS,hcont,hQ,hQS,hG,hGmass,hselect⟩ :=
    exists_compact_paired_shear hT η hη hr hnorm hnoatom ha
  refine ⟨δ,hδ,S,Q,G,hS,hcont,hQ,hQS,hG,hGmass,?_⟩
  intro x y hx hy g hg hd hb hnc D hD
  have hchoices (i : ℕ) := hselect (x i) (hx i) (y i) (hy i) (g i) (hd i) (hb i) (hnc i)
  choose s t k hk hxk hyk hxn hyn hlin hquad hparam using hchoices
  let n : ℕ → ℕ := fun i => extraTime (s i) (t i) (k i)
  have hvchoices (i : ℕ) := hparam i (D i (k i) (n i)) (hD i (k i) (n i) (hxk i))
  choose v hv hvD hvpoly using hvchoices
  refine ⟨s,t,k,v,?_,?_⟩
  · intro i
    exact ⟨hk i,hxk i,hyk i,hxn i,hyn i,hv i,hvD i⟩
  · exact BBEKShearLimit.exists_nonzero_lower_limit ha ha0 g hg k n v hδ
      (fun i => BBEKShearLimit.admissible_time_le_extra (hk i))
      (fun i => (hv i).le) hlin hquad (fun i => (hvpoly i).le)

/-- Actual Lusin version sampling the normalized leaf at the total return time. -/
theorem exists_compact_paired_shear_at_total_time (hT : MeasurePreserving T μ μ)
    (η : Z → Measure F) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnorm : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hnoatom : ∀ᵐ q ∂μ, NoAtoms (η q)) {a : F} (ha : ‖a‖ = 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ S Q G : Set Z,
      IsCompact S ∧
      (∀ j : ℕ, ContinuousOn
        (fun q => ∫ u, BBEKLeafMeasureTests.testFunction j u ∂η q) S) ∧
      MeasurableSet Q ∧ Q ⊆ S ∧ MeasurableSet G ∧ (99 / 100 : ℝ) < μ.real G ∧
      ∀ x ∈ G, ∀ y ∈ G, ∀ g : SL(2,F),
        ‖g 0 0-g 1 1‖ ≤ 1 → ‖g 0 1‖ ≤ 1 →
        (¬∀ u : F, BBEKFiniteQuotients.lower u*g = g*BBEKFiniteQuotients.lower u) →
        ∃ s t k : ℕ, k < min s (t / 2) / 4+1 ∧
          T^[k] x ∈ Q ∧ T^[k] y ∈ Q ∧
          T^[shearTime s t k] x ∈ Q ∧ T^[shearTime s t k] y ∈ Q ∧
          ‖linearCoefficient a g (extraTime s t k)‖ ≤ 1 ∧
          ‖quadraticCoefficient a g k (extraTime s t k)‖ ≤ 1 ∧
          ∀ D : Set F, η (T^[shearTime s t k] x) D ≤ (1/2 : ℝ≥0∞) →
            ∃ v : F, ‖v‖ < r ∧ v ∉ D ∧
              δ < ‖linearCoefficient a g (extraTime s t k)*v +
                quadraticCoefficient a g k (extraTime s t k)*v^2‖ := by
  obtain ⟨S,hS,hSbad,hcont⟩ := BBEKLusin.exists_compact_test_continuity μ η hη
    (by positivity : ENNReal.ofReal (1/20000 : ℝ) ≠ 0)
  have hSsmall : μ.real Sᶜ < (1/20000 : ℝ) := by
    have he := (ENNReal.toReal_lt_toReal (measure_ne_top μ Sᶜ)
      ENNReal.ofReal_ne_top).mpr hSbad
    simpa using he
  obtain ⟨δ,hδ,Q,G,hQ,hQS,hG,hGmass,hselect⟩ :=
    exists_paired_shear_good_set_at_total_time hT S hS.isClosed.measurableSet hSsmall
      η hη hr hnorm hnoatom ha
  exact ⟨δ,hδ,S,Q,G,hS,hcont,hQ,hQS,hG,hGmass,hselect⟩




/-- The actual normalized-coordinate sequence version. Its bad-set mass input
is at `T^(k+n) x`, matching the large root parameter at time `k`. -/
theorem exists_compact_paired_shear_sequence_at_total_time (hT : MeasurePreserving T μ μ)
    (η : Z → Measure F) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnorm : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hnoatom : ∀ᵐ q ∂μ, NoAtoms (η q)) {a : F} (ha : ‖a‖ = 2) (ha0 : a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ S Q G : Set Z,
      IsCompact S ∧
      (∀ j : ℕ, ContinuousOn
        (fun q => ∫ u, BBEKLeafMeasureTests.testFunction j u ∂η q) S) ∧
      MeasurableSet Q ∧ Q ⊆ S ∧ MeasurableSet G ∧ (99 / 100 : ℝ) < μ.real G ∧
      ∀ x y : ℕ → Z, (∀ i, x i ∈ G) → (∀ i, y i ∈ G) →
      ∀ g : ℕ → SL(2,F), Tendsto g atTop (𝓝 1) →
        (∀ i, ‖g i 0 0-g i 1 1‖ ≤ 1) → (∀ i, ‖g i 0 1‖ ≤ 1) →
        (∀ i, ¬∀ u : F, BBEKFiniteQuotients.lower u*g i = g i*BBEKFiniteQuotients.lower u) →
      ∀ D : ℕ → ℕ → ℕ → Set F,
        (∀ i k n, T^[k+n] (x i) ∈ Q → η (T^[k+n] (x i)) (D i k n) ≤ (1/2 : ℝ≥0∞)) →
        ∃ s t k : ℕ → ℕ, ∃ v : ℕ → F,
          (∀ i, k i < min (s i) (t i / 2) / 4+1 ∧
            T^[k i] (x i) ∈ Q ∧ T^[k i] (y i) ∈ Q ∧
            T^[shearTime (s i) (t i) (k i)] (x i) ∈ Q ∧
            T^[shearTime (s i) (t i) (k i)] (y i) ∈ Q ∧
            ‖v i‖ < r ∧ v i ∉ D i (k i) (extraTime (s i) (t i) (k i))) ∧
          ∃ u : F, u ≠ 0 ∧ δ ≤ ‖u‖ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto ((fun i => BBEKSl2Shear.lowerShear
              (a^(2*extraTime (s i) (t i) (k i))*v i)
              (BBEKEntropyExpansive.diagConjugate (a^k i) (pow_ne_zero (k i) ha0) (g i))) ∘ φ)
              atTop (𝓝 (BBEKFiniteQuotients.lower u)) := by
  classical
  obtain ⟨δ,hδ,S,Q,G,hS,hcont,hQ,hQS,hG,hGmass,hselect⟩ :=
    exists_compact_paired_shear_at_total_time hT η hη hr hnorm hnoatom ha
  refine ⟨δ,hδ,S,Q,G,hS,hcont,hQ,hQS,hG,hGmass,?_⟩
  intro x y hx hy g hg hd hb hnc D hD
  have hchoices (i : ℕ) := hselect (x i) (hx i) (y i) (hy i) (g i) (hd i) (hb i) (hnc i)
  choose s t k hk hxk hyk hxn hyn hlin hquad hparam using hchoices
  let n : ℕ → ℕ := fun i => extraTime (s i) (t i) (k i)
  have htime (i : ℕ) : shearTime (s i) (t i) (k i) = k i+n i := by
    apply shearTime_eq_add
    have hh := hk i
    omega
  have hvchoices (i : ℕ) := hparam i (D i (k i) (n i)) (by
    rw [htime]
    exact hD i (k i) (n i) (by simpa only [htime] using hxn i))
  choose v hv hvD hvpoly using hvchoices
  refine ⟨s,t,k,v,?_,?_⟩
  · intro i
    exact ⟨hk i,hxk i,hyk i,hxn i,hyn i,hv i,hvD i⟩
  · exact BBEKShearLimit.exists_nonzero_lower_limit ha ha0 g hg k n v hδ
      (fun i => BBEKShearLimit.admissible_time_le_extra (hk i))
      (fun i => (hv i).le) hlin hquad (fun i => (hvpoly i).le)


end VV.BBEKLusinPairedShear

