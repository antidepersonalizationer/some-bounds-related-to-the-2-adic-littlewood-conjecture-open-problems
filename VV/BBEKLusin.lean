import VV.BBEKLeafMeasureTests
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecificLimits.Basic

/-! Compact continuity sets for measurable leaf observables. -/
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal
namespace VV.BBEKLusin

theorem exists_compact_continuousOn
    {Z Y : Type*} [TopologicalSpace Z] [T2Space Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure Z) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (f : Z → Y) (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set Z, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  classical
  let I := Unit ⊕ ((countableBasis Y) × Bool)
  let S : I → Set Z := fun i => match i with
    | .inl _ => univ
    | .inr (b,true) => f ⁻¹' b.val
    | .inr (b,false) => (f ⁻¹' b.val)ᶜ
  have hS : ∀ i, MeasurableSet (S i) := by
    intro i
    rcases i with i | ⟨b,k⟩
    · exact MeasurableSet.univ
    · cases k
      · exact (((isBasis_countableBasis Y).isOpen b.property).measurableSet.preimage hf).compl
      · exact ((isBasis_countableBasis Y).isOpen b.property).measurableSet.preimage hf
  obtain ⟨δ,hδ,hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε I
  choose C hCS hC hμC using fun i => (hS i).exists_isCompact_diff_lt
    (measure_ne_top μ (S i)) (hδ i).ne'
  let K := C (.inl ()) ∩ ⋂ b : countableBasis Y, C (.inr (b,true)) ∪ C (.inr (b,false))
  have hK : IsCompact K := (hC (.inl ())).inter_right
    (isClosed_iInter (fun b => (hC (.inr (b,true))).isClosed.union
      (hC (.inr (b,false))).isClosed))
  have hbad : Kᶜ ⊆ ⋃ i, S i \ C i := by
    intro z hz
    by_cases h0 : z ∈ C (.inl ())
    · have hn : ¬∀ b : countableBasis Y, z ∈ C (.inr (b,true)) ∪ C (.inr (b,false)) := by
        intro hb
        exact hz ⟨h0,mem_iInter.mpr hb⟩
      obtain ⟨b,hb⟩ := not_forall.mp hn
      by_cases hz' : f z ∈ b.val
      · exact mem_iUnion.mpr ⟨.inr (b,true),hz',fun hc => hb (Or.inl hc)⟩
      · exact mem_iUnion.mpr ⟨.inr (b,false),hz',fun hc => hb (Or.inr hc)⟩
    · exact mem_iUnion.mpr ⟨.inl (),mem_univ z,h0⟩
  refine ⟨K,hK,(measure_mono hbad).trans_lt ((measure_iUnion_le _).trans_lt
    ((ENNReal.tsum_le_tsum (fun i => (hμC i).le)).trans_lt hδsum)),?_⟩
  rw [continuousOn_iff_continuous_restrict]
  apply (isBasis_countableBasis Y).continuous_iff.mpr
  intro O hO
  let b : countableBasis Y := ⟨O,hO⟩
  have he : (K.restrict f) ⁻¹' O = Subtype.val ⁻¹' (C (.inr (b,false)))ᶜ := by
    ext z
    have hz := mem_iInter.mp z.property.2 b
    constructor
    · intro ho hc
      exact hCS (.inr (b,false)) hc ho
    · intro hc
      have ht : z.val ∈ C (.inr (b,true)) := hz.resolve_right hc
      exact hCS (.inr (b,true)) ht
  rw [he]
  exact ((hC (.inr (b,false))).isClosed.isOpen_compl).preimage continuous_subtype_val

theorem exists_compact_test_continuity
    {Z U : Type*} [TopologicalSpace Z] [T2Space Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
    [ProperSpace U] [SecondCountableTopology U]
    (μ : Measure Z) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (η : Z → Measure U) (hη : Measurable η) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set Z, IsCompact K ∧ μ Kᶜ < ε ∧
      ∀ j : ℕ, ContinuousOn (fun z => ∫ u, BBEKLeafMeasureTests.testFunction j u ∂η z) K := by
  have hm : Measurable (fun z j => ∫ u, BBEKLeafMeasureTests.testFunction j u ∂η z) :=
    measurable_pi_iff.mpr (fun j => BBEKLeafMeasureTests.measurable_integral_family η hη _)
  obtain ⟨K,hK,hμK,hf⟩ := exists_compact_continuousOn μ _ hm hε
  refine ⟨K,hK,hμK,fun j => ?_⟩
  exact (continuous_apply j).comp_continuousOn hf

/-- The compact continuity set controls the two genuinely different returning
points in a paired-return argument. -/
theorem tendsto_test_difference_of_close
    {Z U : Type*} [MetricSpace Z]
    [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
    [ProperSpace U] [SecondCountableTopology U]
    (η : Z → Measure U) {K : Set Z} (hK : IsCompact K)
    (hc : ∀ j : ℕ, ContinuousOn
      (fun z => ∫ u, BBEKLeafMeasureTests.testFunction j u ∂η z) K)
    {p q : ℕ → Z} (hp : ∀ n, p n ∈ K) (hq : ∀ n, q n ∈ K)
    (hd : Tendsto (fun n => dist (p n) (q n)) atTop (nhds 0)) (j : ℕ) :
    Tendsto (fun n => (∫ u, BBEKLeafMeasureTests.testFunction j u ∂η (p n)) -
      (∫ u, BBEKLeafMeasureTests.testFunction j u ∂η (q n))) atTop (nhds 0) := by
  have hu := hK.uniformContinuousOn_of_continuous (hc j)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hd δ hδ
  refine ⟨N,fun n hn => ?_⟩
  have hdist : dist (p n) (q n) < δ := by
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg] using hN n hn
  simpa only [Real.dist_eq,sub_zero] using hbound (p n) (hp n) (q n) (hq n) hdist

end VV.BBEKLusin
