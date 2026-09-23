import VV.Entropy.ConditionalEntropyNontrivial

/-! Conditional measures really remain in the same future itinerary.
The support conclusion is proved from conditional expectation, rather
than imposed as a property of a supplied family of leaf measures. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {X I : Type*} [mX : MeasurableSpace X] [StandardBorelSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]

theorem condExpKernel_ae_mem_iff (A : MeasurableSpace X) (hA : A ≤ mX)
    {s : Set X} (hs : MeasurableSet[A] s) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂(@condExpKernel X mX _ μ _ A x), y ∈ s ↔ x ∈ s := by
  letI : MeasurableSpace X := mX
  have hc := condExpKernel_ae_eq_condExp (μ := μ) hA (hA _ hs)
  have he : μ[s.indicator (fun _ => (1 : ℝ)) | A] = s.indicator (fun _ => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable hA (stronglyMeasurable_const.indicator hs)
      ((integrable_const (1 : ℝ)).indicator (hA _ hs))
  rw [he] at hc
  filter_upwards [hc] with x hx
  by_cases hxs : x ∈ s
  · have hm : (condExpKernel μ A x) s = 1 := by
      apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mp
      simpa only [Measure.real, hxs, Set.indicator_of_mem, ENNReal.toReal_one] using hx
    filter_upwards [(mem_ae_iff_prob_eq_one (hA _ hs)).mpr hm] with y hy
    exact iff_of_true hy hxs
  · have hm : (condExpKernel μ A x) s = 0 := by
      simp only [Set.indicator_of_notMem hxs, Measure.real] at hx
      apply (ENNReal.toReal_eq_zero_iff _).mp at hx
      exact hx.resolve_right (measure_ne_top _ _)
    have hy : ∀ᵐ y ∂condExpKernel μ A x, y ∉ s := by
      apply ae_iff.mpr
      simpa only [not_not, Set.setOf_mem_eq] using hm
    filter_upwards [hy] with y hy
    exact iff_of_false hy hxs

variable [Fintype I] {T : X → X}

omit [StandardBorelSpace X] [IsProbabilityMeasure μ] in
theorem measurableSet_future_coordinate (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ I) (n : ℕ) (i : I) :
    MeasurableSet[entireFutureSigma hT P] ((T^[n+1]) ⁻¹' P.cells i) := by
  apply (le_iSup (futureSigma hT P) (n+1))
  rw [futureSigma_eq_comap]
  have hs := measurableSet_preimage_cells hT P (n+1) ⟨n,Nat.lt_succ_self n⟩ i
  have hm : @Measurable X X (MeasurableSpace.comap T (generatedSigmaAlgebra μ (ksJoin hT P (n+1))))
      (generatedSigmaAlgebra μ (ksJoin hT P (n+1))) T := fun s hs => ⟨s,hs,rfl⟩
  have hpre := hm hs
  simpa only [Fin.val_mk,← Set.preimage_comp,← Function.iterate_succ] using hpre

theorem futureKernel_ae_same_itinerary (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ I) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂condExpKernel μ (entireFutureSigma hT P) x,
      ∀ n : ℕ, ∀ i : I, (T^[n+1]) y ∈ P.cells i ↔ (T^[n+1]) x ∈ P.cells i := by
  have hA : entireFutureSigma hT P ≤ mX := iSup_le (futureSigma_le hT P)
  have hall : ∀ n : ℕ, ∀ i : I, ∀ᵐ x ∂μ,
      ∀ᵐ y ∂condExpKernel μ (entireFutureSigma hT P) x,
        (T^[n+1]) y ∈ P.cells i ↔ (T^[n+1]) x ∈ P.cells i :=
    fun n i => condExpKernel_ae_mem_iff _ hA (measurableSet_future_coordinate hT P n i)
  filter_upwards [ae_all_iff.mpr fun n => ae_all_iff.mpr (hall n)] with x hx
  exact ae_all_iff.mpr fun n => ae_all_iff.mpr (hx n)

theorem futureKernel_ae_same_cell (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ I) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂condExpKernel μ (entireFutureSigma hT P) x,
      ∀ n : ℕ, ∃ i : I, (T^[n+1]) x ∈ P.cells i ∧ (T^[n+1]) y ∈ P.cells i := by
  filter_upwards [futureKernel_ae_same_itinerary hT P] with x hx
  filter_upwards [hx] with y hy
  intro n
  have hcov : (T^[n+1]) x ∈ ⋃ i, P.cells i := P.cover ▸ Set.mem_univ _
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hcov
  exact ⟨i,hi,(hy n i).mpr hi⟩

end ErgodicTheory.Entropy
