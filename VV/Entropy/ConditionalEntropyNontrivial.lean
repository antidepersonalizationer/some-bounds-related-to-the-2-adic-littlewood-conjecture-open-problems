import VV.Entropy.KSEntropyFuture

/-! Genuine positive conditional entropy excludes point-mass conditional
measures.  This is an entropy-to-disintegration statement; it does not
claim the much stronger translation symmetry supplied by the low-entropy
method in higher rank. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {X I : Type*} [mX : MeasurableSpace X] [Fintype I]

theorem entropy_dirac_eq_zero (x : X) (cells : I → Set X) :
    entropy (Measure.dirac x) cells = 0 := by
  unfold entropy
  apply Finset.sum_eq_zero
  intro i hi
  rcases Measure.dirac_apply_eq_zero_or_one (a := x) (s := cells i) with h | h
  · simp only [h,ENNReal.toReal_zero,Real.negMulLog_zero]
  · simp only [h,ENNReal.toReal_one,Real.negMulLog_one]

theorem condEntropy_eq_zero_of_ae_dirac [StandardBorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (A : MeasurableSpace X) (cells : I → Set X)
    (hdirac : ∀ᵐ x ∂μ, ∃ y, @condExpKernel X mX _ μ _ A x = @Measure.dirac X mX y) :
    condEntropy μ A cells = 0 := by
  letI : MeasurableSpace X := mX
  unfold condEntropy
  apply integral_eq_zero_of_ae
  filter_upwards [hdirac] with x hx
  obtain ⟨y,hy⟩ := hx
  change entropy (@condExpKernel X mX _ μ _ A x) cells = 0
  rw [hy,entropy_dirac_eq_zero]

theorem not_ae_dirac_of_pos_condEntropy [StandardBorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (A : MeasurableSpace X) (cells : I → Set X)
    (hpos : 0 < condEntropy μ A cells) :
    ¬ (∀ᵐ x ∂μ, ∃ y, @condExpKernel X mX _ μ _ A x = @Measure.dirac X mX y) := by
  letI : MeasurableSpace X := mX
  intro hd
  rw [condEntropy_eq_zero_of_ae_dirac μ A cells hd] at hpos
  exact lt_irrefl 0 hpos

theorem exists_pos_partition_of_pos_ksEntropy
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) (hpos : 0 < ksEntropy hT) :
    ∃ n : ℕ, ∃ P : MeasurePartition μ (Fin n), 0 < ksEntropyPartition hT P := by
  classical
  by_contra hn
  have hzero : ksEntropy hT ≤ 0 := by
    apply iSup_le
    intro n
    apply iSup_le
    intro P
    have h : ksEntropyPartition hT P ≤ 0 :=
      le_of_not_gt (fun hp => hn ⟨n,P,hp⟩)
    exact EReal.coe_nonpos.mpr h
  exact not_le_of_gt hpos hzero

theorem exists_nontrivial_future_kernel_of_pos_ksEntropy [StandardBorelSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) (hpos : 0 < ksEntropy hT) :
    ∃ n : ℕ, ∃ P : MeasurePartition μ (Fin n),
      0 < condEntropy μ (entireFutureSigma hT P) P.cells ∧
      ¬ (∀ᵐ x ∂μ, ∃ y, condExpKernel μ (entireFutureSigma hT P) x = Measure.dirac y) := by
  obtain ⟨n,P,hP⟩ := exists_pos_partition_of_pos_ksEntropy hT hpos
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hc := congrArg μ P.cover
    have hz : (0 : ℝ≥0∞) = 1 := by
      simpa only [iUnion_of_empty,measure_empty,measure_univ] using hc
    exact zero_ne_one hz
  letI : NeZero n := ⟨hn⟩
  have hp : 0 < condEntropy μ (entireFutureSigma hT P) P.cells := by
    rwa [← ksEntropyPartition_eq_condEntropy_entireFuture hT P]
  exact ⟨n,P,hp,not_ae_dirac_of_pos_condEntropy μ _ P.cells hp⟩

end ErgodicTheory.Entropy
