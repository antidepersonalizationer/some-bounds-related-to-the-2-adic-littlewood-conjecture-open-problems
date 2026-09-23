import VV.BBEKSelectedDiagonal

/-! Exact normalized scaling covariance of the constructed full joint lower
leaf Radon family. The proof uses literal successive selected plaques. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal
namespace VV.BBEKGlobalLowerCovariance
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseAtlas BBEKSelectedPlaques BBEKSelectedDiagonal BBEKGrowingGlue
  BBEKGlobalLowerMeasure BBEKProjectiveGlue

/-- Comparing successive actual local restrictions gives projective
covariance on one growing ball. -/
theorem projective_restrict_scaling (ν ν' P P' : Measure Leaf)
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {t r : ℝ} (ht : Real.log 2 ≤ t) (n : ℕ)
    (hP : 0 < P (ball 0 r)) (hP' : 0 < P' (ball 0 r))
    (he : P' = P.map (leafScaling t 1))
    (hν : ν.restrict (growingBall r n) =
      (P (ball 0 r))⁻¹ • P.restrict (growingBall r n))
    (hν' : ν'.restrict (growingBall r (n+1)) =
      (P' (ball 0 r))⁻¹ • P'.restrict (growingBall r (n+1))) :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
      ν'.restrict (growingBall r (n+1)) =
        a • (ν.map (leafScaling t 1)).restrict (growingBall r (n+1)) := by
  let α := P (ball 0 r)
  let β := P' (ball 0 r)
  have hres : ν.restrict ((leafScaling t 1) ⁻¹' growingBall r (n+1)) =
      α⁻¹ • P.restrict ((leafScaling t 1) ⁻¹' growingBall r (n+1)) := by
    have hh : ν.restrict (growingBall r n) = (α⁻¹ • P).restrict (growingBall r n) := by
      rw [Measure.restrict_smul]
      exact hν
    have hh' := Measure.restrict_congr_mono (scaling_preimage_growingBall ht n) hh
    rwa [Measure.restrict_smul] at hh'
  have hmap : (ν.map (leafScaling t 1)).restrict (growingBall r (n+1)) =
      α⁻¹ • (P.map (leafScaling t 1)).restrict (growingBall r (n+1)) := by
    rw [(leafScaling t 1).measurableEmbedding.restrict_map,hres,Measure.map_smul,
      ← (leafScaling t 1).measurableEmbedding.restrict_map]
  have hα : α ≠ 0 := hP.ne'
  have hβ : β ≠ 0 := hP'.ne'
  have hαf : α ≠ ∞ := measure_ne_top P _
  have hβf : β ≠ ∞ := measure_ne_top P' _
  refine ⟨α*β⁻¹,mul_ne_zero hα (ENNReal.inv_ne_zero.mpr hβf),
    ENNReal.mul_ne_top hαf (ENNReal.inv_ne_top.mpr hβ),?_⟩
  rw [hν',hmap,← he,smul_smul]
  change β⁻¹ • P'.restrict (growingBall r (n+1)) =
    (α*β⁻¹*α⁻¹) • P'.restrict (growingBall r (n+1))
  congr 1
  calc
    β⁻¹ = β⁻¹*(α*α⁻¹) := by rw [ENNReal.mul_inv_cancel hα hαf,mul_one]
    _ = _ := by ac_rfl

/-- The common reference ball makes the projective constants on all growing
balls agree, giving an equality of whole-leaf measures. -/
theorem normalized_scaling_of_restrictions {r : ℝ} (hr : 0 < r)
    (ν ν' : Measure Leaf) {t : ℝ} (hnormal : ν' (ball 0 r) = 1)
    (hproj : ∀ n : ℕ, ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
      ν'.restrict (growingBall r (n+1)) =
        a • (ν.map (leafScaling t 1)).restrict (growingBall r (n+1))) :
    ν' = ((ν.map (leafScaling t 1)) (ball 0 r))⁻¹ • ν.map (leafScaling t 1) ∧
      0 < (ν.map (leafScaling t 1)) (ball 0 r) ∧
      (ν.map (leafScaling t 1)) (ball 0 r) ≠ ∞ := by
  have hbase (n : ℕ) : ball (0 : Leaf) r ⊆ growingBall r (n+1) := by
    simpa only [growingBall,pow_zero,one_mul] using growingBall_mono hr.le (Nat.zero_le (n+1))
  have heq (n : ℕ) : ν'.restrict (growingBall r (n+1)) =
      (((ν.map (leafScaling t 1)) (ball 0 r))⁻¹ • ν.map (leafScaling t 1)).restrict
        (growingBall r (n+1)) := by
    obtain ⟨a,ha,haf,he⟩ := hproj n
    have hh := normalize_restrict_of_projective ν' (ν.map (leafScaling t 1))
      isOpen_ball.measurableSet (hbase n) ha haf he
    simpa only [BBEKProjectiveGlue.normalize,hnormal,inv_one,one_smul] using hh
  have hcover : ⋃ n, growingBall r (n+1) = univ := by
    apply eq_univ_of_forall
    intro u
    have hu : u ∈ ⋃ n, growingBall r n := by rw [growingBall_cover hr]; trivial
    obtain ⟨n,hn⟩ := mem_iUnion.mp hu
    exact mem_iUnion.mpr ⟨n,growingBall_mono hr.le (Nat.le_succ n) hn⟩
  have hglobal := Measure.restrict_iUnion_congr.mpr heq
  rw [hcover,Measure.restrict_univ,Measure.restrict_univ] at hglobal
  refine ⟨hglobal,?_⟩
  obtain ⟨a,ha,haf,he⟩ := hproj 0
  have hm := congrArg (fun η : Measure Leaf => η (ball 0 r)) he
  simp only [Measure.restrict_apply isOpen_ball.measurableSet,
    inter_eq_self_of_subset_left (hbase 0),Measure.smul_apply,smul_eq_mul,hnormal] at hm
  have hv : (ν.map (leafScaling t 1)) (ball 0 r) = a⁻¹ := by
    calc
      _ = a⁻¹ * (a*(ν.map (leafScaling t 1)) (ball 0 r)) := by
        rw [← mul_assoc,ENNReal.inv_mul_cancel ha haf,one_mul]
      _ = a⁻¹ := by rw [← hm,mul_one]
  rw [hv]
  exact ⟨ENNReal.inv_pos.mpr haf,ENNReal.inv_ne_top.mpr ha⟩

private theorem mass_pos_of_normalized_restriction (ν P : Measure Leaf)
    {B S : Set Leaf} (hB : MeasurableSet B) (hBS : B ⊆ S) (hνB : ν B = 1)
    (he : ν.restrict S = (P B)⁻¹ • P.restrict S) : 0 < P B := by
  have hh := congrArg (fun η : Measure Leaf => η B) he
  simp only [Measure.restrict_apply hB,inter_eq_self_of_subset_left hBS,
    Measure.smul_apply,smul_eq_mul,hνB] at hh
  by_contra hp
  have hz : P B = 0 := le_antisymm (not_lt.mp hp) (zero_le _)
  simp only [hz,inv_zero,mul_zero] at hh
  exact one_ne_zero hh

/-- Actual existence with exact whole-leaf normalized diagonal covariance.
The scalar is the reciprocal mass of the scaled reference ball and is proved
strictly positive and finite. All local restrictions and pointwise scalings
come from the original quotient measure. -/
theorem exists_global_lower_covariant_family (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Leaf, Measurable η ∧
      (∀ᵐ q ∂μ,
        IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
          ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      (∀ᵐ q ∂μ,
        η (psi t 1 • q) = (((η q).map (leafScaling t 1)) (ball 0 r))⁻¹ •
          (η q).map (leafScaling t 1) ∧
        0 < ((η q).map (leafScaling t 1)) (ball 0 r) ∧
          ((η q).map (leafScaling t 1)) (ball 0 r) ≠ ∞) := by
  obtain ⟨r,hr,c,index,_,hη,hgood⟩ := exists_global_lower_Radon_family μ hK hμK ht hT
  let η := globalMeasure μ c index t r
  have hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ := by
    have hh := hT.symm ((Homeomorph.smul ((psi t 1)⁻¹)).toMeasurableEquiv)
    change MeasurePreserving (fun q : X => ((psi t 1)⁻¹)⁻¹ • q) μ μ at hh
    simpa only [inv_inv] using hh
  refine ⟨r,hr,η,hη,?_,?_⟩
  · filter_upwards [hgood] with q hq
    exact ⟨hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1⟩
  · filter_upwards [hgood,hA.quasiMeasurePreserving.ae hgood,
      ae_selectedMeasure_succ μ c index t hA] with q hq haq hscale
    apply normalized_scaling_of_restrictions hr (η q) (η (psi t 1 • q)) haq.2.2.1
    intro n
    have hbase (k : ℕ) : ball (0 : Leaf) r ⊆ growingBall r k := by
      simpa only [growingBall,pow_zero,one_mul] using growingBall_mono hr.le (Nat.zero_le k)
    have hp : 0 < selectedMeasure μ c index t n q (ball 0 r) :=
      mass_pos_of_normalized_restriction (η q) _ isOpen_ball.measurableSet (hbase n)
        hq.2.2.1 (hq.2.2.2.2 n).1
    have hp' : 0 < selectedMeasure μ c index t (n+1) (psi t 1 • q) (ball 0 r) :=
      mass_pos_of_normalized_restriction (η (psi t 1 • q)) _ isOpen_ball.measurableSet (hbase (n+1))
        haq.2.2.1 (haq.2.2.2.2 (n+1)).1
    exact projective_restrict_scaling (η q) (η (psi t 1 • q))
      (selectedMeasure μ c index t n q) (selectedMeasure μ c index t (n+1) (psi t 1 • q))
      ht n hp hp' (hscale n (hq.2.2.2.2 n).2.1)
      (hq.2.2.2.2 n).1 (haq.2.2.2.2 (n+1)).1

/-- Canonical data version: covariance is proved for the literal gluing of
this quotient measure's local conditional probabilities. The chart restriction
identities remain available to entropy and ambient-invariance arguments. -/
theorem exists_global_lower_covariant_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : ℕ → Chart, ∃ index : X → ℕ,
      Measurable index ∧ Measurable (globalMeasure μ c index t r) ∧
      (∀ᵐ q ∂μ,
        IsLocallyFiniteMeasure (globalMeasure μ c index t r q) ∧
        (globalMeasure μ c index t r q).Regular ∧
        globalMeasure μ c index t r q (ball 0 r)=1 ∧
        (∀ ε : ℝ, 0<ε → 0<globalMeasure μ c index t r q (ball 0 ε)) ∧
        ∀ n : ℕ,
          (globalMeasure μ c index t r q).restrict (growingBall r n)=
            (selectedMeasure μ c index t n q (ball 0 r))⁻¹ •
              (selectedMeasure μ c index t n q).restrict (growingBall r n) ∧
          q∈(selectedChart c index t n q).image ∧
          q∈BBEKPlaqueSelection.safeImage (selectedChart c index t n q) ((4 : ℝ)^n*r)) ∧
      (∀ᵐ q ∂μ,
        globalMeasure μ c index t r (psi t 1 • q)=
          (((globalMeasure μ c index t r q).map (leafScaling t 1)) (ball 0 r))⁻¹ •
            (globalMeasure μ c index t r q).map (leafScaling t 1) ∧
        0<((globalMeasure μ c index t r q).map (leafScaling t 1)) (ball 0 r) ∧
          ((globalMeasure μ c index t r q).map (leafScaling t 1)) (ball 0 r)≠∞) := by
  obtain ⟨r,hr,c,index,hi,hη,hgood⟩ := exists_global_lower_Radon_family μ hK hμK ht hT
  let η := globalMeasure μ c index t r
  have hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ := by
    have hh := hT.symm ((Homeomorph.smul ((psi t 1)⁻¹)).toMeasurableEquiv)
    change MeasurePreserving (fun q : X => ((psi t 1)⁻¹)⁻¹ • q) μ μ at hh
    simpa only [inv_inv] using hh
  refine ⟨r,hr,c,index,hi,hη,hgood,?_⟩
  filter_upwards [hgood,hA.quasiMeasurePreserving.ae hgood,
    ae_selectedMeasure_succ μ c index t hA] with q hq haq hscale
  apply normalized_scaling_of_restrictions hr (η q) (η (psi t 1 • q)) haq.2.2.1
  intro n
  have hbase (k : ℕ) : ball (0 : Leaf) r ⊆ growingBall r k := by
    simpa only [growingBall,pow_zero,one_mul] using growingBall_mono hr.le (Nat.zero_le k)
  have hp : 0<selectedMeasure μ c index t n q (ball 0 r) :=
    mass_pos_of_normalized_restriction (η q) _ isOpen_ball.measurableSet (hbase n)
      hq.2.2.1 (hq.2.2.2.2 n).1
  have hp' : 0<selectedMeasure μ c index t (n+1) (psi t 1 • q) (ball 0 r) :=
    mass_pos_of_normalized_restriction (η (psi t 1 • q)) _ isOpen_ball.measurableSet (hbase (n+1))
      haq.2.2.1 (haq.2.2.2.2 (n+1)).1
  exact projective_restrict_scaling (η q) (η (psi t 1 • q))
    (selectedMeasure μ c index t n q) (selectedMeasure μ c index t (n+1) (psi t 1 • q))
    ht n hp hp' (hscale n (hq.2.2.2.2 n).2.1)
    (hq.2.2.2.2 n).1 (haq.2.2.2.2 (n+1)).1

end VV.BBEKGlobalLowerCovariance




