import VV.BBEKOneRootSelectedDiagonal

/-! Exact normalized scaling covariance of the constructed full joint lower
leaf Radon family. The proof uses literal successive selected plaques. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal
namespace VV.BBEKOneRootCovariance
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseAtlas BBEKSelectedPlaques BBEKRootGrowingGlue
  BBEKOneRootGlobal BBEKProjectiveGlue
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U] [SigmaCompactSpace U]

/-- Comparing successive actual local restrictions gives projective
covariance on one growing ball. -/
theorem projective_restrict_scaling (ν ν' P P' : Measure U)
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {r : ℝ} (e : U ≃ₜ U) (n : ℕ)
    (hpre : e ⁻¹' growingBall r (n+1) ⊆ growingBall r n)
    (hP : 0 < P (ball 0 r)) (hP' : 0 < P' (ball 0 r))
    (he : P' = P.map e)
    (hν : ν.restrict (growingBall r n) =
      (P (ball 0 r))⁻¹ • P.restrict (growingBall r n))
    (hν' : ν'.restrict (growingBall r (n+1)) =
      (P' (ball 0 r))⁻¹ • P'.restrict (growingBall r (n+1))) :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
      ν'.restrict (growingBall r (n+1)) =
        a • (ν.map e).restrict (growingBall r (n+1)) := by
  let α := P (ball 0 r)
  let β := P' (ball 0 r)
  have hres : ν.restrict (e ⁻¹' growingBall r (n+1)) =
      α⁻¹ • P.restrict (e ⁻¹' growingBall r (n+1)) := by
    have hh : ν.restrict (growingBall r n) = (α⁻¹ • P).restrict (growingBall r n) := by
      rw [Measure.restrict_smul]
      exact hν
    have hh' := Measure.restrict_congr_mono (hpre) hh
    rwa [Measure.restrict_smul] at hh'
  have hmap : (ν.map e).restrict (growingBall r (n+1)) =
      α⁻¹ • (P.map e).restrict (growingBall r (n+1)) := by
    rw [e.measurableEmbedding.restrict_map,hres,Measure.map_smul,
      ← e.measurableEmbedding.restrict_map]
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
    (ν ν' : Measure U) (e : U ≃ₜ U) (hnormal : ν' (ball 0 r) = 1)
    (hproj : ∀ n : ℕ, ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
      ν'.restrict (growingBall r (n+1)) =
        a • (ν.map e).restrict (growingBall r (n+1))) :
    ν' = ((ν.map e) (ball 0 r))⁻¹ • ν.map e ∧
      0 < (ν.map e) (ball 0 r) ∧
      (ν.map e) (ball 0 r) ≠ ∞ := by
  have hbase (n : ℕ) : ball (0 : U) r ⊆ growingBall r (n+1) := by
    simpa only [growingBall,pow_zero,one_mul] using growingBall_mono hr.le (Nat.zero_le (n+1))
  have heq (n : ℕ) : ν'.restrict (growingBall r (n+1)) =
      (((ν.map e) (ball 0 r))⁻¹ • ν.map e).restrict
        (growingBall r (n+1)) := by
    obtain ⟨a,ha,haf,he⟩ := hproj n
    have hh := normalize_restrict_of_projective ν' (ν.map e)
      isOpen_ball.measurableSet (hbase n) ha haf he
    simpa only [BBEKProjectiveGlue.normalize,hnormal,inv_one,one_smul] using hh
  have hcover : ⋃ n, growingBall (U := U) r (n+1) = univ := by
    apply eq_univ_of_forall
    intro u
    have hu : u ∈ ⋃ n, growingBall r n := by rw [growingBall_cover hr]; trivial
    obtain ⟨n,hn⟩ := mem_iUnion.mp hu
    exact mem_iUnion.mpr ⟨n,growingBall_mono hr.le (Nat.le_succ n) hn⟩
  have hglobal := Measure.restrict_iUnion_congr.mpr heq
  rw [hcover,Measure.restrict_univ,Measure.restrict_univ] at hglobal
  refine ⟨hglobal,?_⟩
  obtain ⟨a,ha,haf,he⟩ := hproj 0
  have hm := congrArg (fun η : Measure U => η (ball 0 r)) he
  simp only [Measure.restrict_apply isOpen_ball.measurableSet,
    inter_eq_self_of_subset_left (hbase 0),Measure.smul_apply,smul_eq_mul,hnormal] at hm
  have hv : (ν.map e) (ball 0 r) = a⁻¹ := by
    calc
      _ = a⁻¹ * (a*(ν.map e) (ball 0 r)) := by
        rw [← mul_assoc,ENNReal.inv_mul_cancel ha haf,one_mul]
      _ = a⁻¹ := by rw [← hm,mul_one]
  rw [hv]
  exact ⟨ENNReal.inv_pos.mpr haf,ENNReal.inv_ne_top.mpr ha⟩

private theorem mass_pos_of_normalized_restriction (ν P : Measure U)
    {B S : Set U} (hB : MeasurableSet B) (hBS : B ⊆ S) (hνB : ν B = 1)
    (he : ν.restrict S = (P B)⁻¹ • P.restrict S) : 0 < P B := by
  have hh := congrArg (fun η : Measure U => η B) he
  simp only [Measure.restrict_apply hB,inter_eq_self_of_subset_left hBS,
    Measure.smul_apply,smul_eq_mul,hνB] at hh
  by_contra hp
  have hz : P B = 0 := le_antisymm (not_lt.mp hp) (zero_le _)
  simp only [hz,inv_zero,mul_zero] at hh
  exact one_ne_zero hh


open BBEKRootLeafKernel BBEKOneRootLocal BBEKOneRootSafe BBEKOneRootSelectedDiagonal
  BBEKPlaqueSelection BBEKEntropyExpansion

section Construction
variable {B : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology U] [StandardBorelSpace U]

def IsConstructedRootFamily (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (t r : ℝ) (η : X → Measure U) : Prop :=
  ∃c : ℕ → Chart, ∃index : X → ℕ, Measurable index ∧
    η=globalMeasureWith s μ c index t r ∧
    ∀ᵐ q ∂μ, ∀n : ℕ,
      (η q).restrict (growingBall r n)=
        (selectedMeasureWith s μ c index t n q (ball 0 r))⁻¹ •
          (selectedMeasureWith s μ c index t n q).restrict (growingBall r n) ∧
      q∈(selectedChart c index t n q).image ∧
      q∈safeImage (selectedChart c index t n q) ((4 : ℝ)^n*r)

theorem exists_covariant_dataWith
    (s : GroupParams ≃ₜ B × U) (β : B ≃ₜ B) (σ : U ≃ₜ U)
    (hσ : ∀u v : U, σ (u-v)=σ u-σ v)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hcompat : ∀c d : Chart, ∀ᵐ q ∂μ, ∀R : ℝ, 0<R →
      q∈safeImage c R → q∈safeImage d R →
      ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
        (localMeasureWith s μ c q).restrict (ball 0 R)=
          a • (localMeasureWith s μ d q).restrict (ball 0 R))
    {K : Set X} (hK : IsCompact K) (hμK : μ K=1)
    {t : ℝ} (ht : Real.log 2≤t)
    (hcoords : ∀p, s (psiParams t 1 p)=Prod.map β σ (s p))
    (hpre : ∀r : ℝ, ∀n : ℕ, σ ⁻¹' growingBall r (n+1) ⊆ growingBall r n)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃r : ℝ, 0<r ∧ ∃η : X → Measure U, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r)=1 ∧
        ∀ε : ℝ, 0<ε → 0<η q (ball 0 ε)) ∧
      (∀ᵐ q ∂μ,
        η (psi t 1 • q)=((η q).map σ (ball 0 r))⁻¹ • (η q).map σ ∧
        0<(η q).map σ (ball 0 r) ∧ (η q).map σ (ball 0 r)≠∞) ∧
      IsConstructedRootFamily s μ t r η := by
  obtain ⟨r,hr,c,index,hi,hη,hgood⟩ :=
    exists_global_Radon_familyWith s μ hcompat hK hμK ht hT
  let η := globalMeasureWith s μ c index t r
  have hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ := by
    have hh := hT.symm ((Homeomorph.smul ((psi t 1)⁻¹)).toMeasurableEquiv)
    change MeasurePreserving (fun q : X => ((psi t 1)⁻¹)⁻¹ • q) μ μ at hh
    simpa only [inv_inv] using hh
  refine ⟨r,hr,η,hη,?_,?_,?_⟩
  · filter_upwards [hgood] with q hq
    exact ⟨hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1⟩
  · filter_upwards [hgood,hA.quasiMeasurePreserving.ae hgood,
      ae_selectedMeasureWith_succ s β σ hσ μ c index t hcoords hA] with q hq haq hscale
    apply normalized_scaling_of_restrictions hr (η q) (η (psi t 1 • q)) σ haq.2.2.1
    intro n
    have hbase (k : ℕ) : ball (0 : U) r ⊆ growingBall r k := by
      simpa only [growingBall,pow_zero,one_mul] using growingBall_mono hr.le (Nat.zero_le k)
    have hp : 0<selectedMeasureWith s μ c index t n q (ball 0 r) :=
      mass_pos_of_normalized_restriction (η q) _ isOpen_ball.measurableSet (hbase n)
        hq.2.2.1 (hq.2.2.2.2 n).1
    have hp' : 0<selectedMeasureWith s μ c index t (n+1) (psi t 1 • q) (ball 0 r) :=
      mass_pos_of_normalized_restriction (η (psi t 1 • q)) _ isOpen_ball.measurableSet (hbase (n+1))
        haq.2.2.1 (haq.2.2.2.2 (n+1)).1
    exact projective_restrict_scaling (η q) (η (psi t 1 • q))
      (selectedMeasureWith s μ c index t n q)
      (selectedMeasureWith s μ c index t (n+1) (psi t 1 • q))
      σ n (hpre r n) hp hp' (hscale n (hq.2.2.2.2 n).2.1)
      (hq.2.2.2.2 n).1 (haq.2.2.2.2 (n+1)).1
  · refine ⟨c,index,hi,rfl,?_⟩
    filter_upwards [hgood] with q hq
    exact hq.2.2.2.2
end Construction

theorem real_scaling_preimage_growingBall {t r : ℝ} (ht : Real.log 2≤t) (n : ℕ) :
    (realLeafScaling t) ⁻¹' growingBall r (n+1) ⊆ growingBall r n := by
  intro u hu
  have hscale : (4 : ℝ)*‖u‖≤‖realLeafScaling t u‖ := by
    have hh := expand_iterate_norm_lower ht (u,0) 1
    have he : 4*|u|≤Real.exp (2*t)*|u| ∨ 4*|u|≤0 := by
      simpa [expand,leafScaling,realLeafScaling,Prod.norm_def] using hh
    change 4*|u|≤‖Real.exp (2*t)*u‖
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.norm_eq_abs]
    rcases he with he | he
    · exact he
    · exact he.trans (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
  have hnorm : ‖realLeafScaling t u‖<(4 : ℝ)^(n+1)*r := by
    simpa only [growingBall,mem_preimage,mem_ball,dist_zero_right] using hu
  change dist u 0<(4 : ℝ)^n*r
  rw [dist_zero_right]
  rw [pow_succ] at hnorm
  nlinarith

theorem padic_scaling_preimage_growingBall {r : ℝ} (n : ℕ) :
    (padicLeafScaling 1) ⁻¹' growingBall r (n+1) ⊆ growingBall r n := by
  intro u hu
  have hscale : (4 : ℝ)*‖u‖≤‖padicLeafScaling 1 u‖ := by
    have hh := expand_iterate_norm_lower (le_rfl : Real.log 2≤Real.log 2) (0,u) 1
    have he : 4*‖u‖≤0 ∨ 4*‖u‖≤(‖(2 : Q2)‖^2)⁻¹*‖u‖ := by
      simpa [expand,leafScaling,padicLeafScaling,Prod.norm_def] using hh
    have hh' : 4*‖u‖≤(‖(2 : Q2)‖^2)⁻¹*‖u‖ := by
      rcases he with he | he
      · exact he.trans (by positivity)
      · exact he
    simpa [padicLeafScaling] using hh'
  have hnorm : ‖padicLeafScaling 1 u‖<(4 : ℝ)^(n+1)*r := by
    simpa only [growingBall,mem_preimage,mem_ball,dist_zero_right] using hu
  change dist u 0<(4 : ℝ)^n*r
  rw [dist_zero_right]
  rw [pow_succ] at hnorm
  nlinarith

theorem exists_real_lower_covariant_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K=1)
    {t : ℝ} (ht : Real.log 2≤t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃r : ℝ, 0<r ∧ ∃η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r)=1 ∧
        ∀ε : ℝ, 0<ε → 0<η q (ball 0 ε)) ∧
      (∀ᵐ q ∂μ,
        η (psi t 1 • q)=((η q).map (realLeafScaling t) (ball 0 r))⁻¹ •
          (η q).map (realLeafScaling t) ∧
        0<(η q).map (realLeafScaling t) (ball 0 r) ∧
          (η q).map (realLeafScaling t) (ball 0 r)≠∞) ∧
      IsConstructedRootFamily realSplit μ t r η :=
  exists_covariant_dataWith realSplit (realTransverseScaling t 1) (realLeafScaling t)
    (fun u v => by simp [realLeafScaling,mul_sub]) μ (ae_real_projective_on_safe_balls μ)
    hK hμK ht (realSplit_psiParams t 1) (fun _ => real_scaling_preimage_growingBall ht) hT

theorem exists_padic_lower_covariant_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K=1)
    {t : ℝ} (ht : Real.log 2≤t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃r : ℝ, 0<r ∧ ∃η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r)=1 ∧
        ∀ε : ℝ, 0<ε → 0<η q (ball 0 ε)) ∧
      (∀ᵐ q ∂μ,
        η (psi t 1 • q)=((η q).map (padicLeafScaling 1) (ball 0 r))⁻¹ •
          (η q).map (padicLeafScaling 1) ∧
        0<(η q).map (padicLeafScaling 1) (ball 0 r) ∧
          (η q).map (padicLeafScaling 1) (ball 0 r)≠∞) ∧
      IsConstructedRootFamily padicSplit μ t r η :=
  exists_covariant_dataWith padicSplit (padicTransverseScaling t 1) (padicLeafScaling 1)
    (fun u v => by simp [padicLeafScaling,mul_sub]) μ (ae_padic_projective_on_safe_balls μ)
    hK hμK ht (padicSplit_psiParams t 1) (fun _ => padic_scaling_preimage_growingBall) hT

end VV.BBEKOneRootCovariance



