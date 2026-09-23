import VV.BBEKOneRootSafe
import VV.BBEKRootGrowingGlue

/-! Actual measurable Radon conditional families for the separate real and
2-adic lower roots. Projective compatibility is derived from the quotient
measure; it is not an assumption of either final existence theorem. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKOneRootGlobal
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKExpandedPlaques BBEKSelectedPlaques BBEKRootLeafKernel BBEKOneRootLocal
  BBEKOneRootSafe BBEKRootGrowingGlue BBEKSafeBallCompatibility
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

section General
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U] [SigmaCompactSpace U]

def selectedMeasureWith (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (c : ℕ → Chart) (index : X → ℕ)
    (t : ℝ) (n : ℕ) (q : X) : Measure U :=
  localMeasureWith s μ (selectedChart c index t n q) q

set_option maxHeartbeats 1000000 in
theorem measurable_selectedMeasureWith (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (c : ℕ → Chart) {index : X → ℕ}
    (hi : Measurable index) (t : ℝ) (n : ℕ) :
    Measurable (selectedMeasureWith s μ c index t n) := by
  have hf : Measurable (fun p : X × ℕ =>
      localMeasureWith s μ (expandedChart (c p.2) t n) p.1) :=
    measurable_from_prod_countable
      (fun k => measurable_localMeasureWith s μ (expandedChart (c k) t n))
  exact hf.comp (measurable_id.prodMk (hi.comp (continuous_const_smul _).measurable))

instance selectedMeasureWith_probability (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (c : ℕ → Chart) (index : X → ℕ)
    (t : ℝ) (n : ℕ) (q : X) :
    IsProbabilityMeasure (selectedMeasureWith s μ c index t n q) :=
  localMeasureWith_probability s μ _ q

def globalMeasureWith (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (c : ℕ → Chart) (index : X → ℕ) (t r : ℝ) : X → Measure U :=
  normalizedGlue r (selectedMeasureWith s μ c index t)

theorem measurable_globalMeasureWith (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (c : ℕ → Chart) {index : X → ℕ}
    (hi : Measurable index) (t r : ℝ) :
    Measurable (globalMeasureWith s μ c index t r) :=
  measurable_normalizedGlue r _ (fun n => measurable_selectedMeasureWith s μ c hi t n)

/-- Internal gluing lemma, applied below only to the already proved actual
real and 2-adic chart compatibility theorems. -/
theorem exists_global_Radon_familyWith (s : GroupParams ≃ₜ B × U)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hcompat : ∀c d : Chart, ∀ᵐ q ∂μ, ∀R : ℝ, 0<R →
      q∈safeImage c R → q∈safeImage d R →
      ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
        (localMeasureWith s μ c q).restrict (ball 0 R)=
          a • (localMeasureWith s μ d q).restrict (ball 0 R))
    {K : Set X} (hK : IsCompact K) (hμK : μ K=1)
    {t : ℝ} (ht : Real.log 2≤t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃r : ℝ, 0<r ∧ ∃c : ℕ → Chart, ∃index : X → ℕ,
      Measurable index ∧ Measurable (globalMeasureWith s μ c index t r) ∧
      (∀ᵐ q ∂μ,
        IsLocallyFiniteMeasure (globalMeasureWith s μ c index t r q) ∧
        (globalMeasureWith s μ c index t r q).Regular ∧
        globalMeasureWith s μ c index t r q (ball 0 r)=1 ∧
        (∀ε : ℝ, 0<ε → 0<globalMeasureWith s μ c index t r q (ball 0 ε)) ∧
        ∀n : ℕ,
          (globalMeasureWith s μ c index t r q).restrict (growingBall r n)=
            (selectedMeasureWith s μ c index t n q (ball 0 r))⁻¹ •
              (selectedMeasureWith s μ c index t n q).restrict (growingBall r n) ∧
          q∈(selectedChart c index t n q).image ∧
          q∈safeImage (selectedChart c index t n q) ((4 : ℝ)^n*r)) := by
  obtain ⟨r,hr,c,index,hi,_,hpieces⟩ :=
    exists_measurable_expanding_local_family μ hK hμK ht hT
  have hpositive : ∀ᵐ q ∂μ, ∀n k : ℕ,
      q∈(expandedChart (c k) t n).image →
        ∀ε : ℝ, 0<ε → 0<localMeasureWith s μ (expandedChart (c k) t n) q (ball 0 ε) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact (ae_restrict_iff' (expandedChart (c k) t n).isOpen_image.measurableSet).mp
      (ae_localMeasureWith_ball_pos s μ _)
  have hcompatible : ∀ᵐ q ∂μ, ∀n k m j : ℕ, ∀R : ℝ, 0<R →
      q∈safeImage (expandedChart (c k) t n) R →
      q∈safeImage (expandedChart (c j) t m) R →
      ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
        (localMeasureWith s μ (expandedChart (c k) t n) q).restrict (ball 0 R)=
          a • (localMeasureWith s μ (expandedChart (c j) t m) q).restrict (ball 0 R) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro j
    exact hcompat _ _
  refine ⟨r,hr,c,index,hi,measurable_globalMeasureWith s μ c hi t r,?_⟩
  filter_upwards [hpieces,hpositive,hcompatible] with q hq hpos hprojective
  have hsafe (n : ℕ) {R : ℝ} (hR : R≤(4 : ℝ)^n*r) :
      q∈safeImage (selectedChart c index t n q) R := by
    refine ⟨chartCoordinates (selectedChart c index t n q) q,?_,(hq n).1⟩
    intro u hu
    exact (hq n).2.1 u ((show ‖u‖≤R by simpa only [mem_closedBall,dist_zero_right] using hu).trans hR)
  have himage (n : ℕ) : q∈(selectedChart c index t n q).image :=
    safeImage_subset_image _ (by positivity : (0 : ℝ)≤4^n*r) (hsafe n le_rfl)
  have hpos' (n : ℕ) (ε : ℝ) (hε : 0<ε) :
      0<selectedMeasureWith s μ c index t n q (ball 0 ε) :=
    hpos n (index (((psi t 1)⁻¹)^n • q)) (himage n) ε hε
  have hproj (n m : ℕ) : ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
      (selectedMeasureWith s μ c index t n q).restrict (growingBall r n ∩ growingBall r m)=
        a • (selectedMeasureWith s μ c index t m q).restrict (growingBall r n ∩ growingBall r m) := by
    rw [growingBall_inter hr.le]
    have hn : (4 : ℝ)^(min n m)*r≤(4 : ℝ)^n*r :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (min_le_left n m)) hr.le
    have hm : (4 : ℝ)^(min n m)*r≤(4 : ℝ)^m*r :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (min_le_right n m)) hr.le
    exact hprojective n (index (((psi t 1)⁻¹)^n • q)) m
      (index (((psi t 1)⁻¹)^m • q)) ((4 : ℝ)^(min n m)*r) (by positivity)
      (hsafe n hn) (hsafe m hm)
  obtain ⟨hfinite,hregular,hnormal,hres⟩ :=
    normalizedGlue_properties hr (selectedMeasureWith s μ c index t) q (fun n => hpos' n r hr) hproj
  refine ⟨hfinite,hregular,hnormal,?_,fun n => ⟨hres n,himage n,hsafe n le_rfl⟩⟩
  intro ε hε
  let R := min ε r
  have hR : 0<R := lt_min hε hr
  have hB : ball (0 : U) R ⊆ growingBall r 0 := by
    apply ball_subset_ball
    simpa only [pow_zero,one_mul] using min_le_right ε r
  have he := congrArg (fun ν : Measure U => ν (ball 0 R)) (hres 0)
  simp only [Measure.restrict_apply isOpen_ball.measurableSet,
    inter_eq_self_of_subset_left hB,Measure.smul_apply,smul_eq_mul] at he
  apply lt_of_lt_of_le _ (measure_mono (ball_subset_ball (min_le_left ε r)))
  change 0<normalizedGlue r (selectedMeasureWith s μ c index t) q (ball 0 R)
  rw [he]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (hpos' 0 R hR).ne'
end General

theorem exists_real_lower_Radon_family (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K=1)
    {t : ℝ} (ht : Real.log 2≤t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃r : ℝ, 0<r ∧ ∃c : ℕ → Chart, ∃index : X → ℕ,
      Measurable index ∧ Measurable (globalMeasureWith realSplit μ c index t r) ∧
      (∀ᵐ q ∂μ,
        IsLocallyFiniteMeasure (globalMeasureWith realSplit μ c index t r q) ∧
        (globalMeasureWith realSplit μ c index t r q).Regular ∧
        globalMeasureWith realSplit μ c index t r q (ball 0 r)=1 ∧
        (∀ε : ℝ, 0<ε → 0<globalMeasureWith realSplit μ c index t r q (ball 0 ε)) ∧
        ∀n : ℕ,
          (globalMeasureWith realSplit μ c index t r q).restrict (growingBall r n)=
            (selectedMeasureWith realSplit μ c index t n q (ball 0 r))⁻¹ •
              (selectedMeasureWith realSplit μ c index t n q).restrict (growingBall r n) ∧
          q∈(selectedChart c index t n q).image ∧
          q∈safeImage (selectedChart c index t n q) ((4 : ℝ)^n*r)) :=
  exists_global_Radon_familyWith realSplit μ (ae_real_projective_on_safe_balls μ) hK hμK ht hT

theorem exists_padic_lower_Radon_family (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K=1)
    {t : ℝ} (ht : Real.log 2≤t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃r : ℝ, 0<r ∧ ∃c : ℕ → Chart, ∃index : X → ℕ,
      Measurable index ∧ Measurable (globalMeasureWith padicSplit μ c index t r) ∧
      (∀ᵐ q ∂μ,
        IsLocallyFiniteMeasure (globalMeasureWith padicSplit μ c index t r q) ∧
        (globalMeasureWith padicSplit μ c index t r q).Regular ∧
        globalMeasureWith padicSplit μ c index t r q (ball 0 r)=1 ∧
        (∀ε : ℝ, 0<ε → 0<globalMeasureWith padicSplit μ c index t r q (ball 0 ε)) ∧
        ∀n : ℕ,
          (globalMeasureWith padicSplit μ c index t r q).restrict (growingBall r n)=
            (selectedMeasureWith padicSplit μ c index t n q (ball 0 r))⁻¹ •
              (selectedMeasureWith padicSplit μ c index t n q).restrict (growingBall r n) ∧
          q∈(selectedChart c index t n q).image ∧
          q∈safeImage (selectedChart c index t n q) ((4 : ℝ)^n*r)) :=
  exists_global_Radon_familyWith padicSplit μ (ae_padic_projective_on_safe_balls μ) hK hμK ht hT

end VV.BBEKOneRootGlobal

