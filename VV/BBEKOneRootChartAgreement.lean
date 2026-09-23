import VV.BBEKOneRootGlobal

/-! The actual full root measure agrees projectively with every genuine
local chart on every safe centered ball. This supplies the localization needed
for ambient invariance reconstruction and comparisons with other diagonals. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKOneRootChartAgreement
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseAtlas BBEKPlaqueSelection BBEKExpandedPlaques BBEKSelectedPlaques
  BBEKRootLeafKernel BBEKOneRootLocal BBEKOneRootGlobal BBEKRootGrowingGlue
  BBEKOneRootSafe

/-- The stronger joint safe-chart condition is monotone in its radius. -/
theorem safeImage_antitone (c : Chart) {R S : ℝ} (hRS : R ≤ S) :
    safeImage c S ⊆ safeImage c R := by
  intro q hq
  obtain ⟨p,hp,hpq⟩ := hq
  refine ⟨p,?_,hpq⟩
  intro u hu
  exact hp u (closedBall_subset_closedBall hRS hu)

section General
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U] [SigmaCompactSpace U]

/-- Exact local extension and safe geometry, both already proved by the
actual gluing construction. -/
def Pieces (s : GroupParams ≃ₜ B × U) (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℕ → Chart) (index : X → ℕ) (t r : ℝ) (q : X) : Prop :=
  globalMeasureWith s μ c index t r q (ball 0 r)=1 ∧
    ∀ n : ℕ,
      (globalMeasureWith s μ c index t r q).restrict (growingBall r n)=
        (selectedMeasureWith s μ c index t n q (ball 0 r))⁻¹ •
          (selectedMeasureWith s μ c index t n q).restrict (growingBall r n) ∧
      q∈safeImage (selectedChart c index t n q) ((4 : ℝ)^n*r)

theorem ae_globalMeasureWith_chart_agreement
    (s : GroupParams ≃ₜ B × U) (μ : Measure X) [IsProbabilityMeasure μ]
    (hcompat : ∀ c d : Chart, ∀ᵐ q ∂μ, ∀ R : ℝ, 0<R →
      q∈safeImage c R → q∈safeImage d R →
      ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
        (localMeasureWith s μ c q).restrict (ball 0 R)=
          a • (localMeasureWith s μ d q).restrict (ball 0 R))
    (c : ℕ → Chart) (index : X → ℕ) (t : ℝ) {r : ℝ} (hr : 0<r)
    (hpieces : ∀ᵐ q ∂μ, Pieces s μ c index t r q) (d : Chart) :
    ∀ᵐ q ∂μ, ∀ R : ℝ, 0<R → q∈safeImage d R →
      ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
        (globalMeasureWith s μ c index t r q).restrict (ball 0 R)=
          a • (localMeasureWith s μ d q).restrict (ball 0 R) := by
  have hall : ∀ᵐ q ∂μ, ∀ n k : ℕ, ∀ R : ℝ, 0<R →
      q∈safeImage (expandedChart (c k) t n) R → q∈safeImage d R →
      ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
        (localMeasureWith s μ (expandedChart (c k) t n) q).restrict (ball 0 R)=
          a • (localMeasureWith s μ d q).restrict (ball 0 R) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact hcompat _ d
  filter_upwards [hpieces,hall] with q hq hc R hR hqR
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (R/r) (by norm_num : (1 : ℝ)<4)
  have hRn : R≤(4 : ℝ)^n*r := ((div_lt_iff₀ hr).mp hn).le
  have hsmall : ball (0 : U) R ⊆ growingBall r n := ball_subset_ball hRn
  have hsafe : q∈safeImage (selectedChart c index t n q) R :=
    safeImage_antitone _ hRn (hq.2 n).2
  obtain ⟨a,ha,haf,he⟩ := hc n (index (((psi t 1)⁻¹)^n • q)) R hR hsafe hqR
  let P := selectedMeasureWith s μ c index t n q
  have hres : (globalMeasureWith s μ c index t r q).restrict (ball 0 R)=
      (P (ball 0 r))⁻¹ • P.restrict (ball 0 R) := by
    have hh : (globalMeasureWith s μ c index t r q).restrict (growingBall r n)=
        ((P (ball 0 r))⁻¹ • P).restrict (growingBall r n) := by
      rw [Measure.restrict_smul]
      exact (hq.2 n).1
    have hh' := Measure.restrict_congr_mono hsmall hh
    rwa [Measure.restrict_smul] at hh'
  have hbase : ball (0 : U) r ⊆ growingBall r n := by
    simpa only [growingBall,pow_zero,one_mul] using growingBall_mono hr.le (Nat.zero_le n)
  have hm := congrArg (fun ν : Measure U => ν (ball 0 r)) (hq.2 n).1
  simp only [Measure.restrict_apply isOpen_ball.measurableSet,
    inter_eq_self_of_subset_left hbase,Measure.smul_apply,smul_eq_mul,hq.1] at hm
  have hP : P (ball 0 r)≠0 := by
    intro hz
    change (1 : ℝ≥0∞)=(P (ball 0 r))⁻¹*P (ball 0 r) at hm
    rw [hz,mul_zero] at hm
    exact one_ne_zero hm
  have hPf : P (ball 0 r)≠∞ := measure_ne_top P _
  refine ⟨(P (ball 0 r))⁻¹*a,mul_ne_zero (ENNReal.inv_ne_zero.mpr hPf) ha,
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hP) haf,?_⟩
  rw [hres]
  change (P (ball 0 r))⁻¹ • P.restrict (ball 0 R)=_
  change P.restrict (ball 0 R)=a • (localMeasureWith s μ d q).restrict (ball 0 R) at he
  rw [he,smul_smul]
end General

/-- Real-root specialization uses the actual proved chart compatibility. -/
theorem ae_real_globalMeasure_chart_agreement (μ : Measure X) [IsProbabilityMeasure μ]
    (c : ℕ → Chart) (index : X → ℕ) (t : ℝ) {r : ℝ} (hr : 0<r)
    (hpieces : ∀ᵐ q ∂μ, Pieces realSplit μ c index t r q) (d : Chart) :
    ∀ᵐ q ∂μ, ∀ R : ℝ, 0<R → q∈safeImage d R →
      ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
        (globalMeasureWith realSplit μ c index t r q).restrict (ball 0 R)=
          a • (realLocalMeasure μ d q).restrict (ball 0 R) :=
  ae_globalMeasureWith_chart_agreement realSplit μ (ae_real_projective_on_safe_balls μ)
    c index t hr hpieces d

/-- The 2-adic-root specialization likewise has no overlap-compatibility
assumption; it uses the theorem about the original quotient measure. -/
theorem ae_padic_globalMeasure_chart_agreement (μ : Measure X) [IsProbabilityMeasure μ]
    (c : ℕ → Chart) (index : X → ℕ) (t : ℝ) {r : ℝ} (hr : 0<r)
    (hpieces : ∀ᵐ q ∂μ, Pieces padicSplit μ c index t r q) (d : Chart) :
    ∀ᵐ q ∂μ, ∀ R : ℝ, 0<R → q∈safeImage d R →
      ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
        (globalMeasureWith padicSplit μ c index t r q).restrict (ball 0 R)=
          a • (padicLocalMeasure μ d q).restrict (ball 0 R) :=
  ae_globalMeasureWith_chart_agreement padicSplit μ (ae_padic_projective_on_safe_balls μ)
    c index t hr hpieces d

end VV.BBEKOneRootChartAgreement


