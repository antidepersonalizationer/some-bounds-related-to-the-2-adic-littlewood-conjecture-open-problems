import VV.BBEKGrowingGlue
import VV.BBEKSafeBallCompatibility

/-! Actual measurable Radon conditional measures on the full joint lower
root R × Q₂, for a compactly supported inverse-diagonal invariant probability.
Projective chart compatibility is proved from the original measure, never
assumed. Covariance and one-dimensional root disintegrations are separate steps. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKGlobalLowerMeasure
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKExpandedPlaques BBEKLocalRootFamily BBEKLeafwiseTrapped
  BBEKSelectedPlaques BBEKGrowingGlue BBEKSafeBallCompatibility

def globalMeasure (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℕ → Chart) (index : X → ℕ) (t r : ℝ) : X → Measure Leaf :=
  normalizedGlue r (selectedMeasure μ c index t)

theorem measurable_globalMeasure (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℕ → Chart) {index : X → ℕ} (hi : Measurable index) (t r : ℝ) :
    Measurable (globalMeasure μ c index t r) :=
  measurable_normalizedGlue r _ (fun n => measurable_selectedMeasure μ c hi t n)

/-- Simultaneous compatibility for every pair from the actual countable
family of expanded charts, including measurably chosen chart indices. -/
theorem ae_expanded_charts_projective (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℕ → Chart) (t : ℝ) :
    ∀ᵐ q ∂μ, ∀ n k m j : ℕ, ∀ R : ℝ, 0 < R →
      q ∈ safeImage (expandedChart (c k) t n) R →
      q ∈ safeImage (expandedChart (c j) t m) R →
      ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
        (localMeasure μ (expandedChart (c k) t n) q).restrict (ball 0 R) =
          a • (localMeasure μ (expandedChart (c j) t m) q).restrict (ball 0 R) := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro j
  exact ae_projective_on_safe_balls μ _ _

/-- The full-leaf Radon measure is an actual measurable function, obtained by
normalizing and gluing genuine chart conditional probabilities. Every claimed
extension identity is proved on one common conull set. -/
theorem exists_global_lower_Radon_family (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : ℕ → Chart, ∃ index : X → ℕ,
      Measurable index ∧ Measurable (globalMeasure μ c index t r) ∧
      (∀ᵐ q ∂μ,
        IsLocallyFiniteMeasure (globalMeasure μ c index t r q) ∧
        (globalMeasure μ c index t r q).Regular ∧
        globalMeasure μ c index t r q (ball 0 r) = 1 ∧
        (∀ ε : ℝ, 0 < ε → 0 < globalMeasure μ c index t r q (ball 0 ε)) ∧
        ∀ n : ℕ,
          (globalMeasure μ c index t r q).restrict (growingBall r n) =
            (selectedMeasure μ c index t n q (ball 0 r))⁻¹ •
              (selectedMeasure μ c index t n q).restrict (growingBall r n) ∧
          q ∈ (selectedChart c index t n q).image ∧
          q ∈ safeImage (selectedChart c index t n q) ((4 : ℝ)^n*r)) := by
  obtain ⟨r,hr,c,index,hi,hm,hpieces⟩ :=
    exists_measurable_expanding_local_family μ hK hμK ht hT
  refine ⟨r,hr,c,index,hi,measurable_globalMeasure μ c hi t r,?_⟩
  filter_upwards [hpieces,ae_expanded_charts_projective μ c t] with q hq hprojective
  have hpos (n : ℕ) : 0 < selectedMeasure μ c index t n q (ball 0 r) := (hq n).2.2 r hr
  have hsafe (n : ℕ) {R : ℝ} (hR : R ≤ (4 : ℝ)^n*r) :
      q ∈ safeImage (selectedChart c index t n q) R := by
    refine ⟨chartCoordinates (selectedChart c index t n q) q,?_,(hq n).1⟩
    intro u hu
    exact (hq n).2.1 u ((show ‖u‖ ≤ R by simpa only [mem_closedBall,dist_zero_right] using hu).trans hR)
  have hproj (n m : ℕ) : ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
      (selectedMeasure μ c index t n q).restrict (growingBall r n ∩ growingBall r m) =
        a • (selectedMeasure μ c index t m q).restrict (growingBall r n ∩ growingBall r m) := by
    rw [growingBall_inter hr.le]
    have hn : (4 : ℝ)^(min n m)*r ≤ (4 : ℝ)^n*r :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (min_le_left n m)) hr.le
    have hm : (4 : ℝ)^(min n m)*r ≤ (4 : ℝ)^m*r :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (min_le_right n m)) hr.le
    exact hprojective n (index (((psi t 1)⁻¹)^n • q)) m
      (index (((psi t 1)⁻¹)^m • q)) ((4 : ℝ)^(min n m)*r) (by positivity)
      (hsafe n hn) (hsafe m hm)
  obtain ⟨hfinite,hregular,hnormal,hres⟩ :=
    normalizedGlue_properties hr (selectedMeasure μ c index t) q hpos hproj
  have himage (n : ℕ) : q ∈ (selectedChart c index t n q).image :=
    safeImage_subset_image _ (by positivity : (0 : ℝ) ≤ 4^n*r) (hsafe n le_rfl)
  refine ⟨hfinite,hregular,hnormal,?_,fun n => ⟨hres n,himage n,hsafe n le_rfl⟩⟩
  intro ε hε
  let R := min ε r
  have hR : 0 < R := lt_min hε hr
  have hB : ball (0 : Leaf) R ⊆ growingBall r 0 := by
    apply ball_subset_ball
    simpa only [pow_zero,one_mul] using min_le_right ε r
  have he := congrArg (fun ν : Measure Leaf => ν (ball 0 R)) (hres 0)
  simp only [Measure.restrict_apply isOpen_ball.measurableSet,
    inter_eq_self_of_subset_left hB,Measure.smul_apply,smul_eq_mul] at he
  apply lt_of_lt_of_le _ (measure_mono (ball_subset_ball (min_le_left ε r)))
  change 0 < normalizedGlue r (selectedMeasure μ c index t) q (ball 0 R)
  rw [he]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) ((hq 0).2.2 R hR).ne'

end VV.BBEKGlobalLowerMeasure



