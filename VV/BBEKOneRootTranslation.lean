import VV.BBEKOneRootSupport

/-! Translation covariance of the actual canonical leaf measures.
The quotient measure is not assumed invariant under the root group. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Function
open scoped Topology ENNReal
namespace VV.BBEKOneRootTranslation
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
open BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
open BBEKLocalRootFamily BBEKRootLeafKernel BBEKOneRootLocal
open BBEKExpandedPlaques BBEKSelectedPlaques BBEKRootGrowingGlue
open BBEKOneRootGlobal BBEKOneRootCovariance BBEKOneRootSafe
open BBEKSafeBallCompatibility BBEKLeafwiseStabilizer BBEKOneRootSupport

theorem leafShift_leafShift (p : GroupParams) (u v : Leaf) :
    leafShift (leafShift p u) v = leafShift p (v+u) := by
  simp only [leafShift, Homeomorph.apply_symm_apply]
  congr 2
  exact (add_assoc v u (splitCoordinates p).2).symm

theorem safeImage_root_shift (c : Chart) (q : X) (u : Leaf) {R : ℝ}
    (h : q ∈ safeImage c (R+‖u‖)) :
    x u.1 u.2 • q ∈ safeImage c R := by
  obtain ⟨p,hp,hpq⟩ := h
  refine ⟨leafShift p u, ?_, ?_⟩
  · intro v hv
    rw [leafShift_leafShift]
    apply hp
    have hv' : ‖v‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hv
    simpa only [mem_closedBall,dist_zero_right] using
      (norm_add_le v u).trans (add_le_add_right hv' ‖u‖)
  · rw [quotient_leafShift,hpq]

section Local
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]

omit [BorelSpace B] in
theorem localMeasureWith_root_shift
    (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) (q : X) (u : U)
    (hq : quotientCoordinates c.base (chartCoordinates c q) = q)
    (hu : leafShift (chartCoordinates c q) (axis u) ∈ c.domain) :
    localMeasureWith s μ c (x (axis u).1 (axis u).2 • q) =
      translate (-u) (localMeasureWith s μ c q) := by
  have hcoord : chartCoordinates c (x (axis u).1 (axis u).2 • q) =
      leafShift (chartCoordinates c q) (axis u) := by
    have he := quotient_leafShift c.base (chartCoordinates c q) (axis u)
    rw [hq] at he
    rw [← he]
    exact chartCoordinates_apply c ⟨_,hu⟩
  unfold localMeasureWith
  rw [hcoord,hs]
  change (_ : Measure U).map (fun v => v-(u+(s (chartCoordinates c q)).2)) =
    (((_ : Measure U).map (fun v => v-(s (chartCoordinates c q)).2)).map (fun v => -u+v))
  rw [Measure.map_map (show Measurable (fun v : U => -u+v) from
    measurable_const.add measurable_id)
    (show Measurable (fun v : U => v-(s (chartCoordinates c q)).2) from
      measurable_id.sub measurable_const)]
  congr 1
  funext v
  dsimp only [Function.comp_apply]
  abel

variable [SigmaCompactSpace U]

/-- A conull property transfers to almost every point sampled on the actual leaf.
The property itself need not be measurable. -/
theorem canonical_ae (s : GroupParams ≃ₜ B × U) (root : U → G)
    (hroot : Continuous root)
    (hcoords : ∀ b u v, groupMatrixOf (s.symm (b,v+u)) =
      root v * groupMatrixOf (s.symm (b,u)))
    (μ : Measure X) [IsFiniteMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure U) (hcanonical : IsConstructedRootFamily s μ t r η)
    {P : X → Prop} (hP : ∀ᵐ q ∂μ, P q) :
    ∀ᵐ q ∂μ, ∀ᵐ u ∂η q, P (root u • q) := by
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hgood : ∀ᵐ q ∂μ, q ∈ Nᶜ := by
    apply ae_iff.mpr
    simpa only [mem_compl_iff, not_not] using hN0
  filter_upwards [canonical_supported s root hroot hcoords μ hNm.compl hgood hr η hcanonical]
    with q hq
  filter_upwards [hq] with u hu
  by_contra h
  exact hu (hN h)

omit [SigmaCompactSpace U] in
/-- A constructed whole-leaf measure agrees projectively with any fixed safe chart.
The comparison is simultaneous in the radius, with one conull set per chart. -/
theorem canonical_projective_on_chart
    (s : GroupParams ≃ₜ B × U) (μ : Measure X) [IsFiniteMeasure μ]
    (hcompat : ∀ c d : Chart, ∀ᵐ q ∂μ, ∀ R : ℝ, 0 < R →
      q ∈ safeImage c R → q ∈ safeImage d R →
      ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
        (localMeasureWith s μ c q).restrict (ball 0 R) =
          a • (localMeasureWith s μ d q).restrict (ball 0 R))
    {t r : ℝ} (hr : 0 < r) (η : X → Measure U)
    (hcanonical : IsConstructedRootFamily s μ t r η) (d : Chart) :
    ∀ᵐ q ∂μ, ∀ R : ℝ, 0 < R → q ∈ safeImage d R →
      ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
        (η q).restrict (ball 0 R) = a • (localMeasureWith s μ d q).restrict (ball 0 R) := by
  obtain ⟨c,index,hi,hη,hres⟩ := hcanonical
  have hcomp : ∀ᵐ q ∂μ, ∀ n k : ℕ, ∀ R : ℝ, 0 < R →
      q ∈ safeImage (expandedChart (c k) t n) R → q ∈ safeImage d R →
      ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
        (localMeasureWith s μ (expandedChart (c k) t n) q).restrict (ball 0 R) =
          a • (localMeasureWith s μ d q).restrict (ball 0 R) :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun k => hcompat _ d
  have hpos : ∀ᵐ q ∂μ, ∀ n k : ℕ,
      q ∈ (expandedChart (c k) t n).image →
      0 < localMeasureWith s μ (expandedChart (c k) t n) q (ball 0 r) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact ((ae_restrict_iff' (Chart.isOpen_image _).measurableSet).mp
      (ae_localMeasureWith_ball_pos s μ (expandedChart (c k) t n))).mono
        (fun q hq himg => hq himg r hr)
  filter_upwards [hcomp,hpos,hres] with q hq hp hqr R hR hd
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (R/r) (by norm_num : (1 : ℝ) < 4)
  have hRn : R ≤ (4 : ℝ)^n*r := ((div_lt_iff₀ hr).mp hn).le
  let D := selectedChart c index t n q
  let P := selectedMeasureWith s μ c index t n q
  have hsafe : q ∈ safeImage D R := by
    obtain ⟨p,hs,hpq⟩ := (hqr n).2.2
    refine ⟨p,?_,hpq⟩
    intro u hu
    exact hs u (closedBall_subset_closedBall hRn hu)
  obtain ⟨a,ha,haf,he⟩ := hq n (index (((psi t 1)⁻¹)^n • q)) R hR hsafe hd
  have hp0 : P (ball 0 r) ≠ 0 :=
    (hp n (index (((psi t 1)⁻¹)^n • q)) (hqr n).2.1).ne'
  have hpf : P (ball 0 r) ≠ ∞ := measure_ne_top P _
  have hsub : ball (0 : U) R ⊆ growingBall r n := ball_subset_ball hRn
  have hres' : (η q).restrict (ball 0 R) =
      (P (ball 0 r))⁻¹ • P.restrict (ball 0 R) := by
    have hh : (η q).restrict (growingBall r n) =
        ((P (ball 0 r))⁻¹ • P).restrict (growingBall r n) := by
      rw [Measure.restrict_smul]
      exact (hqr n).1
    have hh' := Measure.restrict_congr_mono hsub hh
    rwa [Measure.restrict_smul] at hh'
  refine ⟨(P (ball 0 r))⁻¹*a,
    mul_ne_zero (ENNReal.inv_ne_zero.mpr hpf) ha,
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp0) haf,?_⟩
  rw [hres']
  change (P (ball 0 r))⁻¹ • (localMeasureWith s μ D q).restrict (ball 0 R) = _
  change (localMeasureWith s μ D q).restrict (ball 0 R) = _ at he
  rw [he,smul_smul]

/-- Whole-leaf translation covariance, derived from the literal chart kernels.
No invariance of the ambient measure under root translations is assumed. -/
theorem canonical_translation_on_conull_set
    (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hcompat : ∀ c d : Chart, ∀ᵐ q ∂μ, ∀ R : ℝ, 0 < R →
      q ∈ safeImage c R → q ∈ safeImage d R →
      ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
        (localMeasureWith s μ c q).restrict (ball 0 R) =
          a • (localMeasureWith s μ d q).restrict (ball 0 R))
    {t r : ℝ} (hr : 0 < r) (η : X → Measure U)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily s μ t r η) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      ∀ q ∈ S, ∀ u : U, x (axis u).1 (axis u).2 • q ∈ S →
      η (x (axis u).1 (axis u).2 • q) =
        ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q) ∧
      0 < (translate (-u) (η q)) (ball 0 r) ∧
      (translate (-u) (η q)) (ball 0 r) ≠ ∞ := by
  obtain ⟨c,index,hi,hη,hres⟩ := hcanonical
  have hcanonical' : IsConstructedRootFamily s μ t r η := ⟨c,index,hi,hη,hres⟩
  have hcomp : ∀ᵐ q ∂μ, ∀ m k : ℕ, ∀ R : ℝ, 0 < R →
      q ∈ safeImage (expandedChart (c k) t m) R →
      ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
        (η q).restrict (ball 0 R) =
          a • (localMeasureWith s μ (expandedChart (c k) t m) q).restrict (ball 0 R) :=
    ae_all_iff.mpr fun m => ae_all_iff.mpr fun k =>
      canonical_projective_on_chart s μ hcompat hr η hcanonical' _
  have hpos : ∀ᵐ q ∂μ, ∀ n k : ℕ,
      q ∈ (expandedChart (c k) t n).image →
      0 < localMeasureWith s μ (expandedChart (c k) t n) q (ball 0 r) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact ((ae_restrict_iff' (Chart.isOpen_image _).measurableSet).mp
      (ae_localMeasureWith_ball_pos s μ (expandedChart (c k) t n))).mono
        (fun q hq himg => hq himg r hr)
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null
    (ae_iff.mp (hnormal.and (hcomp.and (hres.and hpos))))
  refine ⟨Nᶜ,hNm.compl,?_,?_⟩
  · apply ae_iff.mpr
    simpa only [mem_compl_iff,not_not] using hN0
  intro q hq u hqu
  have hqgood := not_not.mp (fun h => hq (hN h))
  have hugood := not_not.mp (fun h => hqu (hN h))
  have hqr := hqgood.2.2.1
  have hp := hqgood.2.2.2
  have hu := And.intro hugood.1 hugood.2.1
  let q' := x (axis u).1 (axis u).2 • q
  let e : U ≃ₜ U := Homeomorph.addLeft (-u)
  change η q' = ((η q).map e (ball 0 r))⁻¹ • (η q).map e ∧
    0 < (η q).map e (ball 0 r) ∧ (η q).map e (ball 0 r) ≠ ∞
  apply normalized_scaling_of_restrictions hr (η q) (η q') e hu.1
  intro n
  let R := (4 : ℝ)^(n+1)*r
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt ((R+‖u‖+‖axis u‖)/r)
    (by norm_num : (1 : ℝ) < 4)
  have hRm : R+‖u‖+‖axis u‖ ≤ (4 : ℝ)^m*r := ((div_lt_iff₀ hr).mp hm).le
  let D := selectedChart c index t m q
  let P := selectedMeasureWith s μ c index t m q
  have hsmaller {a : ℝ} (ha : a ≤ (4 : ℝ)^m*r) : q ∈ safeImage D a := by
    obtain ⟨p,hsafe,hpq⟩ := (hqr m).2.2
    exact ⟨p,fun v hv => hsafe v (closedBall_subset_closedBall ha hv),hpq⟩
  have hqsafe : q ∈ safeImage D (R+‖axis u‖) :=
    hsmaller (by linarith [norm_nonneg u])
  have hq'safe : q' ∈ safeImage D R := safeImage_root_shift D q (axis u) hqsafe
  obtain ⟨b,hb,hbf,hbEq⟩ :=
    hu.2 m (index (((psi t 1)⁻¹)^m • q)) R hR hq'safe
  have hc := chartCoordinates_safe (by positivity : 0 ≤ R+‖axis u‖) hqsafe
  have hshift := localMeasureWith_root_shift s axis hs μ D q u hc.1
    (hc.2 (axis u) (by linarith))
  change localMeasureWith s μ D q' = translate (-u) P at hshift
  change (η q').restrict (ball 0 R) = b • (localMeasureWith s μ D q').restrict (ball 0 R) at hbEq
  rw [hshift] at hbEq
  have hp0 : P (ball 0 r) ≠ 0 :=
    (hp m (index (((psi t 1)⁻¹)^m • q)) (hqr m).2.1).ne'
  have hpf : P (ball 0 r) ≠ ∞ := measure_ne_top P _
  have hpre : e ⁻¹' ball 0 R ⊆ growingBall r m := by
    intro v hv
    have hv' : ‖-u+v‖ < R := by
      change dist (-u+v) 0 < R at hv
      simpa only [dist_zero_right] using hv
    have hvnorm : ‖v‖ ≤ ‖-u+v‖+‖u‖ := by
      have hh := norm_add_le (-u+v) u
      simpa only [neg_add_cancel_comm] using hh
    change dist v 0 < (4 : ℝ)^m*r
    rw [dist_zero_right]
    linarith [norm_nonneg (axis u)]
  have hpreEq : (η q).restrict (e ⁻¹' ball 0 R) =
      (P (ball 0 r))⁻¹ • P.restrict (e ⁻¹' ball 0 R) := by
    have he : (η q).restrict (growingBall r m) =
        ((P (ball 0 r))⁻¹ • P).restrict (growingBall r m) := by
      rw [Measure.restrict_smul]
      exact (hqr m).1
    have he' := Measure.restrict_congr_mono hpre he
    rwa [Measure.restrict_smul] at he'
  have hmap : ((η q).map e).restrict (ball 0 R) =
      (P (ball 0 r))⁻¹ • (P.map e).restrict (ball 0 R) := by
    rw [e.measurableEmbedding.restrict_map,hpreEq,Measure.map_smul,
      ← e.measurableEmbedding.restrict_map]
  refine ⟨b*P (ball 0 r),mul_ne_zero hb hp0,ENNReal.mul_ne_top hbf hpf,?_⟩
  change (η q').restrict (ball 0 R) = (b*P (ball 0 r)) • ((η q).map e).restrict (ball 0 R)
  rw [hmap,smul_smul, mul_assoc,ENNReal.mul_inv_cancel hp0 hpf,mul_one]
  exact hbEq

/-- The same covariance also holds at leaf-almost every translated point. -/
theorem canonical_translation_covariance
    (s : GroupParams ≃ₜ B × U) (axis : U → Leaf) (haxis : Continuous axis)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (hcoords : ∀ b u v, groupMatrixOf (s.symm (b,v+u)) =
      x (axis v).1 (axis v).2 * groupMatrixOf (s.symm (b,u)))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hcompat : ∀ c d : Chart, ∀ᵐ q ∂μ, ∀ R : ℝ, 0 < R →
      q ∈ safeImage c R → q ∈ safeImage d R →
      ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
        (localMeasureWith s μ c q).restrict (ball 0 R) =
          a • (localMeasureWith s μ d q).restrict (ball 0 R))
    {t r : ℝ} (hr : 0 < r) (η : X → Measure U)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily s μ t r η) :
    ∀ᵐ q ∂μ, ∀ᵐ u ∂η q,
      η (x (axis u).1 (axis u).2 • q) =
        ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q) ∧
      0 < (translate (-u) (η q)) (ball 0 r) ∧
      (translate (-u) (η q)) (ball 0 r) ≠ ∞ := by
  obtain ⟨S,hS,hμS,hcov⟩ := canonical_translation_on_conull_set s axis hs
    μ hcompat hr η hnormal hcanonical
  have hleaf := canonical_supported s (fun u => x (axis u).1 (axis u).2)
    (continuous_x.comp haxis) hcoords μ hS hμS hr η hcanonical
  filter_upwards [hμS,hleaf] with q hq hleafq
  exact hleafq.mono (fun u hu => hcov q hq u hu)

end Local

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem canonical_real_lower_translation_on_conull_set
    (μ : Measure X) [IsFiniteMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure ℝ) (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily realSplit μ t r η) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      ∀ q ∈ S, ∀ u : ℝ, x u 0 • q ∈ S →
      η (x u 0 • q) = ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q) ∧
      0 < (translate (-u) (η q)) (ball 0 r) ∧
      (translate (-u) (η q)) (ball 0 r) ≠ ∞ :=
  canonical_translation_on_conull_set realSplit (fun u => (u,0))
    (by intro p u; simp [leafShift,realSplit,splitCoordinates])
    μ (ae_real_projective_on_safe_balls μ) hr η hnormal hcanonical

theorem canonical_padic_lower_translation_on_conull_set
    (μ : Measure X) [IsFiniteMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure Q2) (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily padicSplit μ t r η) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      ∀ q ∈ S, ∀ u : Q2, x 0 u • q ∈ S →
      η (x 0 u • q) = ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q) ∧
      0 < (translate (-u) (η q)) (ball 0 r) ∧
      (translate (-u) (η q)) (ball 0 r) ≠ ∞ :=
  canonical_translation_on_conull_set padicSplit (fun u => (0,u))
    (by intro p u; simp [leafShift,padicSplit,splitCoordinates])
    μ (ae_padic_projective_on_safe_balls μ) hr η hnormal hcanonical

theorem canonical_real_lower_translation
    (μ : Measure X) [IsFiniteMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure ℝ) (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily realSplit μ t r η) :
    ∀ᵐ q ∂μ, ∀ᵐ u ∂η q,
      η (x u 0 • q) = ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q) ∧
      0 < (translate (-u) (η q)) (ball 0 r) ∧
      (translate (-u) (η q)) (ball 0 r) ≠ ∞ :=
  canonical_translation_covariance realSplit (fun u => (u,0))
    (continuous_id.prodMk continuous_const)
    (by intro p u; simp [leafShift,realSplit,splitCoordinates]) realMatrix_leaf_add
    μ (ae_real_projective_on_safe_balls μ) hr η hnormal hcanonical

theorem canonical_padic_lower_translation
    (μ : Measure X) [IsFiniteMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure Q2) (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily padicSplit μ t r η) :
    ∀ᵐ q ∂μ, ∀ᵐ u ∂η q,
      η (x 0 u • q) = ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q) ∧
      0 < (translate (-u) (η q)) (ball 0 r) ∧
      (translate (-u) (η q)) (ball 0 r) ≠ ∞ :=
  canonical_translation_covariance padicSplit (fun u => (0,u))
    (continuous_const.prodMk continuous_id)
    (by intro p u; simp [leafShift,padicSplit,splitCoordinates]) padicMatrix_leaf_add
    μ (ae_padic_projective_on_safe_balls μ) hr η hnormal hcanonical

end VV.BBEKOneRootTranslation
