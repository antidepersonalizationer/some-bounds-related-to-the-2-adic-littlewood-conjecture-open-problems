import VV.BBEKOneRootTranslation
import VV.BBEKOneRootLocalDiagonal

/-! Invariance of actual normalized root measures under a diagonal time
that acts trivially on the corresponding root coordinate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Function
open scoped Topology ENNReal
namespace VV.BBEKOneRootDiagonalNatural
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
open BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
open BBEKLocalRootFamily BBEKRootLeafKernel BBEKOneRootLocal
open BBEKExpandedPlaques BBEKSelectedPlaques BBEKRootGrowingGlue
open BBEKOneRootGlobal BBEKOneRootCovariance BBEKOneRootSafe
open BBEKSafeBallCompatibility BBEKOneRootTranslation BBEKOneRootLocalDiagonal

theorem safeImage_translate_of_bound (c : Chart) (a : ℝ) (m : ℤ)
    {R M : ℝ} (q : X) (hq : q ∈ safeImage c M)
    (hbound : ∀ v : Leaf, ‖v‖ ≤ R → ‖(leafScaling a m).symm v‖ ≤ M) :
    psi a m • q ∈ safeImage (translateChart c a m) R := by
  obtain ⟨p,hp,hpq⟩ := hq
  refine ⟨psiParams a m p,?_,?_⟩
  · intro v hv
    let w := (leafScaling a m).symm v
    have hw : leafShift p w ∈ c.domain := hp w (by
      simpa only [mem_closedBall,dist_zero_right] using
        hbound v (by simpa only [mem_closedBall,dist_zero_right] using hv))
    refine ⟨leafShift p w,hw,?_⟩
    rw [psiParams_leafShift]
    simp only [w,Homeomorph.apply_symm_apply]
  · change quotientCoordinates (psi a m*c.base) (psiParams a m p) = _
    rw [quotient_diagonal_params,hpq]

section Root
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U] [SigmaCompactSpace U]

theorem canonical_invariant_of_trivial_root_scaling
    (s : GroupParams ≃ₜ B × U) (β : B ≃ₜ B) (a : ℝ) (m : ℤ)
    (hcoords : ∀ p, s (psiParams a m p) = Prod.map β id (s p))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hA : MeasurePreserving (fun q : X => psi a m • q) μ μ)
    (hcompat : ∀ c d : Chart, ∀ᵐ q ∂μ, ∀ R : ℝ, 0 < R →
      q ∈ safeImage c R → q ∈ safeImage d R →
      ∃ b : ℝ≥0∞, b ≠ 0 ∧ b ≠ ∞ ∧
        (localMeasureWith s μ c q).restrict (ball 0 R) =
          b • (localMeasureWith s μ d q).restrict (ball 0 R))
    {t r : ℝ} (hr : 0 < r) (η : X → Measure U)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily s μ t r η) :
    ∀ᵐ q ∂μ, η (psi a m • q) = η q := by
  obtain ⟨c,index,hi,hη,hres⟩ := hcanonical
  have hcanonical' : IsConstructedRootFamily s μ t r η := ⟨c,index,hi,hη,hres⟩
  have hcomp : ∀ᵐ q ∂μ, ∀ n k : ℕ, ∀ R : ℝ, 0 < R →
      q ∈ safeImage (translateChart (expandedChart (c k) t n) a m) R →
      ∃ b : ℝ≥0∞, b ≠ 0 ∧ b ≠ ∞ ∧
        (η q).restrict (ball 0 R) =
          b • (localMeasureWith s μ (translateChart (expandedChart (c k) t n) a m) q).restrict (ball 0 R) :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun k =>
      canonical_projective_on_chart s μ hcompat hr η hcanonical' _
  have hlocal : ∀ᵐ q ∂μ, ∀ n k : ℕ,
      q ∈ (expandedChart (c k) t n).image →
      localMeasureWith s μ (translateChart (expandedChart (c k) t n) a m) (psi a m • q) =
        localMeasureWith s μ (expandedChart (c k) t n) q := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    have hh := ae_localMeasureWith_translate s β (Homeomorph.refl U)
      (fun _ _ => rfl) μ (expandedChart (c k) t n) a m hcoords hA
    simpa only [Homeomorph.refl_apply,Measure.map_id] using
      ((ae_restrict_iff' (Chart.isOpen_image _).measurableSet).mp hh)
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
  filter_upwards [hres,hpos,hlocal,hnormal,hA.quasiMeasurePreserving.ae hnormal,
    hA.quasiMeasurePreserving.ae hcomp] with q hqr hp hloc hn hn' hcomp'
  have hproj : ∀ n : ℕ, ∃ b : ℝ≥0∞, b ≠ 0 ∧ b ≠ ∞ ∧
      (η (psi a m • q)).restrict (growingBall r (n+1)) =
        b • ((η q).map (Homeomorph.refl U)).restrict (growingBall r (n+1)) := by
    intro n
    let R := (4 : ℝ)^(n+1)*r
    have hR : 0 < R := by dsimp [R]; positivity
    obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Leaf) R).bddAbove_image
      (continuous_norm.comp (leafScaling a m).symm.continuous).continuousOn
    obtain ⟨j,hj⟩ := pow_unbounded_of_one_lt ((max M R)/r) (by norm_num : (1 : ℝ) < 4)
    have hMj : max M R ≤ (4 : ℝ)^j*r := ((div_lt_iff₀ hr).mp hj).le
    let D := selectedChart c index t j q
    let P := selectedMeasureWith s μ c index t j q
    have hsafe : psi a m • q ∈ safeImage (translateChart D a m) R := by
      apply safeImage_translate_of_bound D a m q (hqr j).2.2
      intro v hv
      exact (hM ⟨v,by simpa only [mem_closedBall,dist_zero_right] using hv,rfl⟩).trans
        ((le_max_left M R).trans hMj)
    obtain ⟨b,hb,hbf,hbEq⟩ := hcomp' j (index (((psi t 1)⁻¹)^j • q)) R hR hsafe
    have hlocalEq := hloc j (index (((psi t 1)⁻¹)^j • q)) (hqr j).2.1
    change localMeasureWith s μ (translateChart D a m) (psi a m • q) = P at hlocalEq
    change (η (psi a m • q)).restrict (ball 0 R) =
      b • (localMeasureWith s μ (translateChart D a m) (psi a m • q)).restrict (ball 0 R) at hbEq
    rw [hlocalEq] at hbEq
    have hp0 : P (ball 0 r) ≠ 0 :=
      (hp j (index (((psi t 1)⁻¹)^j • q)) (hqr j).2.1).ne'
    have hpf : P (ball 0 r) ≠ ∞ := measure_ne_top P _
    have hsub : ball (0 : U) R ⊆ growingBall r j :=
      ball_subset_ball ((le_max_right M R).trans hMj)
    have hresR : (η q).restrict (ball 0 R) = (P (ball 0 r))⁻¹ • P.restrict (ball 0 R) := by
      have hh : (η q).restrict (growingBall r j) =
          ((P (ball 0 r))⁻¹ • P).restrict (growingBall r j) := by
        rw [Measure.restrict_smul]
        exact (hqr j).1
      have hh' := Measure.restrict_congr_mono hsub hh
      rwa [Measure.restrict_smul] at hh'
    refine ⟨b*P (ball 0 r),mul_ne_zero hb hp0,ENNReal.mul_ne_top hbf hpf,?_⟩
    change (η (psi a m • q)).restrict (ball 0 R) =
      (b*P (ball 0 r)) • ((η q).map id).restrict (ball 0 R)
    rw [Measure.map_id]
    rw [hresR,smul_smul,mul_assoc,ENNReal.mul_inv_cancel hp0 hpf,mul_one]
    exact hbEq
  have he := (normalized_scaling_of_restrictions hr (η q) (η (psi a m • q))
    (Homeomorph.refl U) hn' hproj).1
  change η (psi a m • q) = (((η q).map id) (ball 0 r))⁻¹ • (η q).map id at he
  simpa only [Measure.map_id,hn,inv_one,one_smul] using he
end Root

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem canonical_real_lower_padic_invariant
    (μ : Measure X) [IsFiniteMeasure μ] (n : ℤ)
    (hA : MeasurePreserving (fun q : X => psi 0 n • q) μ μ)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure ℝ)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily realSplit μ t r η) :
    ∀ᵐ q ∂μ, η (psi 0 n • q) = η q :=
  canonical_invariant_of_trivial_root_scaling realSplit (realTransverseScaling 0 n) 0 n
    (by intro p; simpa [realLeafScaling] using realSplit_psiParams 0 n p)
    μ hA (ae_real_projective_on_safe_balls μ) hr η hnormal hcanonical

theorem canonical_padic_lower_real_invariant
    (μ : Measure X) [IsFiniteMeasure μ] (a : ℝ)
    (hA : MeasurePreserving (fun q : X => psi a 0 • q) μ μ)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure Q2)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily padicSplit μ t r η) :
    ∀ᵐ q ∂μ, η (psi a 0 • q) = η q :=
  canonical_invariant_of_trivial_root_scaling padicSplit (padicTransverseScaling a 0) a 0
    (by intro p; simpa [padicLeafScaling] using padicSplit_psiParams a 0 p)
    μ hA (ae_padic_projective_on_safe_balls μ) hr η hnormal hcanonical

end VV.BBEKOneRootDiagonalNatural
