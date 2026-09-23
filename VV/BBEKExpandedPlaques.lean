import VV.BBEKPlaqueSelection
import VV.BBEKLeafwiseTrapped
import VV.BBEKRootLeafKernel
import VV.BBEKEntropyExpansion

/-! Diagonal translates of actual charts and arbitrarily large injective
plaques on compact inverse-trapped lower-root orbits. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped Topology ENNReal
namespace VV.BBEKExpandedPlaques
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKRootLeafKernel
  BBEKEntropyExpansion

def paramsHomeomorph (t : ℝ) (n : ℤ) : GroupParams ≃ₜ GroupParams :=
  (realParamsScaling t).prodCongr (padicParamsScaling n)

theorem paramsHomeomorph_eq (t : ℝ) (n : ℤ) :
    (paramsHomeomorph t n : GroupParams → GroupParams) = psiParams t n := rfl

theorem isOpen_psiParams_image (t : ℝ) (n : ℤ) {V : Set GroupParams} (hV : IsOpen V) :
    IsOpen (psiParams t n '' V) := by
  rw [← paramsHomeomorph_eq]
  exact (paramsHomeomorph t n).isOpenMap V hV

theorem quotient_diagonal_params (c : Chart) (t : ℝ) (n : ℤ) (p : GroupParams) :
    quotientCoordinates (psi t n*c.base) (psiParams t n p) =
      psi t n • quotientCoordinates c.base p := by
  unfold quotientCoordinates
  rw [← psi_conjugate_coordinates,smul_mk]
  congr 1
  group

def translateChart (c : Chart) (t : ℝ) (n : ℤ) : Chart where
  base := psi t n*c.base
  domain := psiParams t n '' c.domain
  isOpen_domain := isOpen_psiParams_image t n c.isOpen_domain
  embedding := by
    apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact (continuous_quotientCoordinates _).comp continuous_subtype_val
    · rintro ⟨p,⟨u,hu,rfl⟩⟩ ⟨q,⟨v,hv,rfl⟩⟩ he
      apply Subtype.ext
      change quotientCoordinates (psi t n*c.base) (psiParams t n u) =
        quotientCoordinates (psi t n*c.base) (psiParams t n v) at he
      rw [quotient_diagonal_params,quotient_diagonal_params] at he
      have hh := congrArg (fun z : X => (psi t n)⁻¹ • z) he
      simp only [inv_smul_smul] at hh
      have hi : Function.Injective (c.domain.restrict (quotientCoordinates c.base)) := c.embedding.injective
      have hh' : c.domain.restrict (quotientCoordinates c.base) ⟨u,hu⟩ =
          c.domain.restrict (quotientCoordinates c.base) ⟨v,hv⟩ := hh
      have huv : (⟨u,hu⟩ : c.domain) = ⟨v,hv⟩ := hi hh'
      exact congrArg (psiParams t n) (congrArg Subtype.val huv)
    · exact (quotientCoordinates_isOpenMap _).restrict
        (isOpen_psiParams_image t n c.isOpen_domain)

theorem psiParams_leafShift (t : ℝ) (n : ℤ) (p : GroupParams) (u : Leaf) :
    psiParams t n (leafShift p u) =
      leafShift (psiParams t n p) (leafScaling t n u) := by
  simp [leafShift,psiParams,splitCoordinates,leafScaling,mul_add]

def expandedChart (c : Chart) (t : ℝ) : ℕ → Chart
  | 0 => c
  | n+1 => translateChart (expandedChart c t n) t 1

theorem expanded_quotient (c : Chart) (t : ℝ) (n : ℕ) (p : GroupParams) :
    quotientCoordinates (expandedChart c t n).base ((psiParams t 1)^[n] p) =
      (psi t 1)^n • quotientCoordinates c.base p := by
  induction n with
  | zero => simp [expandedChart]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change quotientCoordinates (psi t 1*(expandedChart c t n).base)
      (psiParams t 1 ((psiParams t 1)^[n] p)) = _
    rw [quotient_diagonal_params,ih,← mul_smul,← pow_succ']

theorem expanded_shift_mem (c : Chart) (t : ℝ) (n : ℕ) (p : GroupParams) (u : Leaf)
    (hu : leafShift p u ∈ c.domain) :
    leafShift ((psiParams t 1)^[n] p) ((expand t)^[n] u) ∈ (expandedChart c t n).domain := by
  induction n with
  | zero => exact hu
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    refine ⟨leafShift ((psiParams t 1)^[n] p) ((expand t)^[n] u),ih,?_⟩
    exact psiParams_leafShift t 1 _ _

/-- Pulling a safe chart forward grows its entire centered plaque radius at
least as fast as 4^n, using the actual real/2-adic expansion estimate. -/
theorem expanded_contains_ball (c : Chart) {t : ℝ} (ht : Real.log 2 ≤ t)
    (n : ℕ) (p : GroupParams) {r : ℝ}
    (hp : ∀ u : Leaf, ‖u‖ ≤ r → leafShift p u ∈ c.domain) :
    ∀ u : Leaf, ‖u‖ ≤ (4 : ℝ)^n*r →
      leafShift ((psiParams t 1)^[n] p) u ∈ (expandedChart c t n).domain := by
  intro u hu
  have hsurj : Function.Surjective (expand t) := (leafScaling t 1).surjective
  obtain ⟨v,hv⟩ := hsurj.iterate n u
  have hnorm : (4 : ℝ)^n*‖v‖ ≤ (4 : ℝ)^n*r :=
    (expand_iterate_norm_lower ht v n).trans (hv ▸ hu)
  have hvnorm : ‖v‖ ≤ r := (mul_le_mul_left (by positivity : (0 : ℝ) < 4^n)).mp hnorm
  rw [← hv]
  exact expanded_shift_mem c t n p v (hp v hvnorm)

/-- Every inverse-trapped point has actual injective Gauss plaques of
arbitrarily large prescribed exponential radii. -/
theorem compact_expanding_plaques {K : Set X} (hK : IsCompact K)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : X,
      (∀ n : ℕ, ((psi t 1)⁻¹)^n • q ∈ K) →
      ∀ n : ℕ, ∃ c : Chart, ∃ p : GroupParams,
        quotientCoordinates c.base p = q ∧
        ∀ u : Leaf, ‖u‖ ≤ (4 : ℝ)^n*r → leafShift p u ∈ c.domain := by
  obtain ⟨C,ε,hε,hC⟩ := compact_uniform_safe_plaques hK
  refine ⟨ε/2,half_pos hε,?_⟩
  intro q hq n
  obtain ⟨c,_,p,hp,hplaque⟩ := hC _ (hq n)
  refine ⟨expandedChart c t n,(psiParams t 1)^[n] p,?_,?_⟩
  · rw [expanded_quotient,hp,← mul_smul,inv_pow,mul_inv_cancel,one_smul]
  · apply expanded_contains_ball c ht n p
    intro u hu
    exact hplaque u (by linarith)

end VV.BBEKExpandedPlaques

