import VV.BBEKMautner
import VV.BBEKDiscrete
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.Dynamics.Ergodic.Action.Basic

/-! Mautner's argument on the actual Koopman representation on L².
The group is the literal BBEK group, and ergodicity is mathlib's ordinary
measure-theoretic ergodicity. Domain action is contravariant, so inversion
is used explicitly to obtain the continuous left action. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace VV.BBEKMautnerLp
open BBEKDynamics BBEKMautner

local instance : MeasurableSpace G := borel G
local instance : BorelSpace G := ⟨rfl⟩
local instance : Fact ((1:ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

/-- Inversion converts the right domain action into the left Koopman action. -/
def inverseDom : G →* Gᵈᵐᵃ where
  toFun g := DomMulAct.mk g⁻¹
  map_one' := by simp
  map_mul' g h := by simp

theorem continuous_inverseDom : Continuous inverseDom :=
  DomMulAct.continuous_mk.comp continuous_inv

variable {X : Type*} [TopologicalSpace X] [R1Space X]
  [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X]
  {μ : Measure X} [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [SMulInvariantMeasure G X μ]

/-- A vector fixed by the diagonal Koopman operator is fixed by every
operator of the actual group. No fixed-vector bridge is assumed. -/
theorem all_dom_fixed_of_psi_fixed {E : Type*} [NormedAddCommGroup E]
    {t : ℝ} (ht : 0 < t) {w : Lp E 2 μ}
    (hw : DomMulAct.mk (psi t 1) • w = w) (g : G) :
    DomMulAct.mk g • w = w := by
  letI : MulAction G (Lp E 2 μ) := MulAction.compHom _ inverseDom
  letI : ContinuousSMul G (Lp E 2 μ) :=
    MulAction.continuousSMul_compHom continuous_inverseDom
  have hiso (a : G) : Isometry (fun f : Lp E 2 μ => a • f) := by
    apply Isometry.of_dist_eq
    intro f h
    exact DomMulAct.dist_smul_Lp (inverseDom a) f h
  have hi : (DomMulAct.mk (psi t 1))⁻¹ • w = w :=
    (MulAction.stabilizer Gᵈᵐᵃ w).inv_mem hw
  have hf : psi t 1 • w = w := hi
  have h := group_fixed_of_psi_fixed hiso ht hf g⁻¹
  change DomMulAct.mk (g⁻¹)⁻¹ • w = w at h
  simpa only [inv_inv] using h

/-- Invariance of a measurable set under the single diagonal element
forces almost-everywhere invariance under each group element. -/
theorem preimage_ae_eq_of_psi_invariant {t : ℝ} (ht : 0 < t)
    {s : Set X} (hs : MeasurableSet s)
    (hinv : (psi t 1 • ·) ⁻¹' s =ᵐ[μ] s) (g : G) :
    (g • ·) ⁻¹' s =ᵐ[μ] s := by
  let w : Lp ℝ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) 1
  have hpsi : DomMulAct.mk (psi t 1) • w = w := by
    dsimp only [w]
    rw [DomMulAct.mk_smul_indicatorConstLp]
    exact (indicatorConstLp_inj _ _ _ _ (by norm_num : (1:ℝ) ≠ 0)).mpr hinv
  have hg := all_dom_fixed_of_psi_fixed ht hpsi g
  dsimp only [w] at hg
  rw [DomMulAct.mk_smul_indicatorConstLp] at hg
  exact (indicatorConstLp_inj _ _ _ _ (by norm_num : (1:ℝ) ≠ 0)).mp hg

/-- On any finite Radon measure space with a continuous ergodic action
of the actual BBEK group, its strictly expanding diagonal map is ergodic.
The assumptions are ordinary measure/action regularity and full-group
ergodicity, not a spectral or fixed-vector hypothesis. -/
theorem psi_ergodic_of_group_ergodic [ErgodicSMul G X μ]
    {t : ℝ} (ht : 0 < t) : Ergodic (fun z : X => psi t 1 • z) μ := by
  refine ⟨measurePreserving_smul (psi t 1) μ, ?_⟩
  constructor
  intro s hs hinv
  apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (G:=G) hs
  intro g
  exact preimage_ae_eq_of_psi_invariant ht hs (Filter.EventuallyEq.of_eq hinv) g

section ArithmeticQuotient

local instance : MeasurableSpace BBEKQuotient.X := borel BBEKQuotient.X
local instance : BorelSpace BBEKQuotient.X := ⟨rfl⟩

/-- The Radon probability specialization on the actual arithmetic quotient.
Existence and full-group ergodicity of the measure are not asserted here. -/
theorem quotient_psi_ergodic (ν : Measure BBEKQuotient.X)
    [IsProbabilityMeasure ν] [ν.InnerRegular]
    [ErgodicSMul G BBEKQuotient.X ν] {t : ℝ} (ht : 0 < t) :
    Ergodic (fun z : BBEKQuotient.X => psi t 1 • z) ν :=
  psi_ergodic_of_group_ergodic ht

end ArithmeticQuotient

end VV.BBEKMautnerLp
