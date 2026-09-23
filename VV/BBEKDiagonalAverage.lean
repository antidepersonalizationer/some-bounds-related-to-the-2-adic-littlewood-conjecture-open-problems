import VV.BBEKDiagonal
import VV.BBEKMeasureAverage
import VV.BBEKDiscrete

/-! Compact averaging on the actual split diagonal group. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace VV.BBEKDiagonalAverage
open BBEKDynamics BBEKDiagonal BBEKMeasureAverage

abbrev H := Multiplicative (ℝ × ℤ)
local instance : MeasurableSpace G := borel G
local instance : BorelSpace G := ⟨rfl⟩
local instance : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩
local instance : MeasurableSpace H := borel H
local instance : BorelSpace H := ⟨rfl⟩

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [MulAction G Y] [ContinuousSMul G Y] [SecondCountableTopology Y]

instance psiAction : MulAction H Y := MulAction.compHom Y psiHom

instance psiContinuousSMul : ContinuousSMul H Y :=
  MulAction.continuousSMul_compHom continuous_psiHom

instance psiCommutesCompact : SMulCommClass H K Y where
  smul_comm h k y := by
    change psiHom h • ((k:G) • y) = (k:G) • (psiHom h • y)
    rw [← mul_smul,← mul_smul]
    exact congrArg (fun g : G => g • y) (psi_commute_K h.toAdd.1 h.toAdd.2 k).eq

def averaged (μ : Measure Y) : Measure Y := average (haarProbability (K:=K)) μ

instance averaged_probability (μ : Measure Y) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (averaged μ) := inferInstanceAs (IsProbabilityMeasure (average _ μ))

instance averaged_compact_invariant (μ : Measure Y) [IsProbabilityMeasure μ] :
    SMulInvariantMeasure K Y (averaged μ) :=
  inferInstanceAs (SMulInvariantMeasure K Y (average _ μ))

instance averaged_psi_invariant (μ : Measure Y) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure H Y μ] : SMulInvariantMeasure H Y (averaged μ) :=
  commuting_smulInvariantMeasure _ μ

theorem averaged_diagonal_invariant (μ : Measure Y) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure H Y μ] : SMulInvariantMeasure A Y (averaged μ) := by
  constructor
  intro a s hs
  obtain ⟨t,n,k,he⟩ := diagonal_decomposition a.property
  have hf : (fun y : Y => a • y) =
      (fun y => (Multiplicative.ofAdd (t,n) : H) • y) ∘ (fun y => k • y) := by
    funext y
    change (a:G) • y = psi t n • ((k:G) • y)
    rw [he,mul_smul]
  rw [hf,Set.preimage_comp,measure_preimage_smul,measure_preimage_smul]

theorem averaged_diagonal_ergodic [R1Space Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] [μ.InnerRegular] [ErgodicSMul H Y μ] :
    ErgodicSMul A Y (averaged μ) := by
  letI := averaged_diagonal_invariant μ
  constructor
  intro s hs hi
  apply joint_aeconst_continuous (H:=H) (haarProbability (K:=K)) μ hs
  · intro h
    exact hi ⟨psiHom h,psi_mem_A _ _⟩
  · intro k
    exact hi ⟨k,K_le_A k.property⟩

end VV.BBEKDiagonalAverage
