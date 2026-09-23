import VV.BBEKLeafwiseSupport
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-! Zero mass at the sampled point is a genuine nonatomicity criterion
for the actual disintegration.  This is different from non-Diracness. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory

namespace VV.BBEKKernelAtoms
open BBEKDynamics BBEKLeafwiseKernel
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem noAtoms_of_ae_singleton_zero {U : Type*} [MeasurableSpace U]
    (ν : Measure U) (h : ∀ᵐ u ∂ν, ν {u} = 0) : NoAtoms ν := by
  constructor
  intro u
  by_contra hu
  have hs : {u} ⊆ {v | ¬ ν {v} = 0} := by
    intro v hv
    simpa only [mem_singleton_iff.mp hv] using hu
  exact hu (measure_mono_null hs (ae_iff.mp h))

theorem condKernel_noAtoms_of_ae_singleton_zero
    {B U : Type*} [MeasurableSpace B] [MeasurableSpace U]
    [StandardBorelSpace U] [Nonempty U]
    (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    (h : ∀ᵐ p ∂ρ, ρ.condKernel p.1 {p.2} = 0) :
    ∀ᵐ b ∂ρ.fst, NoAtoms (ρ.condKernel b) := by
  have hh : ∀ᵐ p ∂ρ.fst ⊗ₘ ρ.condKernel, ρ.condKernel p.1 {p.2} = 0 := by
    simpa only [Measure.disintegrate] using h
  exact (Measure.ae_ae_of_ae_compProd hh).mono
    (fun b hb => noAtoms_of_ae_singleton_zero (ρ.condKernel b) hb)

theorem centeredLeafKernel_singleton_zero {B : Type*} [MeasurableSpace B]
    (κ : Kernel B Leaf) [IsSFiniteKernel κ] (p : B × Leaf) :
    centeredLeafKernel κ p {0} = κ p.1 {p.2} := by
  rw [centeredLeafKernel_apply,
    Measure.map_apply (show Measurable (fun v : Leaf => v-p.2) from
      measurable_id.sub measurable_const) (measurableSet_singleton 0)]
  congr 1
  ext v
  simp only [mem_preimage,mem_singleton_iff,sub_eq_zero]

theorem condKernel_noAtoms_of_centered_zero {B : Type*} [MeasurableSpace B]
    (ρ : Measure (B × Leaf)) [IsFiniteMeasure ρ]
    (h : ∀ᵐ p ∂ρ, centeredLeafKernel ρ.condKernel p {0} = 0) :
    ∀ᵐ b ∂ρ.fst, NoAtoms (ρ.condKernel b) := by
  apply condKernel_noAtoms_of_ae_singleton_zero ρ
  simpa only [centeredLeafKernel_singleton_zero] using h

end VV.BBEKKernelAtoms
