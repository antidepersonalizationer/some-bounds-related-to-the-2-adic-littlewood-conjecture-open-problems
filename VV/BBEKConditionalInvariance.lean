import VV.BBEKLeafwiseKernel
import VV.BBEKLeafwiseStabilizer

/-!
# Invariance reconstructed from conditional measures

This file supplies the measure-theoretic step used after the leafwise argument.  If almost every
conditional measure in a genuine disintegration is invariant under a fixed translation in the
leaf coordinate, then the disintegrated measure itself is invariant under the corresponding
fiber translation.  No leafwise-measure existence or rigidity assertion is assumed here.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory

namespace VV.BBEKConditionalInvariance

open BBEKLeafwiseStabilizer

variable {B U : Type*} [MeasurableSpace B]
  [AddCommGroup U] [MeasurableSpace U] [MeasurableAdd₂ U]

/-- Translation in the second coordinate of a product. -/
def fiberTranslate (u : U) : B × U → B × U := fun p => (p.1, u + p.2)

theorem measurable_fiberTranslate (u : U) : Measurable (fiberTranslate (B := B) u) :=
  measurable_fst.prodMk (measurable_const.add measurable_snd)

/-- Reconstruct invariance of a composition product from invariance of almost every conditional
measure.  This is the product-coordinate form of the standard implication “leafwise invariance
implies ambient invariance”. -/
theorem map_compProd_fiberTranslate_eq_self
    (ν : Measure B) [SFinite ν] (κ : Kernel B U) [IsSFiniteKernel κ] (u : U)
    (hinv : ∀ᵐ b ∂ν, Measure.map (u + ·) (κ b) = κ b) :
    Measure.map (fiberTranslate (B := B) u) (ν ⊗ₘ κ) = ν ⊗ₘ κ := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_fiberTranslate u) hs,
    Measure.compProd_apply (hs.preimage (measurable_fiberTranslate u)),
    Measure.compProd_apply hs]
  apply lintegral_congr_ae
  filter_upwards [hinv] with b hb
  have hleaf : Measurable (fun v : U => u + v) := measurable_const.add measurable_id
  have hsection : MeasurableSet (Prod.mk b ⁻¹' s) := measurable_prodMk_left hs
  calc
    κ b (Prod.mk b ⁻¹' (fiberTranslate (B := B) u ⁻¹' s)) =
        κ b ((fun v : U => u + v) ⁻¹' (Prod.mk b ⁻¹' s)) := by rfl
    _ = Measure.map (u + ·) (κ b) (Prod.mk b ⁻¹' s) :=
      (Measure.map_apply hleaf hsection).symm
    _ = κ b (Prod.mk b ⁻¹' s) := by rw [hb]

/-- The same statement with the canonical conditional kernel of a finite measure. -/
theorem map_fiberTranslate_eq_self_of_condKernel
    [StandardBorelSpace U] [Nonempty U]
    (ρ : Measure (B × U)) [IsFiniteMeasure ρ] (u : U)
    (hinv : ∀ᵐ b ∂ρ.fst, Measure.map (u + ·) (ρ.condKernel b) = ρ.condKernel b) :
    Measure.map (fiberTranslate (B := B) u) ρ = ρ := by
  rw [← ρ.disintegrate ρ.condKernel]
  exact map_compProd_fiberTranslate_eq_self ρ.fst ρ.condKernel u hinv

/-- Subgroup-valued version: if almost every conditional measure is invariant under every
element of `H`, the composition product is invariant under every corresponding fiber
translation. -/
theorem map_compProd_fiberTranslate_eq_self_of_subgroup
    (ν : Measure B) [SFinite ν] (κ : Kernel B U) [IsSFiniteKernel κ]
    (H : AddSubgroup U)
    (hinv : ∀ u : H, ∀ᵐ b ∂ν, Measure.map ((u : U) + ·) (κ b) = κ b) (u : H) :
    Measure.map (fiberTranslate (B := B) (u : U)) (ν ⊗ₘ κ) = ν ⊗ₘ κ :=
  map_compProd_fiberTranslate_eq_self ν κ (u : U) (hinv u)

/-- A full exact translation stabilizer on almost every leaf is the hypothesis needed by the
reconstruction lemma above. -/
theorem map_compProd_fiberTranslate_eq_self_of_stabilizer_top
    [TopologicalSpace U] [IsTopologicalAddGroup U] [BorelSpace U]
    [SecondCountableTopology U]
    (ν : Measure B) [SFinite ν] (κ : Kernel B U) [IsSFiniteKernel κ]
    (htop : ∀ᵐ b ∂ν, translationStabilizer (κ b) = ⊤) (u : U) :
    Measure.map (fiberTranslate (B := B) u) (ν ⊗ₘ κ) = ν ⊗ₘ κ := by
  apply map_compProd_fiberTranslate_eq_self ν κ u
  filter_upwards [htop] with b hb
  have hu : u ∈ translationStabilizer (κ b) := by rw [hb]; trivial
  exact hu

/-- Canonical-disintegration version of
`map_compProd_fiberTranslate_eq_self_of_stabilizer_top`. -/
theorem map_fiberTranslate_eq_self_of_condKernel_stabilizer_top
    [TopologicalSpace U] [IsTopologicalAddGroup U] [BorelSpace U]
    [SecondCountableTopology U] [StandardBorelSpace U] [Nonempty U]
    (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    (htop : ∀ᵐ b ∂ρ.fst, translationStabilizer (ρ.condKernel b) = ⊤) (u : U) :
    Measure.map (fiberTranslate (B := B) u) ρ = ρ := by
  rw [← ρ.disintegrate ρ.condKernel]
  exact map_compProd_fiberTranslate_eq_self_of_stabilizer_top
    ρ.fst ρ.condKernel htop u

/-- Push an invariant coordinate measure through a measurable semiconjugacy. -/
theorem map_map_eq_self_of_semiconj
    {Y : Type*} [MeasurableSpace Y] (ρ : Measure (B × U))
    (F : B × U → Y) (hF : Measurable F) (S : Y → Y) (hS : Measurable S)
    (u : U) (hsemi : S ∘ F = F ∘ fiberTranslate (B := B) u)
    (hinv : Measure.map (fiberTranslate (B := B) u) ρ = ρ) :
    Measure.map S (Measure.map F ρ) = Measure.map F ρ := by
  rw [Measure.map_map hS hF, hsemi, ← Measure.map_map hF (measurable_fiberTranslate u), hinv]

end VV.BBEKConditionalInvariance
