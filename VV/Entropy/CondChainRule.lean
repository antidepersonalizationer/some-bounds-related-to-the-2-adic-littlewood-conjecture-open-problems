/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import VV.Entropy.FiniteConditionalEntropy
import VV.Entropy.CondPartition
import VV.Entropy.CondPullback

/-!
# The conditional chain rule (analytic heart of Abramov–Rokhlin, issue #13)

This module proves the entropy chain rule `H(P ∨ Q) = H(P) + H(Q | P)`, the EQUALITY refining
`entropy_join_le`, both in its absolute form and in the kernel-level conditional form
`H(P ∨ Q | 𝒜) = H(P | 𝒜) + H(Q | 𝒜 ⊔ σ(P))`.
-/

open MeasureTheory Function Filter ProbabilityTheory Finset
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]

/-! ## Step 3: the kernel-level (general `𝒜`) conditional chain rule.

The absolute identity, applied *pointwise* against the Markov kernel `condExpKernel μ 𝒜 ω`
(which is a.e. a probability measure for which `P`, `Q` are still partitions) and integrated
over `μ`. This is the EQUALITY refining `condEntropy_join_le`. The refined-conditioning term
`H(Q | 𝒜 ⊔ σ(P))` is expressed in the additive-over-cells form, *avoiding* the refined kernel
`condExpKernel μ (𝒜 ⊔ σ(P))` entirely. -/

section Conditional

variable [StandardBorelSpace α]

-- NOTE: the variable ORDER `{𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]` (top of file,
-- mirroring `CondPullback`) is load-bearing: `mα` is declared AFTER `𝒜`, so it has higher
-- instance priority and `Measure α` / `StandardBorelSpace α` resolve to the ambient `mα`, not
-- the sub-σ-algebra `𝒜`.

/-- **Conditional version of `condEntropyGivenPartition`**, evaluated against the regular
conditional probability `condExpKernel μ 𝒜 ω` and averaged over `μ`. This is `H(Q | 𝒜 ⊔ σ(P))`
written in the additive-over-cells form, i.e. the second summand of the conditional chain rule.

Uses the ambient `mα` for the kernel (exactly as `condEntropy`/`condEntropy_join_le`); the
sub-σ-algebra `𝒜` is a plain explicit argument, never an instance. -/
noncomputable def condEntropyGivenPartitionCond [Fintype ι] [Fintype κ]
    (μ : Measure α) [IsFiniteMeasure μ] (𝒜 : MeasurableSpace α) (s : ι → Set α)
    (t : κ → Set α) : ℝ :=
  ∫ ω, @condEntropyGivenPartition α ι κ mα _ _ (@condExpKernel α mα _ μ _ 𝒜 ω) s t ∂μ

/-- **The conditional chain rule (kernel-level form).**
`H(P ∨ Q | 𝒜) = H(P | 𝒜) + H(Q | 𝒜 ⊔ σ(P))`, with the last term in additive-over-cells form
`∫ ω, ∑ᵢ κ(ω)(Pᵢ) · H_{κ(ω)|Pᵢ}(Q) ∂μ`. The EQUALITY refining `condEntropy_join_le`. -/
theorem condEntropy_join_eq [Fintype ι] [Fintype κ]
    {μ : Measure α} [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    condEntropy μ 𝒜 (joinCells P.cells Q.cells)
      = condEntropy μ 𝒜 P.cells + condEntropyGivenPartitionCond μ 𝒜 P.cells Q.cells := by
  -- Abbreviation for the conditional kernel measure at `ω`.
  set κω : α → Measure α := fun ω => @condExpKernel α mα _ μ _ 𝒜 ω with hκω
  -- The pointwise absolute chain rule: for a.e. `ω`, `κ ω` is a probability measure with `P`, `Q`
  -- genuine partitions, so the absolute equality holds against `κ ω`.
  have hpt : ∀ᵐ ω ∂μ,
      entropy (κω ω) (joinCells P.cells Q.cells)
        = entropy (κω ω) P.cells + condEntropyGivenPartition (κω ω) P.cells Q.cells := by
    filter_upwards [condExpKernel_pairwise_aedisjoint h𝒜 P,
      condExpKernel_pairwise_aedisjoint h𝒜 Q] with ω hPd hQd
    have : IsProbabilityMeasure (κω ω) := IsMarkovKernel.isProbabilityMeasure ω
    let Pω : MeasurePartition (κω ω) ι :=
      { cells := P.cells, measurable := P.measurable, aedisjoint := hPd, cover := P.cover }
    let Qω : MeasurePartition (κω ω) κ :=
      { cells := Q.cells, measurable := Q.measurable, aedisjoint := hQd, cover := Q.cover }
    exact entropy_join_eq_add_condEntropyGivenPartition Pω Qω
  -- Integrability of the per-cell conditional-entropy term: a.e. it is the difference of the two
  -- (integrable) `condEntropy` integrands.
  have hdiff : (fun ω => condEntropyGivenPartition (κω ω) P.cells Q.cells)
      =ᵐ[μ] fun ω =>
        entropy (κω ω) (joinCells P.cells Q.cells) - entropy (κω ω) P.cells := by
    filter_upwards [hpt] with ω hω; rw [hω]; ring
  have hintJ : Integrable (fun ω => entropy (κω ω) (joinCells P.cells Q.cells)) μ := by
    simp only [hκω, entropy_def]
    exact integrable_condEntropy_integrand h𝒜 (joinCells P.cells Q.cells)
      (fun x => (P.measurable x.1).inter (Q.measurable x.2))
  have hintP : Integrable (fun ω => entropy (κω ω) P.cells) μ := by
    simp only [hκω, entropy_def]
    exact integrable_condEntropy_integrand h𝒜 P.cells (fun i => P.measurable i)
  have hintC : Integrable (fun ω => condEntropyGivenPartition (κω ω) P.cells Q.cells) μ :=
    (hintJ.sub hintP).congr hdiff.symm
  -- Now assemble. Rewrite the three quantities as integrals of pointwise `entropy` /
  -- `condEntropyGivenPartition`, combine the two RHS integrals, and integrate the a.e. equality.
  have eJ : condEntropy μ 𝒜 (joinCells P.cells Q.cells)
      = ∫ ω, entropy (κω ω) (joinCells P.cells Q.cells) ∂μ := by
    rw [condEntropy_def]
    simp only [hκω, entropy_def]
  have eP : condEntropy μ 𝒜 P.cells = ∫ ω, entropy (κω ω) P.cells ∂μ := by
    rw [condEntropy_def]
    simp only [hκω, entropy_def]
  have eC : condEntropyGivenPartitionCond μ 𝒜 P.cells Q.cells
      = ∫ ω, condEntropyGivenPartition (κω ω) P.cells Q.cells ∂μ := by
    rw [condEntropyGivenPartitionCond]
  rw [eJ, eP, eC, ← integral_add hintP hintC]
  exact integral_congr_ae hpt

end Conditional

end ErgodicTheory.Entropy
