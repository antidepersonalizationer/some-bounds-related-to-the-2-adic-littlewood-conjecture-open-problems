/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import VV.Entropy.CondPartition

/-!
# Monotonicity of conditional entropy under refinement of the σ-algebra

This file adds the **monotonicity of conditional entropy** to the conditional-entropy milestone
(GitHub issue #13), continuing `ErgodicTheory.Entropy.CondPartition`
(which defines `condEntropy μ 𝒜 s`
as the `μ`-average of the pointwise entropy against the regular conditional probability
`condExpKernel μ 𝒜 ω`).

The single result is the conditional generalization of `condEntropy_le` ("conditioning does not
increase entropy"): conditioning on a **finer** sub-σ-algebra reduces conditional entropy.

* `condEntropy_mono_of_le`: if `𝒜 ≤ ℬ ≤ mα` then `H(P | ℬ) ≤ H(P | 𝒜)`.

The proof runs the same Jensen argument as `condEntropy_le`, but with the *conditional* Jensen
inequality (`ConcaveOn.condExp_map_le`) against the coarser σ-algebra `𝒜` in place of the
unconditional one, combined with the **tower property** of conditional expectation
(`condExp_condExp_of_le`). Term by term over the cells `Pᵢ`, writing
`f_i ω = (condExpKernel μ ℬ ω Pᵢ).toReal` and `g_i ω = (condExpKernel μ 𝒜 ω Pᵢ).toReal`:

* the kernel-to-condExp links (`condExpKernel_ae_eq_condExp`) give `f_i =ᵐ μ⟦Pᵢ | ℬ⟧` and
  `g_i =ᵐ μ⟦Pᵢ | 𝒜⟧`, and the tower property gives `μ⟦f_i | 𝒜⟧ =ᵐ g_i`;
* conditional Jensen for the concave `negMulLog` gives
  `μ⟦negMulLog ∘ f_i | 𝒜⟧ ≤ᵐ negMulLog ∘ μ⟦f_i | 𝒜⟧ =ᵐ negMulLog ∘ g_i`;
* integrating and using `integral_condExp` (the `μ`-average of a conditional expectation is the
  `μ`-average of the function) turns the left side back into `∫ negMulLog ∘ f_i ∂μ`, giving
  `∫ negMulLog ∘ f_i ∂μ ≤ ∫ negMulLog ∘ g_i ∂μ`.

Summing over the finite partition yields the claim.

## Main results

* `ErgodicTheory.Entropy.condEntropy_mono_of_le`: conditioning on a finer σ-algebra reduces
  conditional entropy.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Peter Walters, *An Introduction to Ergodic Theory*, Springer GTM 79, Chapter 4.
-/

open MeasureTheory Function Filter ProbabilityTheory Set
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {α : Type*} {ι : Type*} {𝒜 ℬ : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

/-- **Monotonicity of conditional entropy under refinement.** Conditioning on the finer
sub-σ-algebra `ℬ ⊇ 𝒜` produces the smaller conditional entropy: for any finite measurable partition
`P` of the probability space and any sub-σ-algebras `𝒜 ≤ ℬ ≤ mα`,
`H(P | ℬ) ≤ H(P | 𝒜)`.

This is the conditional generalization of `condEntropy_le` (which is the case `𝒜 = ⊥`). The proof
applies the conditional Jensen inequality (`ConcaveOn.condExp_map_le`) for the concave `negMulLog`
against `𝒜`, term by term over the cells `Pᵢ`. Writing `f_i ω = (condExpKernel μ ℬ ω Pᵢ).toReal`,
the tower property `condExp_condExp_of_le` identifies the inner `𝒜`-conditional expectation
`μ⟦f_i | 𝒜⟧` with the coarser kernel mass `(condExpKernel μ 𝒜 ω Pᵢ).toReal`; integrating the
resulting pointwise Jensen bound and using `integral_condExp` gives the termwise inequality, which
sums to the claim. -/
lemma condEntropy_mono_of_le [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜ℬ : 𝒜 ≤ ℬ) (hℬ : ℬ ≤ mα) (P : MeasurePartition μ ι) :
    condEntropy μ ℬ P.cells ≤ condEntropy μ 𝒜 P.cells := by
  have h𝒜 : 𝒜 ≤ mα := h𝒜ℬ.trans hℬ
  haveI : SigmaFinite (μ.trim h𝒜) := inferInstance
  haveI : SigmaFinite (μ.trim hℬ) := inferInstance
  rw [condEntropy_def, condEntropy_def]
  -- Move both integrals inside the finite sum.
  rw [integral_finset_sum _
      (fun i _ => integrable_negMulLog_condExpKernel hℬ (P.measurable i)),
    integral_finset_sum _
      (fun i _ => integrable_negMulLog_condExpKernel h𝒜 (P.measurable i))]
  refine Finset.sum_le_sum fun i _ => ?_
  -- Abbreviations for the two kernel-mass functions of the cell `Pᵢ`.
  set fℬ : α → ℝ := fun ω => (@condExpKernel α mα _ μ _ ℬ ω (P.cells i)).toReal with hfℬ
  set f𝒜 : α → ℝ := fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal with hf𝒜
  -- Integrability of the relevant functions.
  have hint_fℬ : Integrable fℬ μ := integrable_toReal_condExpKernel (P.measurable i)
  have hint_gℬ : Integrable (Real.negMulLog ∘ fℬ) μ :=
    integrable_negMulLog_condExpKernel hℬ (P.measurable i)
  -- The two kernel masses are a.e. the corresponding conditional expectations.
  have hae_ℬ : fℬ =ᵐ[μ] μ⟦P.cells i | ℬ⟧ := by
    simpa only [hfℬ, measureReal_def] using condExpKernel_ae_eq_condExp hℬ (P.measurable i)
  have hae_𝒜 : f𝒜 =ᵐ[μ] μ⟦P.cells i | 𝒜⟧ := by
    simpa only [hf𝒜, measureReal_def] using condExpKernel_ae_eq_condExp h𝒜 (P.measurable i)
  -- Tower property: `μ[fℬ | 𝒜] =ᵐ f𝒜`.
  have htower : μ[fℬ | 𝒜] =ᵐ[μ] f𝒜 := by
    calc μ[fℬ | 𝒜] =ᵐ[μ] μ[μ⟦P.cells i | ℬ⟧ | 𝒜] := condExp_congr_ae hae_ℬ
      _ =ᵐ[μ] μ⟦P.cells i | 𝒜⟧ := condExp_condExp_of_le h𝒜ℬ hℬ
      _ =ᵐ[μ] f𝒜 := hae_𝒜.symm
  -- Conditional Jensen for the concave `negMulLog` over `Set.Ici 0`, against `𝒜`.
  have hmem : ∀ᵐ ω ∂μ, fℬ ω ∈ Set.Ici (0 : ℝ) :=
    Eventually.of_forall fun ω => Set.mem_Ici.mpr ENNReal.toReal_nonneg
  have hjensen : μ[Real.negMulLog ∘ fℬ | 𝒜] ≤ᵐ[μ] Real.negMulLog ∘ μ[fℬ | 𝒜] := by
    have hfint := hint_fℬ.condExpKernel_ae (m := 𝒜)
    have hgint := hint_gℬ.condExpKernel_ae (m := 𝒜)
    have hfcond := condExp_ae_eq_integral_condExpKernel h𝒜 hint_fℬ
    have hgcond := condExp_ae_eq_integral_condExpKernel h𝒜 hint_gℬ
    filter_upwards [hfint,hgint,hfcond,hgcond] with ω hfω hgω heqf heqg
    simp only [Function.comp_apply,heqf,heqg]
    exact Real.concaveOn_negMulLog.le_map_integral
      Real.continuous_negMulLog.continuousOn isClosed_Ici
      (Eventually.of_forall fun y => (show 0 ≤ fℬ y from ENNReal.toReal_nonneg)) hfω hgω
  -- Rewrite the right-hand bound via the tower identity.
  have hjensen' : μ[Real.negMulLog ∘ fℬ | 𝒜] ≤ᵐ[μ] Real.negMulLog ∘ f𝒜 := by
    filter_upwards [hjensen, htower] with ω hω htw
    simpa only [Function.comp_apply, htw] using hω
  -- Integrate the a.e. inequality; the left side recovers `∫ negMulLog ∘ fℬ ∂μ`.
  calc ∫ ω, Real.negMulLog (fℬ ω) ∂μ
      = ∫ ω, (μ[Real.negMulLog ∘ fℬ | 𝒜]) ω ∂μ := (integral_condExp h𝒜).symm
    _ ≤ ∫ ω, Real.negMulLog (f𝒜 ω) ∂μ :=
        integral_mono_ae integrable_condExp
          (integrable_negMulLog_condExpKernel h𝒜 (P.measurable i)) hjensen'

end ErgodicTheory.Entropy
