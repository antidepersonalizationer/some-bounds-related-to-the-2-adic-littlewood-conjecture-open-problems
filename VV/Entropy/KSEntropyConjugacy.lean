/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import VV.Entropy.FactorEntropy

/-!
# Measurable-conjugacy invariance of the Kolmogorov–Sinai entropy of a system

Two measure-preserving systems `(α, T, μ)` and `(β, S, ν)` that are **measurably conjugate** — i.e.
there is a measurable isomorphism `e : α ≃ᵐ β` that is measure-preserving (`e_* μ = ν`) and
intertwines the dynamics (`e ∘ T = S ∘ e`) — have equal Kolmogorov–Sinai entropies:

`h(T) = h(S)`  (`ErgodicTheory.Entropy.ksEntropy_congr_of_conjugacy`).

This is the entropy-side companion of index-reindexing invariance (which only permutes the index
type of a single partition): here the whole *space* is transported.

## Proof

`e` is a factor map from `(α, T, μ)` onto `(β, S, ν)` and `e.symm` is a factor map the other way.
For a factor map the partition-relative entropies of a pulled-back partition agree with those of the
original (`factor_relative_eq`). Hence:

* every partition `R` of `β` pulls back through `e` to a partition `e⁻¹R` of `α` with
  `h(e⁻¹R, T) = h(R, S)`, so `h(R, S) ≤ h(T)` and therefore `h(S) ≤ h(T)`;
* symmetrically, pulling back through `e.symm` gives `h(T) ≤ h(S)`.

Both pullbacks preserve the index type, so the pulled-back partitions land directly in the
`Fin n`-indexed family realising `ksEntropy`; no reindexing is needed. `le_antisymm` finishes.

## Main results

* `ErgodicTheory.Entropy.ksEntropy_congr_of_conjugacy`: measurable conjugacy ⇒ equal KS entropy.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Ch. 4.
-/

open MeasureTheory Function

namespace ErgodicTheory.Entropy

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {T : α → α} {S : β → β}

/-- **Measurable-conjugacy invariance of the Kolmogorov–Sinai entropy of a system.** If a measurable
isomorphism `e : α ≃ᵐ β` is measure-preserving and intertwines the two dynamics (`e ∘ T = S ∘ e`),
then the systems `(α, T, μ)` and `(β, S, ν)` have equal Kolmogorov–Sinai entropies `h(T) = h(S)`.

Both `e` and its inverse `e.symm` are factor maps, so the factor-relative entropy invariance
`factor_relative_eq` transports partition entropies in either direction; pulling partitions back
through `e.symm` gives `h(T) ≤ h(S)` and through `e` gives `h(S) ≤ h(T)`. -/
theorem ksEntropy_congr_of_conjugacy (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (hconj : e ∘ T = S ∘ e) :
    ksEntropy hT = ksEntropy hS := by
  -- The inverse `e.symm` is measure-preserving and intertwines `S` with `T`.
  have he' : MeasurePreserving (⇑e.symm) ν μ := MeasurePreserving.symm e he
  have hconj' : ⇑e.symm ∘ S = T ∘ ⇑e.symm := by
    funext y
    simp only [Function.comp_apply]
    apply e.injective
    rw [e.apply_symm_apply]
    have h := congrFun hconj (e.symm y)
    simp only [Function.comp_apply, e.apply_symm_apply] at h
    rw [h]
  refine le_antisymm ?_ ?_
  · -- `h(T) ≤ h(S)`: pull each partition `P` of `α` back through `e.symm`.
    refine iSup_le fun n => iSup_le fun P => ?_
    rw [← factor_relative_eq hS hT he' hconj' P]
    exact le_ksEntropy hS (P.pulledBack he')
  · -- `h(S) ≤ h(T)`: pull each partition `R` of `β` back through `e`.
    refine iSup_le fun n => iSup_le fun R => ?_
    rw [← factor_relative_eq hT hS he hconj R]
    exact le_ksEntropy hT (R.pulledBack he)

end ErgodicTheory.Entropy

