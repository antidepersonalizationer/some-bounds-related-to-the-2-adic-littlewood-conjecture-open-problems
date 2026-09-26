# Actual exceptional-branch backend and remaining EL interfaces — 2026-09-27

This note records a proved increment, not a completion of the EL theorem. The admitted body in `BBEKLowEntropyCore.rootAlternative_of_positive_entropy` was not changed.

## Proved increment and source correspondence

The source comparison is with [Einsiedler–Lindenstrauss, *On measures invariant under tori on quotients of semi-simple groups*, §§6–7](https://people.math.ethz.ch/~einsiedl/maxsplit.pdf), especially the local exceptional alternative in Corollary 6.2. The new arithmetic argument discharges the consequences of that local alternative in this particular quotient; it does not prove Theorem 6.1 or produce the alternatives of Corollary 6.2.

- `BBEKExceptionalFactorOrbit` proves that the actual pure-factor orbit maps in `SL₂(ℝ) × SL₂(ℚ₂) / SL₂(ℤ[1/2])` are measurable embeddings. A probability invariant under the indicated contracting diagonal cannot be carried by one such orbit, even if the orbit is not closed. `BBEKExceptionalCentralizer` identifies the common centralizer orbits of two opposite full roots with these factor orbits. `BBEKExceptionalOrbitNull` strengthens the result to zero mass for every orbit and every countable union of them.
- `BBEKInvariantConditionals` proves invariance of the literal `condDistrib id f μ` when `f` is invariant. `BBEKConditionalLeafFibres.condDistrib_id_leaf_pair_fibre` proves that the same actual conditionals over `(ηlo, ηup)` carry both fields unchanged. It uses fixed countable compact-support integral tests for infinite Radon measures, not an unsupported standard-Borel assertion about the space of all measures.
- `BBEKPairExceptional` applies these results to the actual opposite-root canonical fields. `BBEKLocalExceptional.real_local_exceptional_set_null` and its 2-adic counterpart show that any measurable set with the local same-pair-to-centralizer-orbit property has zero ambient mass. Second countability supplies the countable subcover. Neither compact support nor a general rational closed-orbit classification is used in this exceptional-branch argument.
- `BBEKRootFieldSeparation` gives one measurable conull set, independent of the translation parameter, on which an equal-field root translation is zero. `BBEKLowEntropyBackend` combines this with local exceptional-set nullity. Its compact-support existence statements supply actual canonical pairs and exclude an explicitly written disjunction; they do not assert that positive entropy produces that disjunction.
- `BBEKCanonicalCovariance` derives scaling covariance for a specified canonical family, without making a second existential choice. `BBEKUnifiedRootData` derives all its properties for this same family and original radius. Compact Mahler support is used to exclude nontrivial stabilizers. Non-Dirac leaves have infinite total mass, generate the full closed additive root subgroup, and have `NoAtoms`; this does not infer non-Diracness from entropy.

## Final read-only scope review after the actual sequence front end

1. **Entropy must reach the applicable opposite pair.** `BBEKUnifiedRootData.RootProperties` gives non-Dirac implies `NoAtoms`; `BBEKPairedShear` requires almost-everywhere `NoAtoms` for the field used in the shear. Positive KS entropy has not yet been connected to both actual opposite root fields in a suitable factor, with the necessary almost-everywhere or invariant-component quantifier. One non-Dirac root is not by itself sufficient for the current assembly: `real_noncentral_subsequence` and its 2-adic counterpart select lower **or** upper noncommutation. If all chosen matrices commute with the lower root, the construction must use the upper field. Entropy equality for an invertible map and its inverse exists in `Entropy/KSEntropyInverse.lean`, but the actual pure-factor root-entropy identification is still needed. A nonatomic joint lower conditional cannot be treated as nonatomic single-root conditionals without proving the relevant factorization or entropy statement.
2. **The point/matrix front end is now proved.** `BBEKNoncentralSequence.real_shearing_sequence_of_positive_set` and its 2-adic counterpart take the specified canonical opposite pair and any positive measurable set. They construct a base point and actual matrices tending to the identity, keep both fields equal along the displaced points, and select one fixed noncommuting root direction. `BBEKPureRootShear` identifies the pure-factor diagonal matrix computation with actual quotient displacements. These are no longer missing abstract compatibility assumptions.
3. **The remaining leaf-return estimate is substantive.** `BBEKPairedShear.exists_paired_shear_good_set_at_total_time` avoids any supplied root bad set having mass at most one half. The actual bad set must still be defined and proved to have this bound for both paired translated points, at the correct total-time leaf field and original normalization radius. The resulting points must lie in the same compact Lusin/conull set; literal equal-field transport under the chosen pure-factor time and common root translation then needs to be assembled. `BBEKLusinRootLimit` proves the terminal limiting implication when these actual return and test-equality hypotheses are supplied. It does not produce those hypotheses.
4. **Keep the exact measure and scope.** All canonical properties must apply to the same chosen fields and the backend's chosen conull set. Strong translation covariance is pointwise only within that set. Compact Mahler support is used to force stabilizers to be trivial, whereas the exceptional-orbit and sequence arguments do not need compact support. The current general `BBEKLowEntropyCore.rootAlternative_of_positive_entropy` signature assumes reductive-orbit exclusion, not compact Mahler support. A completed compact-specific contradiction would discharge the actual BBEK application, but would not by itself prove that more general signature without a corresponding scope adjustment.

No new EL conclusion is asserted here. In particular, the positive-entropy-to-root-pair bridge and actual leaf bad-set estimate remain necessary mathematical input to the final assembly.
## Verification and frozen module list

The first 16 modules below compiled individually. Their 101 new theorems passed a direct, unabstracted `#print axioms` audit: only `propext`, `Classical.choice`, and `Quot.sound` occurred. The script also checked that all 101 expected outputs were present. After clearing two harmless unused-variable warnings and sequentially recompiling the final two modules, all eight of their theorems were audited again with the same result. No full-project build was run by this subtask.

Raw checks: `work/ELExceptionalFinalAudit.lean` and `.log` (101 theorems); `work/ELUnifiedFinalAudit.lean` and `.log` (8 final-source rechecks). These are workspace checks; the publication's authoritative fresh build/audit is performed separately.

```
BBEKExceptionalFactorOrbit
BBEKExceptionalCentralizer
BBEKLeafSupportGeneration
BBEKOneRootFullSupport
BBEKAlgebraicRootSupport
BBEKInvariantConditionals
BBEKOneRootNoAtoms
BBEKCanonicalExceptional
BBEKConditionalLeafFibres
BBEKPairExceptional
BBEKExceptionalOrbitNull
BBEKLocalExceptional
BBEKRootFieldSeparation
BBEKLowEntropyBackend
BBEKCanonicalCovariance
BBEKUnifiedRootData
BBEKNoncentralSequence
```

The final seventeenth module, `BBEKNoncentralSequence`, compiled individually without warnings. All 12 of its theorems passed a separate unabstracted `#print axioms` audit, again using only `propext`, `Classical.choice`, and `Quot.sound`; all 12 expected outputs were present. Raw script/log: `work/ELNoncentralSequenceAudit.lean` and `.log`. Thus this subtask delivered 17 new modules and 113 new audited theorems in the current round. No new admitted proof or axiom was introduced.

