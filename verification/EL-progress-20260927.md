# EL formalization increment — 2026-09-27

**The EL core is not completed. Both previously declared admissions remain.**
The requested finite-computation trial was conditional on completing EL; it
was not started. No large Problem 5 computation was performed.

Seven new source modules establish the following results without either
admission:

- `BBEKLeafMeasureTests`: a fixed countable family of compactly supported
  continuous tests determines Radon measures, including infinite-total-mass
  measures; translated test integrals are continuous and family integrals measurable.
- `BBEKLeafStabilizerMeasurable`: hit-open measurability of the literal
  translation stabilizer of a measurable Radon family.
- `BBEKLeafStabilizerDichotomy`: a null-set modification and one contracting
  measure-preserving time give almost-everywhere trivial/full stabilizers,
  retaining the original family and normalization radius.
- `BBEKLeafStabilizerEscape`: compact support and full diagonal invariance
  exclude full leaf stabilizers almost everywhere, in all four root branches.
  Only a finite escape cover is intersected; no uncountable intersection of
  conull sets, top-event measurability or ergodic promotion is assumed.
- `BBEKRootContraction`: the actual normalized expanding covariance gives
  finite positive inverse-time multipliers at the same reference radius.
- `BBEKCompactLeafStabilizers`: the constructed real/p-adic lower/upper
  canonical families have almost-everywhere trivial exact and projective
  translation stabilizers for a full-diagonal-invariant probability supported
  on a positive Mahler compact.
- `BBEKLeafEntropyDisintegration`: transverse conditional entropy is exactly
  the average fiber entropy of the actual chart conditional kernel. Positive
  single-step conditional entropy excludes Dirac local kernels, not general
  atomic kernels or zero dynamical entropy.

This closes the previously recorded hit-measurability and contraction hookup
gap, and removes the need for full-diagonal leaf-field covariance and ergodic
promotion in the specialized compact-support contradiction.

It does not supply positive root entropy from positive KS entropy, the
paired-return/non-transience theorem in the low-entropy argument, or the
exceptional-centralizer-to-rational-closed-orbit passage. The original final
theorems still use `VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy`.
Their raw axioms therefore still include `sorryAx`. See
[the precise EL gap review](EL-core-gap-20260927.md).

Verification: all seven modules were compiled individually before integration.
`VV.Audit` includes a separate unabstracted audit of every new theorem. The
generated `report.json` and `final-axioms.txt` record the final full-project
build and audit outcome; these notes do not independently certify that outcome.
