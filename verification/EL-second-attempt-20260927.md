# Second bounded EL attempt — 2026-09-27

**The EL admission was not eliminated.** The original two admitted declarations
remain unchanged. The final Problem 7 theorem still has raw axioms
`[propext, sorryAx, Classical.choice, Quot.sound]`. This document records proved
intermediate mathematics, not a proof of the admitted theorem.

## Completed connections

1. **The same actual canonical fields.** Strong root-translation covariance
   holds on one measurable conull set, for every pair of its points on the
   same root leaf. Independent-factor diagonal invariance, Weyl transport,
   covariance under the other diagonal time, and the projective-stabilizer
   consequences retain the same canonical field and normalization radius.
   Non-Diracness implies infinite total mass, full root support and absence
   of atoms for the compact-support application; non-Diracness itself is
   still a hypothesis at this step.
2. **A direct exceptional-orbit argument.** For this arithmetic quotient,
   pure-factor orbit maps are measurable embeddings, and such orbits have
   zero mass under the complementary root-kernel diagonal invariance.
   Equality fibres of the two actual opposite leaf fields are treated with
   countable compact integral tests. This proves that a positive measurable
   set cannot satisfy the specified local common-centralizer concentration.
   It bypasses a general rational closed-orbit classification in the compact
   application. It does not prove the original general EL theorem.
3. **Actual nearby pairs.** From a positive measurable set and the same
   opposite canonical fields, `BBEKNoncentralSequence` produces a base point
   and group displacements tending to the identity, with both fields equal
   along the sequence. A fixed lower or upper noncentral subsequence is
   selected. `BBEKPureRootShear` identifies the actual diagonal dynamics and
   pair displacements with the matrix shearing formula in each local factor.
4. **Paired times, parameters and limits.** A proved Hopf weak maximal bound
   produces common good visits. Quadratic scale selection and uniform
   nonconcentration for nonatomic leaf families produce nonvanishing
   shearing parameters. The matrix estimates give an actual nonzero root
   limit. The applicable endpoint samples the small parameter at the
   **total time** `T^[k+n] x`; it still requires the bad-leaf-set bound below.
5. **Compact comparison.** A Lusin theorem for the countable determining
   leaf tests is proved, with the compact set chosen inside any prescribed
   measurable conull set. Actual returning pairs and exact field equality
   (or vanishing differences of all tests) then give an exact limiting root
   return with equal leaf fields. Iteration and common translation preserve
   field equality on the appropriate common conull sets.
6. **Subordinate codes and conditional probabilities.** Boundary estimates,
   small partitions and literal chart safety construct measurable past
   codes whose fibres lie in the actual root orbit and almost everywhere
   contain a root neighbourhood. Positive code-fibre mass and normalized
   restriction formulas are proved for the genuine chart conditional kernel.
   The global past-code conditional law is identified with the normalized
   restriction of the **original ambient measure's** chart kernel, followed
   by the chart map; restriction to the active chart is explicitly removed.
   The finite and infinite reverse conditional-expectation maximal estimates
   are proved and identified with actual `condDistrib id` kernels of tail
   codes. Further conditional-measure interfaces in the compiled source
   retain their explicit hypotheses; their existence does not establish the
   final uniform bound for root-return bad sets.

See the detailed [exceptional-branch review](EL-exceptional-backend-20260927.md)
and [paired-shearing interfaces](BBEK-paired-return-progress-20260927.md),
with [the exact subordinate-code result](leaf-entropy-2026-09-26-notes.md).
The earlier [first increment](EL-progress-20260927.md) is historical.

## Exact remaining obligations

- Connect positive KS entropy of the designated time map to the **appropriate
  opposite root fields of one factor**, with the required almost-everywhere
  nonatomicity or a proved invariant-component reduction. A single non-Dirac
  root is insufficient for the current choice between lower and upper
  noncentral displacements. Joint-leaf nonatomicity does not imply that of
  each root conditional. General commuting-map entropy subadditivity is
  not a valid shortcut.
- Convert the reverse conditional-kernel bound to the literal root-return
  bad sets for these same canonical fields. In the quantitative sequence
  endpoint the input is
  `η (T^[k+n] x_i) (D i k n) ≤ 1/2` for all relevant indices and times.
  This must also put the sheared points in the same compact Lusin/conull
  set. The automatically chosen nonconcentration set does not silently
  contain the additional leaf maximal good event.
- Assemble the actual displacement sequence, total-time leaf sampling,
  returning pairs, common field transport and compact limit into a
  contradiction to the terminal root-separation theorem, with **one chosen
  pair of fields and one compatible conull set** throughout. This includes
  the upper-root/Weyl transport when the selected noncentral branch is upper.
- Respect the theorem's scope. The current admitted core assumes
  `NoProperReductiveClosedOrbit`, not compact Mahler support. Several new
  stabilizer and terminal theorems use compact support, as available at the
  Problem 7 application point. Closing that specialized route would require
  an honest corresponding change to the core/application/audit signatures,
  or an additional proof of the stated more general core. Compact support
  may not be silently introduced into its present proof.

The relevant sources are the authors' [general low-entropy paper, Sections
5–7](https://people.math.ethz.ch/~einsiedl/low-entropy.pdf) and
[maximally split torus paper, Sections 5–7](https://people.math.ethz.ch/~einsiedl/maxsplit.pdf).
No broad literature search or full Ratner–Tomanov formalization was undertaken.

## Verification and admission policy

New modules were compiled separately before integration. `VV/Audit.lean`
recursively checks **every theorem defined in the new modules without
abstracting either admission**. The ordinary project audit still checks
all definitions and the exact signatures of the only two permitted proof
admissions. A fresh full local build and audit, using revision-checked
pinned dependency caches, are recorded in [report.json](report.json) and
[final-axioms.txt](final-axioms.txt). This is not an empty-cache or independent
reproduction.

The two retained admissions are:

- `VV.P5FiniteCheck.rank_check_10_14`;
- `VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy`.

The user scheduled the finite-computation attempt after EL completion.
It was not started, and the large enumeration was not executed.
