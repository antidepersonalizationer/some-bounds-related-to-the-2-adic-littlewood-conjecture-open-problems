> Historical review, superseded in part by [the second attempt](EL-second-attempt-20260927.md). The general rational closed-orbit passage discussed below is now bypassed for this quotient; the entropy and full low-entropy application remain incomplete.

# EL core gap and leaf-stabilizer escape review — 2026-09-27

This is an independent source review, not a completion of the low-entropy theorem. No Lean source or admitted proof was changed for this review.

## Reviewed strengthening

`VV/BBEKLeafStabilizerEscape.lean` correctly proves `ae_stabilizer_ne_top_of_leaf_escape` and its four real/p-adic, lower/upper canonical-family specializations.

The quantifiers are sound. Compactness first selects finitely many escape pairs `(d,u)`. For each of those pairs, full diagonal invariance makes the closed set `d⁻¹ K` conull. Canonical support transfers this to the leaf. At any base point where the leaf stabilizer is the whole root group, positive mass in every zero neighborhood makes every translated neighborhood positive, so closed almost-everywhere support becomes support of the entire root orbit. Intersecting only the finitely many resulting conull sets contradicts the selected escape cover.

In particular, the argument does **not** intersect conull sets over the uncountable diagonal group. It does not need measurability of the top-stabilizer event, full-diagonal covariance of the leaf field, or ergodic promotion. The four specializations retain actual `IsConstructedRootFamily` / `IsConstructedUpperRootFamily` and positivity hypotheses; they do not replace canonical conditionals with arbitrary measures. No omitted mathematical hypothesis was found.

`ae_stabilizer_eq_bot_of_ne_top` is only the final logical combination with a separately proved bot/top dichotomy. Neither that lemma nor the escape theorem creates a nontrivial stabilizer. A nonzero symmetry at an exceptional single point is insufficient: the missing input must contradict almost-everywhere triviality (for example, a positive-measure nontriviality event).

## Precise remaining EL input

The checked source is [Einsiedler–Lindenstrauss, *On measures invariant under tori on quotients of semi-simple groups*, §§5–7](https://people.math.ethz.ch/~einsiedl/maxsplit.pdf). The following is a scope summary, not a formalized result:

- Theorem 6.1, itself quoted from earlier work, supplies the non-transience / exceptional-concentration dichotomy under faithful unipotent recurrence and its stated structural assumptions.
- Corollary 6.2 uses entropy symmetry and leaf product structure before applying that dichotomy. Its first branch obtains distinct points with matching leaf measures; leaf translation covariance then supplies a symmetry.
- The exceptional branch still needs §7's passage from centralizer-orbit concentration of kernel-of-root components to a proper rational reductive closed orbit. `NoProperReductiveClosedOrbit` excludes the endpoint, not this missing passage.

Ordinary one-point Poincaré recurrence and the already proved quadratic matrix-shearing formulas do not establish the required paired returns or that dichotomy. Likewise, joint-leaf non-atomicity does not by itself imply non-atomicity of either one-root conditional: a measure on the graph of an injective map is an elementary obstruction to that inference. Thus there remain both an entropy-to-root input and the genuine low-entropy comparison/exception-removal input. No new hypothesis, axiom, or `sorry` was introduced to stand in for them.

## Verification

The reviewed source file was compiled directly with the project environment and exited successfully. An independent six-endpoint `#print axioms` check (`work/ELGapReview.lean`) also exited successfully: the general escape theorem, all four root specializations, and the bot/top combination each depend only on `propext`, `Classical.choice`, and `Quot.sound`. The check did not abstract any admitted declaration. No full-project rebuild was run as part of this review.

