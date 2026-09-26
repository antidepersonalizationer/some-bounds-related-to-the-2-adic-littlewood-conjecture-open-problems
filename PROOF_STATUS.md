# Proof status of this research checkpoint

The goal is to answer all open problems in Vitorino and Vukusic's *Some Bounds Related to the 2-adic Littlewood Conjecture*. This checkpoint does not do so: Problems 1, 2 and 6 have no solution here; Problem 4 is partial; the stronger Problem 5 result and Problem 7 retain distinct admissions. A theorem with no external arguments can still depend on `sorryAx`.

## Results without admissions

- **Problem 3:** `VV.problem3_classification` classifies actual tail classes using a primitive quadratic equation and the odd-integer signed Pell condition `t² − Dv² = ±8`. Quadraticity and both directions of Serret's theorem are proved. The fixed-representative criterion additionally requires an odd leading coefficient.
- **Problem 4:** `VV.Problem4.problem4_all_periods` proves finiteness and count at most `3 * ℓ * 4^ℓ`. Periods 0, 1 and 2 are empty. `P4UniformDigits.lean` proves the equivalence between a class with a chosen root and an actual rooted periodic word, then constructs a common eventual digit alphabet of size at most `3 * ℓ² * 4^ℓ`. Its finite maximum gives a noncomputable uniform bound. `P4PeriodThree.lean` proves `card_class_three`, the complete tail-equivalence criterion `period_three_iff`, `uniformAlphabet_three : uniformAlphabet 3 = {1,3}`, `uniformDigitBound_three : uniformDigitBound 3 = 3` and `B_eq_three_of_period_three`. General exact counts and a general explicit numerical digit-bound formula remain open here.
- **Problem 5, small certificate:** `VV.P5SmallCertificate.frequently_three_within_two` proves that one of `x`, `2x`, `4x` has digits at least 3 infinitely often, for every irrational `x`. A height table on the actual bound-2 machine decreases along every successful transition; its finite verification uses ordinary `decide`. The proof certifies the original `windowGraph 2 0`, with 192 state/input vertices, rather than substituting an unrelated graph. This result validates the verification method, not an improvement over the paper's bound 5.
- **General Problem 5 reductions:** `P5GeneralWindow.lean` turns any suitable bounded-period window classification into discriminant growth, a frequently-large-digit result, and an eventual result for every window. The conditional bound 11 endpoint now uses this general argument. `P5GraphSimulation.lean` proves label-preserving graph simulation and transient pruning preserve actual continued-fraction tails. `P5SparseCertificate.lean` proves a supplied-rank sparse checker sound and complete and links explicit vertex encodings to the original graph. These theorems do not assert the existence of the large required certificate.
- **Canonical root-measure lemmas:** `BBEKOneRootAtoms.lean`, `BBEKOneRootRecurrence.lean` and `BBEKOneRootLocalInvariance.lean` prove atomic/Dirac alternatives, exactness of projective translation stabilizers, and local invariance of the actual selected conditional kernels on safe overlaps. The canonical construction and its chart restrictions are retained throughout. These lemmas do not imply positive entropy produces the required nonzero invariant root element.

These results use only `propext`, `Classical.choice` and `Quot.sound`. The whole-project audit checks this after abstracting precisely the two admitted proof bodies below.

`P4PeriodFour.lean` supplies the actual successful example `[5,2,1,2]`, with value `(5 + √33)/2`, exact period 4 and `B = 5`. The additional `P4PeriodFourClassification.lean` and its helper/branch modules prove `card_class_four : Nat.card (Class 4) = 1`, `period_four_iff`, `B_eq_five_of_period_four`, `uniformAlphabet_four : uniformAlphabet 4 = {1,2,5}` and `uniformDigitBound_four : uniformDigitBound 4 = 5`. The 48 symbolic parity/size branches cover unbounded integer digits, using the actual transition, cleanup, cyclic alignment and trace lemmas. No numerical digit cutoff is assumed. General period counts remain open.

`P5QuotientCertificate.lean` proves the actual machine graph is label-deterministic and pulls a rank certificate back through a label- and edge-preserving map to a smaller graph; the map need not be injective. `window_check_of_sparse_compression` concludes the original raw graph's Boolean check. `P5SCCCertificate.lean` proves this check is equivalent to uniqueness of an outgoing target within each strongly connected component. It constructs ranks mathematically from reachable sets; it does not claim to have implemented or executed a large SCC search.

`P5PrunedCertificate.lean` also pulls descent-certified transient pruning back to the original Boolean obligation, via the SCC criterion. Its `window_check_of_sparse_pruned_compression` requires neither an injective vertex map nor a comparison of graph sizes. The pruning rank must be nonincreasing along every raw edge, rank-preserving edges must survive, and all vertex labels must be preserved. No actual large pruning certificate is supplied. As a negative small test, `P5SmallObstruction.lean` checks eight actual transitions and proves `(windowGraph 3 0).checkEventuallyDeterministic = false`; this says nothing about the bound-10, depth-14 assertion.

`BBEKOneRootSupport.lean` proves actual support transfer in all four root branches. From `μ K = 1`, measurability of `K`, a positive reference radius and the canonical root-family construction, almost every leaf parameter sends its base point into `K`. This uses the literal chart pullback and conditional-kernel disintegration, then the centered maps and growing-ball restrictions. Compactness, diagonal invariance and leaf stabilizers are not smuggled in as replacements for that support argument.

`BBEKOneRootSupportEscape.lean` uses positive mass on every centered ball to turn almost-everywhere support into whole-root orbit containment when the leaf translation stabilizer is the whole group. Combining actual canonical support transfer with diagonal translates of the Mahler set and a finite escape cover yields `no_real_lower_top`, `no_padic_lower_top`, `no_real_upper_top` and `no_padic_upper_top`. These contradictions do not assume global ambient root invariance and do not use the EL admission. The missing entropy/shearing bridge is still needed to produce the leaf symmetry.

## Admission 1: Problem 5 finite check

```lean
VV.P5FiniteCheck.rank_check_10_14 :
  (VV.P5Window.windowGraph 10 14).checkEventuallyDeterministic = true
```

This precise assertion is still **unexecuted and independently unverified**. No original large computation certificate or concrete verified reduction to a small graph is included.

`P5StateSize.lean` proves symbolically that `windowGraph C r` has `C * (24 * C^2)^(3^r)` vertices. For the admitted instance this is `10 * 2400 ^ 4782969`. Its arbitrary finite numbering uses `Fintype.equivFin`; its original Boolean assertion decides existence of a whole rank function. Neither source-level finiteness nor a successful build makes that enormous check an executed program. The sparse and simulation interfaces provide ways to certify appropriate explicit data without pretending those data have been supplied.

The conditional real-number proof connects actual continued-fraction transformations, bounded buffers, synchronized windows, finite graph paths, eventual periodicity and quadratic discriminant growth. `VV.P5FiniteCheck.problem5_bound_eleven`, `problem5_limsup` and `eventual_every_31` depend on this admission. This is not a fully verified proof of the lower bound 11.

## Admission 2: EL low-entropy core

[VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy](VV/BBEKLowEntropyCore.lean) concerns the actual arithmetic quotient `X`, full split-diagonal group `A`, a probability measure, `A`-invariance and ergodicity, a measure-preserving designated time map, positive KS entropy, and `NoProperReductiveClosedOrbit`.

Its conclusion `RootAlternative μ` is invariance under one nonzero element of a real lower, real upper, 2-adic lower or 2-adic upper root group. The admission covers the leafwise entropy bridge, low-entropy shearing and exceptional-branch elimination. The current canonical leaf-measure results do not complete that argument. In particular, local proportionality with finite conditional probabilities does not allow replacing them by globally translation-invariant probabilities.

For the compact-support route, the 2026-09-27 increment proves measurability of open-hit events `{q | ∃ u ∈ translationStabilizer (η q), u ∈ O}` for the actual Radon leaf family and supplies the exact contraction and normalization hypotheses. The four constructed canonical root families now have almost-everywhere trivial exact and projective stabilizers. This specialized support-escape argument avoids ambient reconstruction and ergodic promotion. The positive KS-to-root entropy bridge, paired-return/non-transience theorem and exceptional-centralizer-to-rational-closed-orbit passage remain unproved.

The project separately proves generation of the full corresponding root group, all four Mahler escape cases, the compact-support contradiction, entropy production and averaging, the reductive-orbit exclusion at the application point, Proposition 5.1, and the box-dimension and Hausdorff-dimension reductions.

```lean
VV.bbekTheorem42 : VV.P7BoxCover.BBEKTheorem42
VV.problem7 : VV.Problem7.Statement
```

Neither takes BBEK as an external parameter. Both depend on the EL admission, with raw axioms `[propext, sorryAx, Classical.choice, Quot.sound]`. Full Einsiedler–Lindenstrauss or Ratner–Tomanov formalization is not claimed.

## Audit and build evidence

[VV/Audit.lean](VV/Audit.lean) validates the exact types and type dependencies of the two admissions. It abstracts only those two proof bodies while recursively checking every other project declaration and dependency. Additional project axioms and opaque interfaces are rejected. The raw axiom output for final theorems remains visible.

This checkpoint was validated by one final local project build and Audit after individual compilation of new modules. Pinned dependency caches were reused after revision and tracked-file cleanliness checks. [verification/report.json](verification/report.json) records the run time, declaration counts and SHA-256 hashes of the exact build inputs. Every published build input matches those hashes. [verification/final-axioms.txt](verification/final-axioms.txt) contains the actual selected axiom output. The wrapper also requires all project Lean files to belong to the `VV`/`VV.Audit` import closure. Extra `verification/*.lean` files are optional inspection helpers; the authoritative recursive audit is `VV/Audit.lean`.

Selected new endpoints also undergo a separate recursive axiom assertion with **no proof abstractions at all**, so an accidental dependency on either admission fails validation rather than merely appearing in printed output.

This is not an empty-cache clean-clone build, independent review, or proof of either admission. Re-run `lake build` and `lake env lean VV/Audit.lean` for the checkout under examination. `Check-VV.ps1` is the PowerShell 7 reporting wrapper.

The toolchain is `leanprover/lean4:v4.20.1`, whose [official release](https://github.com/leanprover/lean4/releases/tag/v4.20.1) uses commit `b02228b03f655c0cd051d82280ad5758359ec8ba` and asset names `lean-4.20.0-*`. The compiler reports Lean 4.20.0. Mathlib is pinned to `5c0c94b3f563ed756b48b9439788c53b0d56a897`.

## Remaining work

- Answer Problems 1, 2 and 6, and complete Problem 4 beyond the established results.
- Supply and verify the precise Problem 5 certificate or a mathematically justified replacement proof.
- Prove the stated EL root-invariance core, including the entropy and shearing bridges.
- Independently reproduce the build and review correspondence between formal and informal mathematics.


## EL increment, 2026-09-27

The latest increment proves actual leaf-stabilizer hit measurability,
radius-preserving contraction dichotomies, almost-everywhere root escape,
and trivial exact/projective stabilizers for the four constructed canonical
root families on a Mahler compact. It also identifies transverse conditional
entropy with the actual chart kernels. See
[the detailed progress and remaining gaps](verification/EL-progress-20260927.md).

**EL is still incomplete; the two named admissions remain.** Positive KS
entropy has not yet been connected to the needed root entropy, and the
low-entropy paired-return and exceptional-orbit arguments are not proved.
The finite-computation trial scheduled after EL completion was not started.
