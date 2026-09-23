# Proof status of this research snapshot

This file separates proved Lean results, admitted obligations and build evidence. A theorem having no external arguments does not imply that its proof is free of `sorryAx`.

The project aims to answer all open problems in Dinis Vitorino and Ingrid Vukusic's *Some Bounds Related to the 2-adic Littlewood Conjecture*. The current release does not do so: Problems 1, 2 and 6 have no solution here; Problem 4 is only partially answered; and Problems 5 and 7 retain the distinct admissions below.

## Proved results without admissions

- **Problem 3:** `VV.problem3_classification` classifies actual tail-equivalence classes by a primitive quadratic equation and the odd-integer signed Pell condition `t² − Dv² = ±8`. Quadraticity and both directions of Serret's theorem are proved. The fixed-representative criterion additionally requires an odd leading coefficient.
- **Problem 4, partial answer:** `VV.Problem4.problem4_all_periods` proves finiteness and the upper bound `3 * ℓ * 4^ℓ` on successful classes of least eventual period `ℓ`. Periods 0, 1 and 2 are empty. A general exact enumeration and the candidate digit-bound formula remain unproved. The proved bound does not constitute a complete answer to Problem 4.

These conclusions use the standard permitted axioms `propext`, `Classical.choice` and `Quot.sound`.

## Admission 1: Problem 5 finite check

```lean
VV.P5FiniteCheck.rank_check_10_14 :
  (VV.P5Window.windowGraph 10 14).checkEventuallyDeterministic = true
```

The graph and Boolean check are explicitly defined in the source. This check has not been executed or independently verified as true. A previously described finite computation has not been reproduced, its original certificate is not included, and equivalence with that implementation has not been established.

The remaining proof connects the actual continued-fraction transformations, bounded buffers, synchronized windows, finite graph paths, eventual periodicity and quadratic discriminant growth. The resulting declaration `VV.P5FiniteCheck.problem5_bound_eleven` says that for each irrational `x`, there exists one fixed doubling exponent whose partial quotients are at least 11 infinitely often. `problem5_limsup` and `eventual_every_31` depend on the same admission.

This release must not be described as a fully verified proof of the lower bound 11. Removing this admission requires a proof of this precise finite statement or a verified certificate procedure together with its connection to this exact graph.

## Admission 2: the EL low-entropy core

The only admitted theoretical declaration is [VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy](VV/BBEKLowEntropyCore.lean). Its hypotheses use the actual arithmetic quotient `X`, the full split-diagonal group `A`, a probability measure, `A`-invariance and ergodicity, a measure-preserving designated time map, positive KS entropy and `NoProperReductiveClosedOrbit`.

Its conclusion, `RootAlternative μ`, asserts that one nonzero element of one of the four local root groups preserves the measure: real lower, real upper, 2-adic lower or 2-adic upper. It does not assert a final dimension theorem.

The admitted argument comprises the leafwise entropy bridge, low-entropy shearing and elimination of the exceptional alternative. The existing leafwise-measure infrastructure does not complete that argument, and this release does not claim full EL or Ratner–Tomanov formalization.

The following are proved separately: extension from a nonzero root element to its full root group using diagonal normalization; all four Mahler escape cases; the compact-support contradiction; entropy production and averaging; the reductive-orbit exclusion used at the application point; Proposition 5.1; and the conversion to zero upper box dimension and then Problem 7.

The assembled declarations are:

```lean
VV.bbekTheorem42 : VV.P7BoxCover.BBEKTheorem42
VV.problem7 : VV.Problem7.Statement
```

Neither takes BBEK as an external parameter. Both depend transitively on the EL-core admission. The recorded raw axiom list for each is `[propext, sorryAx, Classical.choice, Quot.sound]`.

## Audit interpretation

[VV/Audit.lean](VV/Audit.lean) checks the exact signatures of the two admitted declarations and checks their signature dependencies. It then abstracts only their proof bodies while recursively auditing other project declarations. It rejects additional project axioms, opaque interfaces or dependencies outside the standard three axioms. The final raw axiom output is also printed, so `sorryAx` remains visible for the final Problem 5 and 7 declarations.

The existing verification record reports a successful build and audit of 3,392 theorem declarations and 837 definitions, with two admitted declarations. Its 268 recorded build-input hashes matched the source snapshot when inspected for publication. Publication edits to comments, notices, configuration or the reporting script can change those hashes; a changed source must not be presented as covered by an old hash manifest without qualification.

These are prior local verification records. Writing the public documentation is not a new clean-clone build, an independent mathematical review or verification of either admitted assertion. Re-run `lake build` and `lake env lean VV/Audit.lean` for the checkout being examined; `Check-VV.ps1` provides the Windows reporting wrapper.

The pinned toolchain is `leanprover/lean4:v4.20.1`, whose [official release](https://github.com/leanprover/lean4/releases/tag/v4.20.1) uses commit `b02228b03f655c0cd051d82280ad5758359ec8ba` and asset names `lean-4.20.0-*`. The compiler identifies itself as Lean 4.20.0. The release tag and version output therefore differ in the official distribution; this is not an unverified local alias. Mathlib is pinned to `5c0c94b3f563ed756b48b9439788c53b0d56a897`.

## Current priorities

- Answer Problems 1, 2 and 6, and complete the parts of Problem 4 beyond the proved finiteness and count bound.
- Independently verify the precise finite graph obligation for Problem 5.
- Prove the narrowly stated EL root-invariance core.
- Reproduce the build and audit from a clean checkout using a publicly obtainable, precisely documented compiler.
- Review that the formal definitions and hypotheses faithfully express the intended mathematical statements.
