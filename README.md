# Some Bounds Related to the 2-adic Littlewood Conjecture — Open Problems

A Lean research project addressing the open problems in [Dinis Vitorino and Ingrid Vukusic, *Some Bounds Related to the 2-adic Littlewood Conjecture*, Section 8](https://arxiv.org/html/2506.04110v2#S8). The intended scope is a complete answer to all of the paper's open problems. **This initial snapshot does not achieve that goal.** Its current results concern Problems 3, 4, 5 and 7, using actual real continued fractions and their tail-equivalence classes.

**Problems 1, 2 and 6 are not solved in this release. Problem 4 is only partially answered by the proved finiteness and upper bound below. The project is also not fully `sorry`-free: Problem 5 depends on an unexecuted, independently unverified finite check, and Problem 7 depends on one admitted Einsiedler–Lindenstrauss low-entropy core.**

[中文说明](README.zh.md) · [Proof status](PROOF_STATUS.md) · [AI disclosure](AI_DISCLOSURE.md) · [Third-party sources](THIRD_PARTY.md)

## Results and boundaries

| Problem | Formalized result | Entry point and remaining obligation |
|---|---|---|
| 1, 2, 6 | No solution supplied in this snapshot. | Open work for this project. |
| 3 | A tail class has a representative satisfying `x ~ x/2 ~ (x+1)/2` exactly when it has a primitive quadratic equation whose discriminant `D` satisfies `t² − Dv² = ±8` for odd integers `t,v`. Quadraticity and Serret's theorem are proved internally. | `VV.problem3_classification`; no admission. |
| 4 | Partial answer: for least eventual period `ℓ`, successful tail classes are finite and their number is at most `3 * ℓ * 4^ℓ`. Periods 0, 1 and 2 have no such classes. | `VV.Problem4.problem4_all_periods`; this specific bound has no admission. A general exact counting formula and the other unproved claims are not established here. |
| 5 | For every irrational real `x`, some fixed `k ≥ 0` has infinitely many partial quotients of `2^k x` at least 11. | `VV.P5FiniteCheck.problem5_bound_eleven`; conditional on the finite-check admission below. |
| 7 | The exceptional set `VV.BExceptional` has Hausdorff dimension zero. | `VV.problem7`; no external parameter in its signature, but its proof depends on the EL-core admission below. |

The discriminant in Problem 3 is that of a primitive integer quadratic equation; it must not be silently replaced by a number field's fundamental discriminant. For a fixed representative, the classification also requires the quadratic leading coefficient to be odd.

## Exactly two admitted declarations

1. `VV.P5FiniteCheck.rank_check_10_14`, in [VV/P5FiniteCheck.lean](VV/P5FiniteCheck.lean):

   ```lean
   (VV.P5Window.windowGraph 10 14).checkEventuallyDeterministic = true
   ```

   This assertion concerns the explicitly defined finite graph. The calculation has **not been executed or independently verified**. No original computation certificate is included, and agreement with a previously described pruning/merging implementation has not been established.

2. `VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy`, in [VV/BBEKLowEntropyCore.lean](VV/BBEKLowEntropyCore.lean): positive entropy, full split-diagonal invariance and ergodicity, and the stated reductive-orbit exclusion imply invariance under one nonzero real or 2-adic root element. The unformalized input covers the leafwise entropy argument, low-entropy shearing and exceptional-branch elimination. It is a theoretical admission, not a finite computation.

Root-group generation, all four root-escape branches, the entropy/box-dimension reductions and the final assembly are outside the EL admission. In [VV/BBEKFinal.lean](VV/BBEKFinal.lean), the project constructs:

```lean
VV.bbekTheorem42 : VV.P7BoxCover.BBEKTheorem42
VV.problem7 : VV.Problem7.Statement
```

The recorded raw axiom list for `VV.problem7` is `[propext, sorryAx, Classical.choice, Quot.sound]`. [VV/Audit.lean](VV/Audit.lean) validates the exact types of the two allowed admissions and abstracts only their proof bodies. Every other project declaration is then checked transitively against `propext`, `Classical.choice` and `Quot.sound`. A successful audit does not establish either admitted statement.

## Build and audit

The pinned toolchain is `leanprover/lean4:v4.20.1`, whose [official release](https://github.com/leanprover/lean4/releases/tag/v4.20.1) uses compiler commit `b02228b03f655c0cd051d82280ad5758359ec8ba`. Its release assets are named `lean-4.20.0-*`, and the compiler used for the existing verification reports identifies itself as **Lean 4.20.0**. This is the official release's tag/version discrepancy, not a locally invented toolchain alias. Mathlib is pinned to `5c0c94b3f563ed756b48b9439788c53b0d56a897`, with transitive dependencies in `lake-manifest.json`.

With the matching Lean/Lake compiler and dependencies available, run from the repository root on any supported platform:

```sh
lake build
lake env lean VV/Audit.lean
```

On Windows with PowerShell 7, the reporting wrapper also validates the compiler commit, checks the allowed admissions, and writes a report and source hashes:

```powershell
./Check-VV.ps1
```

An existing dependency checkout can optionally be supplied using `-DependencyPackages`; the wrapper checks its locked revisions and tracked-file cleanliness. Ordinary builds do not execute the large Problem 5 calculation. Build caches and private research archives are excluded from this publication.

Existing verification records describe the earlier local build and audit. Preparing these publication documents does **not** constitute a new clean-clone or cross-platform build. See [PROOF_STATUS.md](PROOF_STATUS.md) for how to interpret the evidence.

## Sources and reuse

The BBEK input is [Badziahin–Bugeaud–Einsiedler–Kleinbock, Theorem 4.2 and Section 5](https://arxiv.org/html/1405.5545v2), specialized to `p = 2`. The project does not claim a complete formalization of Einsiedler–Lindenstrauss or Ratner–Tomanov.

Imported and adapted entropy sources retain their Apache-2.0 license and attribution. **No project-wide license has yet been specified for the original contributions.** See [THIRD_PARTY.md](THIRD_PARTY.md). AI-assisted development and the limits of the review are disclosed in [AI_DISCLOSURE.md](AI_DISCLOSURE.md).
