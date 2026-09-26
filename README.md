# Some Bounds Related to the 2-adic Littlewood Conjecture — Open Problems

A Lean research project addressing the open problems in [Dinis Vitorino and Ingrid Vukusic, *Some Bounds Related to the 2-adic Littlewood Conjecture*, Section 8](https://arxiv.org/html/2506.04110v2#S8). The goal is a complete answer to all of the paper's open problems. **This research checkpoint does not achieve that goal.** The current results concern Problems 3, 4, 5 and 7, using actual real continued fractions and their tail-equivalence classes.

**Problems 1, 2 and 6 are not solved here. Problem 4 remains partial. The bound 11 for Problem 5 and the dimension-zero result for Problem 7 still depend on two explicitly identified admissions.** The new small Problem 5 certificate is fully checked, but does not verify the larger bound 11 calculation.

[中文说明](README.zh.md) · [Proof status](PROOF_STATUS.md) · [AI disclosure](AI_DISCLOSURE.md) · [Third-party sources](THIRD_PARTY.md)

## Results and boundaries

| Problem | Formalized result | Entry point and remaining obligation |
|---|---|---|
| 1, 2, 6 | No solution supplied. | Open work for this project. |
| 3 | A tail class has a representative satisfying `x ~ x/2 ~ (x+1)/2` exactly when it has a primitive quadratic equation whose discriminant `D` satisfies `t² − Dv² = ±8` for odd integers `t,v`. Quadraticity and Serret's theorem are proved internally. | `VV.problem3_classification`; no admission. |
| 4 | Successful classes of least eventual period `ℓ` are finite, with count at most `3 * ℓ * 4^ℓ`. Periods 0, 1 and 2 are empty. Periods 3 and 4 each have exactly one class, with `B = 3` and `B = 5` respectively. A finite common eventual digit alphabet exists for every `ℓ`. | `VV.Problem4.problem4_all_periods`, `card_class_three`, `card_class_four`, `period_three_iff`, `period_four_iff`, `exists_uniform_eventual_bound`; no admission. A general exact counting formula and an explicit general numerical digit bound remain open here. |
| 5, checked small instance | For every irrational `x`, one of `x`, `2x`, `4x` has partial quotients at least 3 infinitely often. | `VV.P5SmallCertificate.frequently_three_within_two`; no admission. This validates the certificate method and does not improve the paper's bound 5. |
| 5, stronger conditional result | For every irrational `x`, some fixed `k ≥ 0` has infinitely many partial quotients of `2^k x` at least 11. | `VV.P5FiniteCheck.problem5_bound_eleven`; still depends on the large finite-check admission. |
| 7 | The exceptional set `VV.BExceptional` has Hausdorff dimension zero. | `VV.problem7`; no external parameter, but depends on the EL-core admission. |

The discriminant in Problem 3 belongs to a primitive integer quadratic equation; it must not be silently replaced by a number field's fundamental discriminant. For a fixed representative, the criterion additionally requires an odd leading coefficient.

The new Problem 4 alphabet has at most `3 * ℓ² * 4^ℓ` elements. Its maximum is defined noncomputably from a proved finite set; this is not an evaluated formula for the largest digit. The new Problem 5 graph simulation, pruning and sparse certificate lemmas are proved for their stated finite hypotheses. No concrete compression of the bound-10, depth-14 graph is supplied.

The certificate framework includes both a positive small instance and a negative one: the original zero-depth bound-3 graph fails its rank check, witnessed by eight kernel-checked transitions. Certified transient pruning can now discharge the original check through `VV.P5PrunedCertificate.window_check_of_sparse_pruned_compression`; the large input data remain to be found and verified.

The unique period-3 class is represented by `(3 + √17)/2`, with periodic word `[3,1,1]`. The unique period-4 class is represented by `(5 + √33)/2`, with word `[5,2,1,2]`. The corresponding common eventual alphabets are exactly `{1,3}` and `{1,2,5}`. `VV/P4PeriodFourClassification.lean` assembles the period-4 proof from 48 symbolic parity/size branches covering unbounded integer digits; it is not an enumeration up to a numerical digit cutoff.

## Exactly two admitted declarations

1. `VV.P5FiniteCheck.rank_check_10_14`, in [VV/P5FiniteCheck.lean](VV/P5FiniteCheck.lean):

   ```lean
   (VV.P5Window.windowGraph 10 14).checkEventuallyDeterministic = true
   ```

   This precise assertion has **not been executed or independently verified**. The raw graph has `10 * 2400 ^ 4782969` vertices, proved symbolically without evaluating the power. Its original numbering uses a noncomputable finite equivalence, and its Boolean definition decides existence of an entire rank assignment. Finiteness alone does not make this an efficient executable calculation. The new certificate interfaces connect supplied finite data back to the original graph; the required large certificate is still missing.

2. `VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy`, in [VV/BBEKLowEntropyCore.lean](VV/BBEKLowEntropyCore.lean): positive entropy, full split-diagonal invariance and ergodicity, and the stated reductive-orbit exclusion imply invariance under one nonzero real or 2-adic root element. The unformalized input covers the leafwise entropy argument, low-entropy shearing and exceptional-branch elimination. It is a theoretical admission.

Canonical one-root families now have proved atomic/Dirac alternatives, equality of projective and exact leaf translation stabilizers, and local conditional-measure invariance on overlapping chart domains. `BBEKOneRootSupport.lean` also transfers full ambient measure on a measurable set to almost-everywhere support of each of the four actual root families on the corresponding root-orbit preimage. These are preparatory lemmas, not a proof of the EL core. In particular, local leaf invariance has not been silently identified with global ambient measure invariance.

`BBEKOneRootSupportEscape.lean` completes a further conditional route: a canonical root family whose leaf translation stabilizers are the whole root group contradicts full-diagonal invariance and support in a positive Mahler compact set. All four branches are proved, without assuming ambient root invariance. Obtaining that leaf symmetry from the entropy hypotheses is still missing.

Root-group generation, all four root-escape branches, the entropy/box-dimension reductions and final assembly are outside the EL admission. [VV/BBEKFinal.lean](VV/BBEKFinal.lean) constructs:

```lean
VV.bbekTheorem42 : VV.P7BoxCover.BBEKTheorem42
VV.problem7 : VV.Problem7.Statement
```

The raw axiom list for `VV.problem7` is `[propext, sorryAx, Classical.choice, Quot.sound]`. [VV/Audit.lean](VV/Audit.lean) validates the exact types of the two admissions and abstracts only their proof bodies. Every other project declaration is checked transitively against `propext`, `Classical.choice` and `Quot.sound`. A successful audit does not prove either admitted statement.

## Build and audit

The pinned toolchain is `leanprover/lean4:v4.20.1`, whose [official release](https://github.com/leanprover/lean4/releases/tag/v4.20.1) uses compiler commit `b02228b03f655c0cd051d82280ad5758359ec8ba`. Its release assets are named `lean-4.20.0-*`, and the compiler identifies itself as **Lean 4.20.0**. This is the official tag/version discrepancy. Mathlib is pinned to `5c0c94b3f563ed756b48b9439788c53b0d56a897`, with transitive dependencies in `lake-manifest.json`.

With the matching compiler and dependencies available, run from the repository root:

```sh
lake build
lake env lean VV/Audit.lean
```

On Windows with PowerShell 7, the reporting wrapper also checks compiler identity, import coverage of every project Lean source, and the allowed admissions:

```powershell
./Check-VV.ps1
```

An existing dependency checkout can be supplied using `-DependencyPackages`; the wrapper verifies its locked revisions and tracked-file cleanliness. Ordinary builds do not execute the large Problem 5 check. The small certificate uses ordinary kernel-checked `decide`, not `native_decide`.

This checkpoint includes a fresh local project build and recursive audit, using pinned dependency caches. The counts, time and source hashes are in [verification/report.json](verification/report.json), with actual axiom output in [verification/final-axioms.txt](verification/final-axioms.txt). This is not an empty-cache clean-clone build, a cross-platform test or independent mathematical review. Public file hashes are recorded separately in [verification/publication-manifest.json](verification/publication-manifest.json).

## Sources and reuse

The BBEK input is [Badziahin–Bugeaud–Einsiedler–Kleinbock, Theorem 4.2 and Section 5](https://arxiv.org/html/1405.5545v2), specialized to `p = 2`. The project does not claim a complete formalization of Einsiedler–Lindenstrauss or Ratner–Tomanov.

Imported and adapted entropy sources retain their Apache-2.0 license and attribution. **No project-wide license has been specified for original contributions.** See [THIRD_PARTY.md](THIRD_PARTY.md). AI-assisted development and review limits are disclosed in [AI_DISCLOSURE.md](AI_DISCLOSURE.md).


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
