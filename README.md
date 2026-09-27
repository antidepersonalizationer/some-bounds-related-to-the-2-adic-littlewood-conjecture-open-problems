# Some Bounds Related to the 2-adic Littlewood Conjecture — Open Problems

A Lean research project addressing the open problems in Dinis Vitorino and Ingrid Vukusic, [*Some Bounds Related to the 2-adic Littlewood Conjecture*, Section 8](https://arxiv.org/html/2506.04110v2#S8).
The aim is to answer all the open problems. **This checkpoint does not achieve that aim.** Problems 1, 2 and 6 are not solved; Problem 4 is partial; the bound 11 in Problem 5 and the dimension-zero conclusion in Problem 7 remain conditional on explicitly admitted inputs.

[中文说明](README.zh.md) · [Proof status](PROOF_STATUS.md) · [Module inventory](docs/MODULES.md) · [AI disclosure](AI_DISCLOSURE.md) · [Licensing](THIRD_PARTY.md)

## Results

| Problem | Result in this project | Status / entry point |
|---|---|---|
| 3 | Tail-class classification by a primitive quadratic discriminant and an odd-integer equation `t² − Dv² = ±8`. | Proved: `VV.problem3_classification`. |
| 4 | Finiteness for each least eventual period; at most `3 * ℓ * 4^ℓ` classes. Periods 0, 1, 2 are empty; periods 3 and 4 each have one class. A finite common eventual digit alphabet exists for each period. | Proved: `VV.Problem4.problem4_all_periods`, `card_class_three`, `card_class_four`, `exists_uniform_eventual_bound`. General exact counts and an explicit numerical digit bound remain open here. |
| 5, small certificate | One of `x`, `2x`, `4x` has partial quotients at least 3 infinitely often, for each irrational `x`. | Proved: `VV.P5SmallCertificate.frequently_three_within_two`. Does not improve the paper's bound 5. |
| 5, bound 11 | Some fixed power-of-two multiple of each irrational has partial quotients at least 11 infinitely often. | Conditional: `VV.P5FiniteCheck.problem5_bound_eleven`. The large finite check is unverified. |
| 7 | The exceptional set `VV.BExceptional` has Hausdorff dimension zero. | Conditional: `VV.problem7`. The compact entropy exclusion below is unproved. |

The discriminant in Problem 3 is that of a primitive integer quadratic equation; it is not silently replaced by a number field's fundamental discriminant. Periods 3 and 4 have representatives `(3 + √17)/2` and `(5 + √33)/2`, respectively. The finite alphabet in the general Problem 4 result is noncomputable; no general evaluated maximum is supplied.

## Shortened Problem 7 route

Failure of zero upper box dimension gives a full-diagonal invariant, ergodic probability measure with positive designated entropy and mass one on a positive Mahler compact `K δ`. The remaining theoretical input says this is impossible. The project then proves zero upper box dimension and performs the BBEK/continued-fraction reductions to Problem 7.

```text
nonzero trapped box dimension
    → compactly supported full-diagonal positive-entropy ergodic probability [proved]
    → contradiction [ADMITTED compact entropy exclusion]
    → trapped zero box dimension → BBEK Theorem 4.2 → Problem 7 [proved reductions]
```

Exactly two proof bodies are admitted:

1. `VV.P5FiniteCheck.rank_check_10_14`, in [VV/P5FiniteCheck.lean](VV/P5FiniteCheck.lean).
2. `VV.BBEKCompactEntropyCore.no_positive_entropy_supported_K`, in [VV/BBEKCompactEntropyCore.lean](VV/BBEKCompactEntropyCore.lean).

The second is a **changed admission boundary, not a newly proved theorem**. It replaces the previous, more general root-alternative admission in this application. The large finite check has not been executed. See [exact signatures and limitations](PROOF_STATUS.md).

The parameter-free entries `VV.bbekTheorem42` and `VV.problem7` are constructed internally in [VV/BBEKFinal.lean](VV/BBEKFinal.lean). Their raw axiom lists still include `sorryAx`.

## Separated theory development

The [S-arithmetic dynamics foundations repository](https://github.com/antidepersonalizationer/s-arithmetic-dynamics-lean) preserves 180 source modules outside the shortened application's import closure, plus their dependencies. It organizes entropy, leafwise measures, shearing, arithmetic dynamics and algebraic-orbit work. Its proved entry point has no admitted proofs; its optional EL research target has one.

Removal from this application is not evidence that a lemma is mathematically useless or unnecessary for a future proof of the compact entropy exclusion. In particular, canonical leafwise-measure and return-estimate tools may still be needed. This split does not claim a formalization of the entire EL or Ratner–Tomanov theory. [Split method and provenance](docs/SPLIT.md).

## Build and audit

```sh
lake build
lake env lean VV/Audit.lean
```

With PowerShell 7, `./Check-Project.ps1` runs the build, checks complete import coverage, verifies the exact admitted signatures and recursively audits project declarations. `./Check-VV.ps1` is an equivalent compatibility entry point. Optional `-DependencyPackages PATH` reuses clean dependency checkouts after checking their locked revisions.

The toolchain label is `leanprover/lean4:v4.20.1`; the compiler reports Lean 4.20.0 and commit `b02228b03f655c0cd051d82280ad5758359ec8ba`. Mathlib is pinned to `5c0c94b3f563ed756b48b9439788c53b0d56a897`. See [BUILD.md](BUILD.md) for the version-label discrepancy and setup.

The published [verification report](verification/report.json) and [axiom output](verification/final-axioms.txt) report local builds using pinned caches. They are not an empty-cache clean-clone test or independent mathematical review. No compiled caches are published. An audit pass does not discharge an admission.

Adapted third-party sources retain their licenses. No project-wide license has been specified for original contributions. See [THIRD_PARTY.md](THIRD_PARTY.md).
