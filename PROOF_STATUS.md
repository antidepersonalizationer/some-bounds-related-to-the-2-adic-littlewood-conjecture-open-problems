# Proof status — shortened application, 2026-09-27

This split changes the proof boundary; it does not complete EL or the large computation.

## Exact admissions

### Finite check

`VV.P5FiniteCheck.rank_check_10_14`:

```lean
(VV.P5Window.windowGraph 10 14).checkEventuallyDeterministic = true
```

This assertion has not been executed or independently verified. The raw graph has `10 * 2400 ^ 4782969` vertices, proved symbolically without evaluating the power. Its original numbering and Boolean specification do not constitute an efficient executable enumeration. The small checked certificate and compression lemmas do not verify this particular large input.

### Compact entropy exclusion

`VV.BBEKCompactEntropyCore.no_positive_entropy_supported_K` states, on the literal arithmetic quotient `X`, for every probability `μ` invariant and ergodic under the full split diagonal `A`, every `δ > 0`, and every proof that the designated map preserves `μ`:

```text
μ (K δ) = 1  →  0 < ksEntropy(timeMap time0, μ)  →  False.
```

Its exact Lean type is checked by `VV/Audit.lean`. It replaces the older `rootAlternative_of_positive_entropy` proof body in this application. The new admitted conclusion includes compact positive-entropy exclusion itself; it does not include the entropy-production, averaging, zero-box conversion or final Problem 7 reductions. All required leafwise entropy and return estimates remain unproved here. The original stronger root-alternative target is preserved in the companion repository's optional `Research` entry point.

## Endpoints and trust

`VV.bbekTheorem42 : VV.P7BoxCover.BBEKTheorem42` and `VV.problem7 : VV.Problem7.Statement` have no external BBEK parameter. They nevertheless depend on `sorryAx` through the compact exclusion. They do not depend on the Problem 5 finite check.

The recursive audit abstracts exactly the two listed theorem proof bodies, verifies their types without abstraction, and permits only `propext`, `Classical.choice`, `Quot.sound` everywhere else. No custom axiom or opaque interface is allowed. A passed audit establishes this boundary, not mathematical truth of the admissions.

Problems 3 and the stated partial Problem 4 results, and the small Problem 5 certificate, require no admission. Problems 1, 2 and 6 are unresolved in this project. See README for exact scope.

Local build details and actual axiom lists: [report](verification/report.json), [axioms](verification/final-axioms.txt). The verification uses pinned dependency caches and may reuse byte-identical project caches; it is not an independent review or an empty-cache clone test.
