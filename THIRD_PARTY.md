# Third-party sources and licensing

**No project-wide license has yet been specified for this project's original contributions.** Publishing the repository does not relicense those contributions or change the licenses of third-party code. The existing third-party notices and license text must be retained.

## Adapted entropy formalization

Selected modules under `VV/Entropy/` are adapted from Marcel Morgenstern's [lean4-ergodic-theory](https://github.com/marcmorningstar/lean4-ergodic-theory), source commit `040fec2e0ddf4fcba49af9f76c866d295308dd7f`.

- Copyright: Marcel Morgenstern, 2026, as recorded in the retained source headers.
- License: Apache-2.0; the full text is in [VV/Entropy/LICENSE](VV/Entropy/LICENSE).
- File selection and compatibility changes: [VV/Entropy/NOTICE](VV/Entropy/NOTICE).
- Adaptations include the import root, APIs of the pinned Lean/mathlib environment, finite-sum and conditional-expectation interfaces, and local replacement proofs described in the notice.

The original upstream environment used Lean 4.30.0-rc2 and mathlib commit `34f7a6cd150fd7a166958d989d5abab56e9e3d15`; its compiled binaries are not part of this project. The existence of adapted files in this directory does not imply that every local entropy module came from upstream. The notice identifies imported modules and locally written additions.

`KSEntropyInverse.lean` is a local extension written for this project on top of the vendored entropy API. There is no corresponding module at upstream commit `040fec2e0ddf4fcba49af9f76c866d295308dd7f`. The inverse-transformation proof uses definitions and lemmas from upstream `KSEntropy.lean` and `KSEntropySystem.lean`, together with their finite-partition and subadditive-limit dependencies. Its pre-existing Marcel Morgenstern / Apache-2.0 header has been retained as an attribution notice for that upstream foundation; it must not be read as attributing the locally added inverse proof to the upstream author or implying upstream review.

## Compact probability measures

`VV/Entropy/CompactProbability.lean` adapts the compact-space part of [mathlib's Prokhorov module](https://github.com/leanprover-community/mathlib4/blob/34f7a6cd150fd7a166958d989d5abab56e9e3d15/Mathlib/MeasureTheory/Measure/Prokhorov.lean) at commit `34f7a6cd150fd7a166958d989d5abab56e9e3d15`.

It retains the copyright of Sébastien Gouëzel, 2025, and the Apache-2.0 notice. This is not a backport of the general noncompact Prokhorov theorem. The namespace and compatibility adaptations are documented in `VV/Entropy/NOTICE`.

## Build dependencies

The project depends on mathlib at commit `5c0c94b3f563ed756b48b9439788c53b0d56a897`. `lake-manifest.json` locks the transitive package versions. Dependencies are fetched through Lake and retain their own upstream licenses and notices; dependency caches and compiled artifacts are not part of the source release.

## Mathematical references

- [Vitorino–Vukusic, arXiv:2506.04110v2, Section 8](https://arxiv.org/html/2506.04110v2#S8): the numbered continued-fraction problems.
- [Badziahin–Bugeaud–Einsiedler–Kleinbock, *On the complexity of a putative counterexample to the p-adic Littlewood conjecture*, arXiv:1405.5545v2](https://arxiv.org/html/1405.5545v2): Theorem 4.2 and its proof in Section 5, specialized here to `p = 2`.
- [Einsiedler–Kleinbock, *Measure rigidity and p-adic Littlewood-type problems*](https://arxiv.org/html/math/0506514): the dynamical entropy route used in the reduction.

These references provide mathematical provenance, not a claim that the authors reviewed or endorsed this repository. The EL low-entropy input remains explicitly admitted as described in `PROOF_STATUS.md`.
