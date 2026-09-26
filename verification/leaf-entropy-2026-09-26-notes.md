# Actual subordinate root codes and their conditional distributions

This work does not prove the positive-KS-entropy-to-root-entropy theorem and does
not remove the EL-core assumption. It closes a concrete earlier obstruction:
constructing actual measurable subordinate root partitions and identifying their
conditional probabilities with kernels disintegrated from the original measure.

## Construction now proved

1. For a finite measure, a measurable real observable and geometric widths,
   almost every threshold has summable boundary-strip masses. The selected
   threshold can be placed in any prescribed nonempty interval. Borel--Cantelli
   gives eventual avoidance along every measure-preserving orbit.
2. The actual chart safety radius is measurable and changes by at most the norm
   of a joint lower-root translation. No exponentially contracting quotient
   metric is assumed.
3. A finite safe-chart cover of a compact set admits positive thresholds with
   these summable boundaries. At every inverse mixed-time iterate, the code
   records the active flag and transverse coordinate in each chart.
4. Actual mixed time contracts each joint, real, and 2-adic lower-root parameter
   by at most `4^-n`. Thus each code fiber through the compact set lies in its
   literal root orbit and almost every fiber contains a positive root ball.
5. Refining an actual product disintegration by such a locally constant code
   yields positive-mass code atoms on almost every leaf. Its conditional kernel
   is the normalized restriction of the original leaf kernel to the code fiber.
   This is proved directly; it is not assumed as a new kernel interface.
6. The active flag and transverse coordinate are already determined by the
   code. Redundant conditioning is removed, the chart map is pushed forward,
   and restriction to a code-measurable active event is removed.
7. The final endpoint `global_pastCode_original_conditional` identifies the
   global `condDistrib id F μ` with the normalized restriction of the literal
   chart conditional kernel of the original `μ`, followed by the chart map.
   The intermediate kernel of `μ.restrict active` has been eliminated by an
   explicit restriction identity and cancellation of both normalizing factors.

## Remaining mathematical bridge

The endpoint concerns the original measure's actual chart kernel. Existing
canonical whole-root measures agree projectively with this chart kernel on
safe balls. A whole-code-fiber identification with the global canonical measure
still needs local-to-global comparison if that entire fiber is used.

More importantly, positive KS entropy has not yet been proved to force
nontrivial root entropy or a non-atomic actual root conditional. That requires
the relative entropy comparison for the constructed subordinate partition and
the center/stable zero-entropy bound. The new code construction and conditional
formula supply actual objects for that comparison but do not prove it.

No inference from non-atomicity to translation symmetry is made here. Low-entropy
shearing and the exceptional branch remain separate obligations.

## Modules

`BBEKLeafEntropyBoundary`, `GoodPartition`, `Safety`, `SafetyCuts`,
`Subordinate`, `SubordinateTime`, `SubordinateCharts`, `Refinement`,
`ChartConditionals`, `CodeConditioning`, `GlobalConditionals`, and
`CanonicalConditionals` are the new modules. `BBEKLeafEntropyDisintegration`
is an earlier completed module. Names in this list after the first entry share
the prefix `BBEKLeafEntropy`.

`GoodPartition` and `Disintegration` require their own imports; the other
construction modules are in the dependency chain of `CanonicalConditionals`.
The normalized restriction cancellation is supplied by
`BBEKNormalizedRestriction.normalize_restrict_normalize`.
