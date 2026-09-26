# Paired-return proof increment, 2026-09-27

The following are actual proved parts of the low-entropy argument. They do not discharge `BBEKLowEntropyCore.rootAlternative_of_positive_entropy`.

## Hopf maximal bound

`VV/BBEKPairedReturnMaximal.lean` proves the signed finite Hopf inequality directly from invariance, using the recursive maximum of the first Birkhoff sums. For every finite invariant measure and measurable bad set B,

    μ {q : some n has badVisits(T,B,n,q) > ε n} ≤ μ(B) / ε.

The countable supremum uses continuity from below, so the constant is independent of time length. For a probability measure, `exists_all_lengths_good_set_of_small_bad` gives one measurable G with μ(G)>1−ε whenever μ(B)<ε², and every point of G satisfies the frequency bound at every length. No ergodic maximal theorem or good-set hypothesis is postulated.

## Simultaneous return times

`VV/BBEKPairedReturnTimes.lean` studies the concrete integer schedule

    shearTime(s,t,k) = min(k+s, floor((k+t)/2)).

Each fiber has cardinality at most two: equality of both the schedule and parity forces equality of source times. Consequently pulling back bad times loses at most a factor of two. The theorem `exists_uniform_paired_return_set` obtains a single measurable set G of mass greater than 99/100 from μ(B)<1/10000. For every pair x,y in G and every s,t, it produces a common k<floor(min(s,floor(t/2))/4)+1 such that both points avoid B at k and at shearTime(s,t,k). The finite horizon and numerical room estimates are proved internally.

## Actual matrix normalization

`VV/BBEKQuadraticScale.lean` constructs s,t from the actual nonconstant coefficient sizes of an SL₂ displacement, including either zero-coefficient case. Its `actual_lower_shear` identifies the two coefficients in the real matrix product after diagonal conjugation and root dilation. For a normed field and a diagonal parameter of norm two, `exists_actual_shear_scales` proves that the two rescaled coefficient norms are at most one and their maximum exceeds 1/16 throughout the entire search interval. Thus the schedule parameters in the preceding paragraph can be chosen from actual matrix coefficients.

## Uniform polynomial nonconcentration

`BBEKShearNonconcentration.lean` proves that a nonzero polynomial `a*v+b*v²` has at most two roots and hence a nonatomic measure gives its zero set mass zero. Continuity from above and a finite cover of a compact annulus of coefficients give one positive sublevel threshold for every normalized coefficient pair. This uses neither a doubling assumption nor an unproved polynomial small-ball estimate.

`BBEKShearFamilyNonconcentration.lean` upgrades this to an actual measurable family: after restricting the canonical radius-r ball, it constructs a measurable base set of mass greater than `1−κ` and a single positive threshold working for every point of that set and every coefficient pair with norms at most one and maximum at least `c`. Measurability is proved through a countable dense coefficient family and enlarged sublevels. The global leaf measure can have infinite total mass. Its actual radius-r normalization and almost-everywhere nonatomicity are explicit hypotheses; the module does not infer nonatomicity from positive entropy.

## A nonidentity root limit from actual matrices

`BBEKShearLimit.lean` proves quantitative bounds for the actual conjugated SL₂ matrices. The upper entry is at most the square root of the original upper entry's norm. Each diagonal correction is at most `R` times its fourth root. The lower entry is bounded above by the original lower entry plus `R+R²`, and below by the polynomial lower bound minus the original lower entry. Consequently `exists_nonzero_lower_limit` constructs a strict subsequence converging to a genuine nonidentity lower-root element whenever the original displacement tends to the identity and the normalized polynomial stays uniformly away from zero. Properness is used only for an actual bounded sequence of lower entries. The result applies to both ℝ and ℚ₂.

## Combined actual return and root-parameter selection

`BBEKPairedShear.exists_paired_shear_good_set` starts with an arbitrary measurable set S whose complement has mass below 1/20000, an invariant probability measure, and a measurable nonatomic leaf family normalized on its actual radius-r ball. It constructs a single threshold δ>0, a measurable Q⊆S, and a measurable G of mass greater than 99/100. For any two points of G and any small noncentral SL₂ displacement, it constructs normalization scales and a common return time. All four required returns lie in Q. At the selected time, every root bad set D of leaf mass at most 1/2 can be avoided by a root parameter of norm less than r whose genuine quadratic shear has norm greater than δ.

`BBEKLusinPairedShear.exists_compact_paired_shear` constructs S itself using the actual Lusin theorem and retains continuity of every countable leaf test. Its sequence version `exists_compact_paired_shear_sequence` uses exactly the same selected scales, times and root parameters in the nonzero-root subsequence theorem. It does not assume a nonzero root limit.

For the actual coordinate application use the `_at_total_time` variants of the three combined endpoints. The diagonal `diag(a,a⁻¹)` contracts the lower root. Thus the large parameter `a^(2n)*v` at time k is represented by the small parameter v in the normalized leaf field at total time k+n, which equals `shearTime` on the admissible range. The original first-time sampling endpoints remain valid abstract statements, but should not be used to identify this literal change of leaf coordinates.

The actual sequence endpoint has the precise remaining root-bad-set input

    ∀ i k n, T^[k+n](x_i) ∈ Q → η(T^[k+n](x_i))(D i k n) ≤ 1/2.

This inequality is not proved there for the literal bad sets of root returns. It requires identifying the conditional-kernel maximal estimate with normalized restrictions of the canonical leaf measure. Furthermore, the automatically chosen Q only contains the normalization, nonconcentration and Lusin conditions. To incorporate a leaf maximal good event one must intersect that event with an appropriately high-mass Lusin set and use the given-S version; it cannot be assumed that every point of the automatic Q already satisfies the leaf maximal estimate.

## Terminal compact-Lusin comparison

`BBEKLusinRootLimit.exists_equal_leaf_root_return` takes actual returning pairs p_i=g_i•q_i in one compact Lusin set, an actual group limit g_i→root(u), and convergence of every difference of leaf-test integrals to zero. It constructs z in that set with root(u)•z also in the set and proves equality of their full Radon leaf measures. The `of_eq` variant starts with literal equality for each returning pair. `root_limit_eq_zero_of_separation` combines this with the proved canonical root-separation property. The required test-difference or equality hypothesis is not inferred merely from closeness of the original pair.

`exists_compact_test_continuity_in_conull` chooses the Lusin compact set inside any specified measurable conull set. This retains pointwise regularity, strong canonical covariance, and root separation where needed; it does not silently promote almost-everywhere properties to every point of an unrelated compact set.

## Exact field transport on one conull set

`BBEKLeafFieldTransport.exists_invariant_conull_equal_field` proves, from the actual almost-everywhere formula f(Tq)=Φ(f(q)) and measure preservation, the existence of a measurable forward-invariant conull set on which equality of f is retained by every iterate. Its real and 2-adic lower-root instances use `BBEKCanonicalCovariance` for the same canonical family and radius. `equal_field_of_common_translation` then uses strong canonical covariance to retain literal equality after an arbitrary common root translation, when all four points belong to the one specified covariance set. No exceptional set depending on the translation parameter is substituted for that requirement.

## Remaining mathematical dependencies

The actual past subordinate chart codes, their decreasing `tailSigma` sequence, and the reverse conditional-kernel maximal bound have now been constructed in `BBEKLeafEntropySubordinate`, `BBEKLeafEntropySubordinateCharts`, `BBEKLeafEntropySubordinateTime`, and `BBEKReverseMaximal`. Thus neither the subordinate-code construction nor the uniform-in-length kernel maximal estimate is still an assumed input.

The remaining identification is between those literal conditional kernels and normalized restrictions of the canonical leaf measure, including the actual normalization radius and the plaque-to-ball comparison. This is needed to prove the concrete root bad-set bound displayed above at total time `k+n`. The kernel maximal estimate alone does not yet prove that leaf-measure inequality. Positive KS entropy must also be linked to the relevant one-root non-Dirac/nonatomic component so that the proved polynomial nonconcentration applies. These inputs must then be assembled with the actual returning pairs, canonical field transport, and compact-Lusin comparison; the individual endpoints do not by themselves discharge the EL core.

The specialized exceptional backend is already proved: `BBEKLocalExceptional` and `BBEKLowEntropyBackend` exclude the relevant local exceptional sets by the actual orbit-null argument. `BBEKNoncentralSequence` supplies the noncentral close-pair sequence from failure of that local exceptional condition. The exceptional alternative is therefore not an untouched external classification assumption in this compact-support application. The outstanding work is the entropy/leaf-mass identification and the complete application of the proved front and back endpoints.

The original source is the authors' [general low-entropy paper](https://people.math.ethz.ch/~einsiedl/low-entropy.pdf), especially Sections 5–7. The finite-prefix, coefficient, nonconcentration, and compact-limit estimates described here are proved directly in Lean.

## Verification

Each of the ten files in [the module inventory](BBEK-paired-return-modules-20260927.txt) was compiled separately under the pinned project environment. Their audited endpoints use only `propext`, `Classical.choice`, and `Quot.sound`; no new admission or axiom was introduced, and these modules do not import the EL core or final BBEK theorem.

Per-module raw `*.log` files are local working outputs and are not included in the public package. The authoritative public audit artifacts are [final-axioms.txt](final-axioms.txt) and [report.json](report.json), generated by the reproducible project check. The report records the checked source hashes, build status, counts, and the exact two retained admissions. Its timestamp identifies the audited snapshot; a successful build does not discharge the remaining EL admission.

