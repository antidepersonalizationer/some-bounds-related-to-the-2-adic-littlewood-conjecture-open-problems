import VV.BBEKOneRootSupportEscape

/-!
# Almost-everywhere exclusion of full canonical leaf stabilizers

The finite escape cover excludes full stabilization at almost every base
point, rather than merely contradicting an everywhere-full family. Thus
one positive-measure nontriviality event and a bot/top dichotomy suffice
for the compact-support application. No ergodic promotion, full-diagonal
covariance of the leaf field, or measurability of the top event is used.
-/
noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped Topology ENNReal MatrixGroups
namespace VV.BBEKLeafStabilizerEscape
open BBEKDynamics BBEKQuotient BBEKOrbit BBEKDiagonal BBEKMautner
open BBEKLeafwiseStabilizer BBEKOneRootSupport BBEKOneRootCovariance BBEKOneRootUpper
open BBEKRootLeafKernel BBEKRootEscape BBEKOneRootSupportEscape

section General
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

/-- Full leaf stabilization is a null event under the finite escape
hypothesis. The event need not be assumed measurable. -/
theorem ae_stabilizer_ne_top_of_leaf_escape
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    (η : X → Measure U) (root : U → G) (hroot : Continuous root)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    (hsupport : ∀ S : Set X, IsClosed S → μ S = 1 →
      ∀ᵐ q ∂μ, ∀ᵐ u ∂η q, root u • q ∈ S)
    {K : Set X} (hK : IsCompact K) (hmass : μ K = 1)
    (hescape : ∀ q ∈ K, ∃ d : A, ∃ u : U, (d : G) • (root u • q) ∉ K) :
    ∀ᵐ q ∂μ, translationStabilizer (η q) ≠ ⊤ := by
  let O : A × U → Set X := fun p => (fun q : X => (p.1 : G) • (root p.2 • q)) ⁻¹' Kᶜ
  have hcover : K ⊆ ⋃ p, O p := by
    intro q hq
    obtain ⟨d,u,hu⟩ := hescape q hq
    exact mem_iUnion.mpr ⟨(d,u),hu⟩
  have hopen : ∀ p, IsOpen (O p) := fun p =>
    hK.isClosed.isOpen_compl.preimage
      ((continuous_const_smul (p.1 : G)).comp (continuous_const_smul (root p.2)))
  obtain ⟨T,hT⟩ := hK.elim_finite_subcover O hopen hcover
  have hexclude (p : A × U) :
      ∀ᵐ q ∂μ, translationStabilizer (η q) = ⊤ → q ∉ O p := by
    let S : Set X := (fun q : X => (p.1 : G) • q) ⁻¹' K
    have hS : IsClosed S := hK.isClosed.preimage (continuous_const_smul _)
    have hmS : μ S = 1 := by
      change μ ((fun q : X => p.1 • q) ⁻¹' K) = 1
      rw [measure_preimage_smul μ p.1 K,hmass]
    filter_upwards [hpos,hsupport S hS hmS] with q hqpos hqs hqtop
    change ¬ ¬ ((p.1 : G) • (root p.2 • q) ∈ K)
    exact not_not.mpr (orbit_subset_of_supported root hroot (η q) q hS hqpos hqtop hqs p.2)
  have hall : ∀ᵐ q ∂μ, ∀ p ∈ T,
      translationStabilizer (η q) = ⊤ → q ∉ O p :=
    (eventually_all_finset T).mpr (fun p _ => hexclude p)
  have hmem : ∀ᵐ q ∂μ, q ∈ K := by
    rw [ae_iff]
    change μ Kᶜ = 0
    rw [measure_compl hK.isClosed.measurableSet (measure_ne_top _ _),
      measure_univ,hmass,tsub_self]
  filter_upwards [hmem,hall] with q hq hqall hqtop
  obtain ⟨p,hp,ho⟩ := mem_iUnion₂.mp (hT hq)
  exact hqall p hp hqtop ho

/-- A separately proved bot/top dichotomy leaves only the trivial subgroup.
No invariance of the top event is required. -/
theorem ae_stabilizer_eq_bot_of_ne_top
    (μ : Measure X) (η : X → Measure U)
    (hne : ∀ᵐ q ∂μ, translationStabilizer (η q) ≠ ⊤)
    (hdichotomy : ∀ᵐ q ∂μ,
      translationStabilizer (η q) = ⊥ ∨ translationStabilizer (η q) = ⊤) :
    ∀ᵐ q ∂μ, translationStabilizer (η q) = ⊥ := by
  filter_upwards [hne,hdichotomy] with q hq hd
  exact hd.resolve_right hq
end General
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- For real lower canonical leaves, top stabilization already contradicts
Mahler compact support, without an ambient reconstruction lemma. -/
theorem ae_real_lower_stabilizer_ne_top
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure ℝ)
    (hcanonical : IsConstructedRootFamily realSplit μ t r η)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    : ∀ᵐ q ∂μ, translationStabilizer (η q) ≠ ⊤ := by
  apply ae_stabilizer_ne_top_of_leaf_escape μ η (fun u => x u 0)
    (continuous_x.comp (continuous_id.prodMk continuous_const)) hpos
    (fun S hS hmS => canonical_real_lower_supported μ hS.measurableSet hmS hr η hcanonical)
    (BBEKMahler.compact_K hδ) hmass
  intro q _
  obtain ⟨a,ha,u,hu⟩ := exists_real_lower_diagonal_not_mem_K q hδ
  have hd : (diagonal a ha, (1 : SL(2,Q2))) ∈ A :=
    ⟨⟨a,ha,rfl⟩,(diagonalGroup Q2).one_mem⟩
  refine ⟨⟨(diagonal a ha,1),hd⟩,u,?_⟩
  simpa only [← mul_smul,x,Prod.mk_mul_mk,lower_zero,mul_one] using hu

theorem ae_padic_lower_stabilizer_ne_top
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure Q2)
    (hcanonical : IsConstructedRootFamily padicSplit μ t r η)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    : ∀ᵐ q ∂μ, translationStabilizer (η q) ≠ ⊤ := by
  apply ae_stabilizer_ne_top_of_leaf_escape μ η (fun u => x 0 u)
    (continuous_x.comp (continuous_const.prodMk continuous_id)) hpos
    (fun S hS hmS => canonical_padic_lower_supported μ hS.measurableSet hmS hr η hcanonical)
    (BBEKMahler.compact_K hδ) hmass
  intro q _
  obtain ⟨a,ha,u,hu⟩ := exists_padic_lower_diagonal_not_mem_K q hδ
  have hd : ((1 : SL(2,ℝ)),diagonal a ha) ∈ A :=
    ⟨(diagonalGroup ℝ).one_mem,⟨a,ha,rfl⟩⟩
  refine ⟨⟨(1,diagonal a ha),hd⟩,u,?_⟩
  simpa only [← mul_smul,x,Prod.mk_mul_mk,lower_zero,mul_one] using hu

theorem ae_real_upper_stabilizer_ne_top
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure ℝ)
    (hcanonical : IsConstructedUpperRootFamily realSplit μ t r η)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    : ∀ᵐ q ∂μ, translationStabilizer (η q) ≠ ⊤ := by
  have hc : Continuous (fun u : ℝ => upperPoint u 0) := by
    have hc₀ : Continuous (fun u : ℝ => transposeG (x u 0)) :=
      continuous_transposeG.comp (continuous_x.comp (continuous_id.prodMk continuous_const))
    simpa only [transposeG_x] using hc₀
  apply ae_stabilizer_ne_top_of_leaf_escape μ η (fun u => upperPoint u 0) hc hpos
    (fun S hS hmS => canonical_real_upper_supported μ hS.measurableSet hmS hr η hcanonical)
    (BBEKMahler.compact_K hδ) hmass
  intro q _
  obtain ⟨a,ha,u,hu⟩ := exists_real_upper_diagonal_not_mem_K q hδ
  have hd : (diagonal a ha, (1 : SL(2,Q2))) ∈ A :=
    ⟨⟨a,ha,rfl⟩,(diagonalGroup Q2).one_mem⟩
  refine ⟨⟨(diagonal a ha,1),hd⟩,u,?_⟩
  simpa only [← mul_smul,upperPoint,Prod.mk_mul_mk,BBEKFiniteQuotients.upper_zero,mul_one] using hu

theorem ae_padic_upper_stabilizer_ne_top
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure Q2)
    (hcanonical : IsConstructedUpperRootFamily padicSplit μ t r η)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    : ∀ᵐ q ∂μ, translationStabilizer (η q) ≠ ⊤ := by
  have hc : Continuous (fun u : Q2 => upperPoint 0 u) := by
    have hc₀ : Continuous (fun u : Q2 => transposeG (x 0 u)) :=
      continuous_transposeG.comp (continuous_x.comp (continuous_const.prodMk continuous_id))
    simpa only [transposeG_x] using hc₀
  apply ae_stabilizer_ne_top_of_leaf_escape μ η (fun u => upperPoint 0 u) hc hpos
    (fun S hS hmS => canonical_padic_upper_supported μ hS.measurableSet hmS hr η hcanonical)
    (BBEKMahler.compact_K hδ) hmass
  intro q _
  obtain ⟨a,ha,u,hu⟩ := exists_padic_upper_diagonal_not_mem_K q hδ
  have hd : ((1 : SL(2,ℝ)),diagonal a ha) ∈ A :=
    ⟨(diagonalGroup ℝ).one_mem,⟨a,ha,rfl⟩⟩
  refine ⟨⟨(1,diagonal a ha),hd⟩,u,?_⟩
  simpa only [← mul_smul,upperPoint,Prod.mk_mul_mk,BBEKFiniteQuotients.upper_zero,mul_one] using hu

end VV.BBEKLeafStabilizerEscape

