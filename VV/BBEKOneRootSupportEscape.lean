import VV.BBEKOneRootSupport
import VV.BBEKRootEscape

/-! A full translation stabilizer of a genuine canonical root leaf is incompatible
with a full-diagonal-invariant probability concentrated on a Mahler compact.
The proof uses support transfer and a finite open escape cover; it does not
assume or reconstruct invariance of the ambient measure under the root. -/
noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped Topology ENNReal MatrixGroups
namespace VV.BBEKOneRootSupportEscape
open BBEKDynamics BBEKQuotient BBEKOrbit BBEKDiagonal BBEKMautner
open BBEKLeafwiseStabilizer BBEKOneRootSupport BBEKOneRootCovariance BBEKOneRootUpper
open BBEKRootLeafKernel BBEKRootEscape

section General
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

/-- Positive mass at every zero neighborhood and all translation symmetries
force any closed conull set to contain every point. -/
theorem closed_conull_eq_univ (η : Measure U)
    (hpos : ∀ ε : ℝ, 0 < ε → 0 < η (ball 0 ε))
    (htop : translationStabilizer η = ⊤)
    {S : Set U} (hS : IsClosed S) (hηS : ∀ᵐ u ∂η, u ∈ S) : S = univ := by
  apply eq_univ_of_forall
  intro u
  by_contra hu
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hS.isOpen_compl.mem_nhds hu)
  have he : translate u η = η := by
    apply (mem_translationStabilizer η u).mp
    rw [htop]
    exact AddSubgroup.mem_top u
  have hb : η (ball u ε) = η (ball 0 ε) := by
    calc
      η (ball u ε) = translate u η (ball u ε) := congrArg (fun ν : Measure U => ν (ball u ε)) he.symm
      _ = η ((fun v : U => u+v) ⁻¹' ball u ε) := translate_apply u η isOpen_ball.measurableSet
      _ = η (ball 0 ε) := by
        congr 1
        ext v
        simp only [mem_preimage,mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero]
  have hz : η Sᶜ = 0 := by simpa only [ae_iff] using hηS
  have : η (ball u ε) = 0 := measure_mono_null hball hz
  rw [hb] at this
  exact (hpos ε hε).ne' this

/-- Actual orbit containment from an almost-everywhere leaf support statement. -/
theorem orbit_subset_of_supported (root : U → G) (hroot : Continuous root)
    (η : Measure U) (q : X) {K : Set X} (hK : IsClosed K)
    (hpos : ∀ ε : ℝ, 0 < ε → 0 < η (ball 0 ε))
    (htop : translationStabilizer η = ⊤)
    (hsupport : ∀ᵐ u ∂η, root u • q ∈ K) : ∀ u, root u • q ∈ K := by
  have he := closed_conull_eq_univ η hpos htop
    (hK.preimage (hroot.smul continuous_const)) hsupport
  intro u
  change u ∈ (fun v => root v • q) ⁻¹' K
  rw [he]
  exact mem_univ u

/-- A finite escape cover converts canonical leaf support into a contradiction.
The support input here is discharged by the four actual canonical-family
theorems below; no ambient root-invariance input is used. -/
theorem no_supported_of_leaf_escape
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    (η : X → Measure U) (root : U → G) (hroot : Continuous root)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    (htop : ∀ᵐ q ∂μ, translationStabilizer (η q) = ⊤)
    (hsupport : ∀ S : Set X, IsClosed S → μ S = 1 →
      ∀ᵐ q ∂μ, ∀ᵐ u ∂η q, root u • q ∈ S)
    {K : Set X} (hK : IsCompact K) (hmass : μ K = 1)
    (hescape : ∀ q ∈ K, ∃ d : A, ∃ u : U, (d : G) • (root u • q) ∉ K) : False := by
  let O : A × U → Set X := fun p => (fun q : X => (p.1 : G) • (root p.2 • q)) ⁻¹' Kᶜ
  have hcover : K ⊆ ⋃ p, O p := by
    intro q hq
    obtain ⟨d,u,hu⟩ := hescape q hq
    exact mem_iUnion.mpr ⟨(d,u),hu⟩
  have hopen : ∀ p, IsOpen (O p) := fun p =>
    hK.isClosed.isOpen_compl.preimage
      ((continuous_const_smul (p.1 : G)).comp (continuous_const_smul (root p.2)))
  obtain ⟨T,hT⟩ := hK.elim_finite_subcover O hopen hcover
  have hnull : ∀ p : A × U, μ (O p) = 0 := by
    intro p
    let S : Set X := (fun q : X => (p.1 : G) • q) ⁻¹' K
    have hS : IsClosed S := hK.isClosed.preimage (continuous_const_smul _)
    have hmS : μ S = 1 := by
      change μ ((fun q : X => p.1 • q) ⁻¹' K) = 1
      rw [measure_preimage_smul μ p.1 K,hmass]
    have hh := hsupport S hS hmS
    have ha : ∀ᵐ q ∂μ, q ∉ O p := by
      filter_upwards [hpos,htop,hh] with q hqpos hqtop hqs
      change ¬ ¬ ((p.1 : G) • (root p.2 • q) ∈ K)
      exact not_not.mpr (orbit_subset_of_supported root hroot (η q) q hS hqpos hqtop hqs p.2)
    simpa only [ae_iff,not_not] using ha
  have hz : μ (⋃ p ∈ (T : Set (A × U)), O p) = 0 :=
    (measure_biUnion_null_iff T.countable_toSet).mpr (fun p _ => hnull p)
  exact zero_ne_one ((measure_mono_null hT hz).symm.trans hmass)
end General

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- For real lower canonical leaves, top stabilization already contradicts
Mahler compact support, without an ambient reconstruction lemma. -/
theorem no_real_lower_top
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure ℝ)
    (hcanonical : IsConstructedRootFamily realSplit μ t r η)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    (htop : ∀ᵐ q ∂μ, translationStabilizer (η q) = ⊤) : False := by
  apply no_supported_of_leaf_escape μ η (fun u => x u 0)
    (continuous_x.comp (continuous_id.prodMk continuous_const)) hpos htop
    (fun S hS hmS => canonical_real_lower_supported μ hS.measurableSet hmS hr η hcanonical)
    (BBEKMahler.compact_K hδ) hmass
  intro q _
  obtain ⟨a,ha,u,hu⟩ := exists_real_lower_diagonal_not_mem_K q hδ
  have hd : (diagonal a ha, (1 : SL(2,Q2))) ∈ A :=
    ⟨⟨a,ha,rfl⟩,(diagonalGroup Q2).one_mem⟩
  refine ⟨⟨(diagonal a ha,1),hd⟩,u,?_⟩
  simpa only [← mul_smul,x,Prod.mk_mul_mk,lower_zero,mul_one] using hu

theorem no_padic_lower_top
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure Q2)
    (hcanonical : IsConstructedRootFamily padicSplit μ t r η)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    (htop : ∀ᵐ q ∂μ, translationStabilizer (η q) = ⊤) : False := by
  apply no_supported_of_leaf_escape μ η (fun u => x 0 u)
    (continuous_x.comp (continuous_const.prodMk continuous_id)) hpos htop
    (fun S hS hmS => canonical_padic_lower_supported μ hS.measurableSet hmS hr η hcanonical)
    (BBEKMahler.compact_K hδ) hmass
  intro q _
  obtain ⟨a,ha,u,hu⟩ := exists_padic_lower_diagonal_not_mem_K q hδ
  have hd : ((1 : SL(2,ℝ)),diagonal a ha) ∈ A :=
    ⟨(diagonalGroup ℝ).one_mem,⟨a,ha,rfl⟩⟩
  refine ⟨⟨(1,diagonal a ha),hd⟩,u,?_⟩
  simpa only [← mul_smul,x,Prod.mk_mul_mk,lower_zero,mul_one] using hu

theorem no_real_upper_top
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure ℝ)
    (hcanonical : IsConstructedUpperRootFamily realSplit μ t r η)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    (htop : ∀ᵐ q ∂μ, translationStabilizer (η q) = ⊤) : False := by
  have hc : Continuous (fun u : ℝ => upperPoint u 0) := by
    have hc₀ : Continuous (fun u : ℝ => transposeG (x u 0)) :=
      continuous_transposeG.comp (continuous_x.comp (continuous_id.prodMk continuous_const))
    simpa only [transposeG_x] using hc₀
  apply no_supported_of_leaf_escape μ η (fun u => upperPoint u 0) hc hpos htop
    (fun S hS hmS => canonical_real_upper_supported μ hS.measurableSet hmS hr η hcanonical)
    (BBEKMahler.compact_K hδ) hmass
  intro q _
  obtain ⟨a,ha,u,hu⟩ := exists_real_upper_diagonal_not_mem_K q hδ
  have hd : (diagonal a ha, (1 : SL(2,Q2))) ∈ A :=
    ⟨⟨a,ha,rfl⟩,(diagonalGroup Q2).one_mem⟩
  refine ⟨⟨(diagonal a ha,1),hd⟩,u,?_⟩
  simpa only [← mul_smul,upperPoint,Prod.mk_mul_mk,BBEKFiniteQuotients.upper_zero,mul_one] using hu

theorem no_padic_upper_top
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure Q2)
    (hcanonical : IsConstructedUpperRootFamily padicSplit μ t r η)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    (htop : ∀ᵐ q ∂μ, translationStabilizer (η q) = ⊤) : False := by
  have hc : Continuous (fun u : Q2 => upperPoint 0 u) := by
    have hc₀ : Continuous (fun u : Q2 => transposeG (x 0 u)) :=
      continuous_transposeG.comp (continuous_x.comp (continuous_const.prodMk continuous_id))
    simpa only [transposeG_x] using hc₀
  apply no_supported_of_leaf_escape μ η (fun u => upperPoint 0 u) hc hpos htop
    (fun S hS hmS => canonical_padic_upper_supported μ hS.measurableSet hmS hr η hcanonical)
    (BBEKMahler.compact_K hδ) hmass
  intro q _
  obtain ⟨a,ha,u,hu⟩ := exists_padic_upper_diagonal_not_mem_K q hδ
  have hd : ((1 : SL(2,ℝ)),diagonal a ha) ∈ A :=
    ⟨(diagonalGroup ℝ).one_mem,⟨a,ha,rfl⟩⟩
  refine ⟨⟨(1,diagonal a ha),hd⟩,u,?_⟩
  simpa only [← mul_smul,upperPoint,Prod.mk_mul_mk,BBEKFiniteQuotients.upper_zero,mul_one] using hu

end VV.BBEKOneRootSupportEscape

