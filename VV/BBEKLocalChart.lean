import VV.BBEKDiscrete
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homeomorph.Lemmas

/-! Pointwise local quotient charts for the actual arithmetic quotient.
No compact-uniform radius or entropy statement is assumed or concluded. -/

noncomputable section
open Set Metric Topology
open scoped Topology

namespace VV.BBEKLocalChart
open BBEKDynamics BBEKQuotient BBEKDiscrete

private theorem exists_open_injOn_quotient {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (Γ : Subgroup H) (V₀ : Set H) (hV₀ : IsOpen V₀)
    (h1 : (1 : H) ∈ V₀) (hisolate : ∀ a ∈ Γ, a ∈ V₀ → a = 1) (g : H) :
    ∃ U : Set H, IsOpen U ∧ g ∈ U ∧ Set.InjOn (QuotientGroup.mk : H → H ⧸ Γ) U := by
  let D : Set (H × H) := {p | p.1⁻¹ * p.2 ∈ V₀}
  have hcont : Continuous (fun p : H × H => p.1⁻¹ * p.2) :=
    continuous_fst.inv.mul continuous_snd
  have hD : IsOpen D := hV₀.preimage hcont
  have hgg : (g,g) ∈ D := by change g⁻¹ * g ∈ V₀; simpa using h1
  obtain ⟨V,W,hV,hW,hgV,hgW,hVW⟩ := isOpen_prod_iff.mp hD g g hgg
  refine ⟨V ∩ W, hV.inter hW, ⟨hgV,hgW⟩, ?_⟩
  intro a ha b hb hab
  have hgamma : a⁻¹ * b ∈ Γ := QuotientGroup.eq.mp hab
  have hsmall : a⁻¹ * b ∈ V₀ := hVW (show (a,b) ∈ V ×ˢ W from ⟨ha.1,hb.2⟩)
  have he : a⁻¹ * b = 1 := hisolate _ hgamma hsmall
  exact inv_mul_eq_one.mp he

/-- Around each concrete group element, quotient representatives are unique
in a sufficiently small open neighborhood. -/
theorem exists_open_injOn_mk (g : G) :
    ∃ U : Set G, IsOpen U ∧ g ∈ U ∧ Set.InjOn mk U := by
  exact exists_open_injOn_quotient Gamma (ball 1 1) isOpen_ball (by simp)
    (fun _ ha hs => gamma_eq_one_of_dist_lt_one ha hs) g

theorem isOpenMap_mk : IsOpenMap (mk : G → X) :=
  QuotientGroup.isOpenQuotientMap_mk.isOpenMap

/-- On every open set where the quotient map is injective, its restriction
is an open embedding into the quotient. -/
theorem isOpenEmbedding_restrict {U : Set G} (hU : IsOpen U) (hi : Set.InjOn mk U) :
    IsOpenEmbedding (U.restrict mk) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_mk.comp continuous_subtype_val
  · exact Set.injOn_iff_injective.mp hi
  · exact isOpenMap_mk.restrict hU

theorem exists_open_embedding_mk (g : G) :
    ∃ U : Set G, IsOpen U ∧ g ∈ U ∧ IsOpenEmbedding (U.restrict mk) := by
  obtain ⟨U,hU,hg,hi⟩ := exists_open_injOn_mk g
  exact ⟨U,hU,hg,isOpenEmbedding_restrict hU hi⟩

/-- A named actual homeomorphism onto the open quotient image. -/
def chartHomeomorph {U : Set G} (hU : IsOpen U) (hi : Set.InjOn mk U) :
    U ≃ₜ (mk '' U) :=
  (isOpenEmbedding_restrict hU hi).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by ext q; simp [Set.range_restrict]))

@[simp] theorem chartHomeomorph_apply {U : Set G} (hU : IsOpen U)
    (hi : Set.InjOn mk U) (g : U) :
    ((chartHomeomorph hU hi g : mk '' U) : X) = mk g := rfl

theorem chart_image_isOpen {U : Set G} (hU : IsOpen U) : IsOpen (mk '' U) :=
  isOpenMap_mk U hU

/-- The quotient map is locally a homeomorphism at each source point.
This is a pointwise statement, with no uniform size specified. -/
theorem isLocalHomeomorph_mk : IsLocalHomeomorph (mk : G → X) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro g
  obtain ⟨U,hU,hg,hEmb⟩ := exists_open_embedding_mk g
  exact ⟨U,hU.mem_nhds hg,hEmb⟩

end VV.BBEKLocalChart
