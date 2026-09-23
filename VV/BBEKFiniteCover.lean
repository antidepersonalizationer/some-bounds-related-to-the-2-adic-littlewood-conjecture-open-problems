import VV.BBEKFiniteBowen

noncomputable section
open Set Metric
open scoped Topology
namespace VV.BBEKFiniteBowen

/-- A fixed compact target supplies a uniform finite cover of every image,
with centers chosen in the source subset itself. -/
theorem finite_cover_of_map_into_compact {P Z : Type*} [PseudoMetricSpace Z]
    {K : Set Z} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ (S : Set P) (f : P → Z), Set.MapsTo f S K →
      ∃ s : Finset P, (s : Set P) ⊆ S ∧ s.card ≤ M ∧
        ∀ p ∈ S, ∃ q ∈ s, dist (f p) (f q) < δ := by
  classical
  obtain ⟨T,hTK,hT,hcover⟩ := hK.finite_cover_balls (half_pos hδ)
  letI : Fintype T := hT.fintype
  refine ⟨Fintype.card T,?_⟩
  intro S f hf
  by_cases hS : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hS
    have hex (t : T) : ∃ p ∈ S,
        (∃ a ∈ S, dist (f a) t < δ/2) → dist (f p) t < δ/2 := by
      by_cases ht : ∃ a ∈ S, dist (f a) t < δ/2
      · obtain ⟨p,hp,hclose⟩ := ht
        exact ⟨p,hp,fun _ => hclose⟩
      · exact ⟨p₀,hp₀,fun h => False.elim (ht h)⟩
    choose rep hrep hclose using hex
    let s := Finset.univ.image rep
    refine ⟨s,?_,(Finset.card_image_le.trans (by simp)),?_⟩
    · intro q hq
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hq
      exact hrep t
    · intro p hp
      obtain ⟨t,htT,hpt⟩ := mem_iUnion₂.mp (hcover (hf hp))
      let ti : T := ⟨t,htT⟩
      have hrt := hclose ti ⟨p,hp,hpt⟩
      refine ⟨rep ti,Finset.mem_image.mpr ⟨ti,Finset.mem_univ _,rfl⟩,?_⟩
      calc
        dist (f p) (f (rep ti)) ≤ dist (f p) t + dist t (f (rep ti)) := dist_triangle _ _ _
        _ < δ/2 + δ/2 := add_lt_add hpt (by simpa only [dist_comm] using hrt)
        _ = δ := by ring
  · refine ⟨∅,by simp,by simp,?_⟩
    intro p hp
    exact False.elim (hS ⟨p,hp⟩)

end VV.BBEKFiniteBowen
