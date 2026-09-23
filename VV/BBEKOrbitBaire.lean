import VV.BBEKNormalizerExclusion
import VV.BBEKGaussTransition

/-! A genuine orbit-to-subgroup bridge: a closed periodic orbit carrying an
invariant measure forces an open intersection with the diagonal group. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure MulAction Filter
open scoped Topology
namespace VV.BBEKOrbitBaire

section CosetCover
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Baire category removes the countable stabilizer ambiguity from a coset
cover: the intersection of the two actual subgroups is open in H. -/
theorem open_comap_of_countable_coset_cover (H L : Subgroup G) [BaireSpace H]
    (hL : IsClosed (L : Set G)) {ι : Type*} [Countable ι] (r : ι → G)
    (hcover : ∀ a : H, ∃ i, a.val*r i ∈ L) :
    IsOpen (L.comap H.subtype : Set H) := by
  let F : ι → Set H := fun i => {a | a.val*r i ∈ L}
  have hF (i : ι) : IsClosed (F i) :=
    hL.preimage (continuous_subtype_val.mul continuous_const)
  have hc : (⋃ i, F i)=univ := by
    apply eq_univ_of_forall
    intro a
    exact mem_iUnion.mpr (hcover a)
  obtain ⟨i,a,ha⟩ := nonempty_interior_of_iUnion_of_closed hF hc
  have hai : a.val*r i ∈ L := show a ∈ F i from interior_subset ha
  have he : (fun b : H => b*a) ⁻¹' F i = (L.comap H.subtype : Set H) := by
    ext b
    change (b.val*a.val)*r i ∈ L ↔ b.val ∈ L
    constructor
    · intro hb
      have hh := L.mul_mem hb (L.inv_mem hai)
      simpa only [mul_assoc,mul_inv_rev,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh
    · intro hb
      simpa only [mul_assoc] using L.mul_mem hb hai
  apply (L.comap H.subtype).isOpen_of_mem_nhds (g:=1)
  rw [← he]
  exact (continuous_id.mul continuous_const).continuousAt
    (by simpa only [id_eq,one_mul] using mem_interior_iff_mem_nhds.mp ha)
end CosetCover

open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKInvariantSupport BBEKPeriodicOrbit

local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- On the literal S-arithmetic quotient, no containment A ≤ L is presumed.
It follows locally from invariance, closedness of the periodic orbit, and
the countability of the arithmetic stabilizer. -/
theorem diagonal_intersection_isOpen_of_closed_full_orbit
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    (L : Subgroup G) (hL : IsClosed (L : Set G))
    (q : X) (hq : IsClosed (orbit L q)) (hμq : μ (orbit L q)=1) :
    IsOpen (L.comap A.subtype : Set A) := by
  obtain ⟨x,hx⟩ := positiveSupport_nonempty μ
  have hxL := positiveSupport_subset_of_closed_full μ hq hμq hx
  have hox : orbit L x = orbit L q := orbit_eq_iff.mpr hxL
  have hAx (a : A) : a • x ∈ orbit L x := by
    rw [hox]
    exact positiveSupport_subset_of_closed_full μ hq hμq (smul_positiveSupport μ a hx)
  obtain ⟨g,hg⟩ : ∃ g : G, mk g=x := Quotient.exists_rep x
  apply open_comap_of_countable_coset_cover A L hL
    (fun γ : Gamma => g*(γ.val)⁻¹*g⁻¹)
  intro a
  obtain ⟨l,hl⟩ := hAx a
  have he : mk (l.val*g)=mk (a.val*g) := by
    simpa only [← smul_mk,hg,subgroup_smul_def] using hl
  let γ : Gamma := ⟨(l.val*g)⁻¹*(a.val*g),(mk_eq_iff _ _).mp he⟩
  refine ⟨γ,?_⟩
  have hm : a.val*(g*γ.val⁻¹*g⁻¹)=l.val := by dsimp [γ]; group
  rw [hm]
  exact l.property

end VV.BBEKOrbitBaire

