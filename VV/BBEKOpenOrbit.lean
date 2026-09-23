import VV.BBEKPeriodicAmbient
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! Closed orbits of open subgroups, with the actual orbit topology. -/
noncomputable section
open Set MulAction
open scoped Topology
namespace VV.BBEKOpenOrbit

section Transitive
variable {H Y : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SigmaCompactSpace H] [TopologicalSpace Y] [T2Space Y] [BaireSpace Y]
  [MulAction H Y] [ContinuousSMul H Y] [MulAction.IsPretransitive H Y]

theorem isOpen_orbit_of_open_subgroup (N : Subgroup H) (hN : IsOpen (N : Set H))
    (y : Y) : IsOpen (orbit N y) := by
  have he : orbit N y = (fun h : H => h • y) '' (N : Set H) := by
    ext z
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a.val,a.property,ha⟩
    · rintro ⟨a,ha,haz⟩
      exact ⟨⟨a,ha⟩,haz⟩
  rw [he]
  exact isOpenMap_smul_of_sigmaCompact y _ hN

theorem isClosed_orbit_of_open_subgroup (N : Subgroup H) (hN : IsOpen (N : Set H))
    (y : Y) : IsClosed (orbit N y) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  apply Filter.mem_of_superset
    ((isOpen_orbit_of_open_subgroup N hN z).mem_nhds (mem_orbit_self z))
  intro w hw
  intro hwy
  have he : orbit N z = orbit N w := orbit_eq_iff.mpr (mem_orbit_symm.mp hw)
  exact hz (orbit_eq_iff.mp (he.trans (orbit_eq_iff.mpr hwy)))
end Transitive

section ClosedOrbit
variable {H Y : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SigmaCompactSpace H] [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MulAction H Y] [ContinuousSMul H Y]

/-- An open subgroup's orbits inside a closed orbit are closed in the ambient
space. No closedness of the smaller orbit is assumed. -/
theorem closed_subgroup_orbit (N : Subgroup H) (hN : IsOpen (N : Set H))
    (y : Y) (hy : IsClosed (orbit H y)) : IsClosed (orbit N y) := by
  let O := orbit H y
  let y₀ : O := ⟨y,mem_orbit_self y⟩
  letI : LocallyCompactSpace O := hy.locallyCompactSpace
  letI : ContinuousSMul H O := ⟨
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  have hc := isClosed_orbit_of_open_subgroup N hN y₀
  have he : ((↑) : O → Y) '' orbit N y₀ = orbit N y := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact mem_subgroup_orbit_iff.mp hw
    · intro hz
      let z₀ : O := ⟨z,orbit_subgroup_subset N y hz⟩
      exact ⟨z₀,mem_subgroup_orbit_iff.mpr hz,rfl⟩
  rw [← he]
  exact hy.isClosedEmbedding_subtypeVal.isClosedMap _ hc
end ClosedOrbit

end VV.BBEKOpenOrbit
