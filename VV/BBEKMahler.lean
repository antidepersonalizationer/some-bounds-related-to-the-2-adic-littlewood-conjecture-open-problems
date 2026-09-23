import VV.BBEKMahlerBounds
import VV.BBEKMahlerReal

/-! S-arithmetic Mahler compactness for the actual BBEK homogeneous space.
The proof combines dyadic strong approximation, two-dimensional real
lattice reduction, and the closedness of the literal no-short-vector set. -/

noncomputable section
open Matrix
open scoped MatrixGroups Topology

namespace VV.BBEKMahler
open BBEKDynamics BBEKQuotient BBEKDyadic BBEKOrbit BBEKShortVector
open BBEKMahlerPadic BBEKMahlerBridge BBEKMahlerBounds BBEKMahlerReal
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def representativeBound (δ : ℝ) : ℝ := 2 + 1 / ((min δ 1)^2/2)

theorem K_subset_bounded_representatives {δ : ℝ} (hδ : 0 < δ) :
    K δ ⊆ mk '' boundedRepresentatives (representativeBound δ) := by
  intro z hz
  obtain ⟨R,P,hP,he,hmin⟩ := K_has_normalized_representative hδ hz
  have hr : 0 < (min δ 1)^2/2 := by
    have hm : 0 < min δ 1 := lt_min hδ (by norm_num)
    positivity
  obtain ⟨A,hA⟩ := exists_bounded_integer_basis R hr hmin
  refine ⟨(R * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A,
      P * Matrix.SpecialLinearGroup.map (Int.castRingHom Q2) A), ?_, ?_⟩
  · exact ⟨hA, padicIntegral_mul hP (padicIntegral_map_int A)⟩
  · exact (integer_change_of_basis R P A).trans he

/-- Actual S-arithmetic Mahler compactness; there are no compactness,
bounded-representative, or arithmetic approximation hypotheses. -/
theorem compact_K {δ : ℝ} (hδ : 0 < δ) : IsCompact (K δ) :=
  (boundedRepresentatives_image_compact (representativeBound δ)).of_isClosed_subset
    (isClosed_K δ) (K_subset_bounded_representatives hδ)

/-- BBEK Proposition 5.1 has a genuinely compact trapping set. -/
theorem joint_orbit_closure_compact {ε u : ℝ} {v : ℤ_[2]} (hε : 0 < ε)
    (h : (u,v) ∈ P7AdicLimits.JointBadlyApproximable ε) :
    IsCompact (closure (coneOrbit (parameterPoint u (v:Q2)))) := by
  apply (compact_K (shortRadius_pos hε)).of_isClosed_subset isClosed_closure
  exact closure_minimal (proposition51 hε h) (isClosed_K _)

end VV.BBEKMahler
