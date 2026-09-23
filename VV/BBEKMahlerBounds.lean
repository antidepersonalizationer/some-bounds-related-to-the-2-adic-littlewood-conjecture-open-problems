import VV.BBEKMahlerBridge

/-! Compact sets of actual bounded representatives for the S-arithmetic quotient. -/

noncomputable section
open Matrix
open scoped MatrixGroups Topology

namespace VV.BBEKMahlerBounds
open BBEKDynamics BBEKQuotient BBEKDyadic BBEKOrbit BBEKMahlerPadic BBEKMahlerBridge
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def realBound (C : ℝ) : Set SL(2,ℝ) := {R | ∀ i j, |R i j| ≤ C}

theorem realBound_compact (C : ℝ) : IsCompact (realBound C) := by
  have hc : IsCompact {M : Matrix (Fin 2) (Fin 2) ℝ | ∀ i j, |M i j| ≤ C} := by
    have hball : IsCompact {a : ℝ | |a| ≤ C} := by
      simpa only [Metric.closedBall, dist_zero_right, Real.norm_eq_abs]
        using isCompact_closedBall (0 : ℝ) C
    exact isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hball
  have hd : IsClosed {M : Matrix (Fin 2) (Fin 2) ℝ | M.det = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  exact hd.isClosedEmbedding_subtypeVal.isCompact_preimage hc

def boundedRepresentatives (C : ℝ) : Set G := realBound C ×ˢ padicIntegral

theorem boundedRepresentatives_compact (C : ℝ) : IsCompact (boundedRepresentatives C) :=
  (realBound_compact C).prod padicIntegral_compact

theorem boundedRepresentatives_image_compact (C : ℝ) :
    IsCompact (mk '' boundedRepresentatives C) :=
  (boundedRepresentatives_compact C).image continuous_mk

/-- Integer changes of basis are genuinely in the diagonal dyadic group. -/
theorem integer_change_of_basis (R : SL(2,ℝ)) (P : SL(2,Q2)) (A : SL(2,ℤ)) :
    mk (R * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A,
      P * Matrix.SpecialLinearGroup.map (Int.castRingHom Q2) A) = mk (R,P) := by
  convert mk_right_gamma (R,P)
    (Matrix.SpecialLinearGroup.map (Int.castRingHom dyadic) A) using 1

theorem K_mono {δ ε : ℝ} (h : ε ≤ δ) : K δ ⊆ K ε := by
  intro z hz w hw hne
  exact h.trans (hz w hw hne)

/-- Every actual no-short-vector class has an integral 2-adic representative
whose real integer lattice has a uniform positive minimum. -/
theorem K_has_normalized_representative {δ : ℝ} (hδ : 0 < δ)
    {z : X} (hz : z ∈ K δ) :
    ∃ R : SL(2,ℝ), ∃ P : SL(2,Q2), P ∈ padicIntegral ∧ mk (R,P) = z ∧
      ∀ v : Fin 2 → ℤ, v ≠ 0 → (min δ 1)^2/2 ≤ ‖R.val *ᵥ (fun i => (v i:ℝ))‖ := by
  obtain ⟨R,P,hP,he⟩ := quotient_has_padic_integral_representative z
  refine ⟨R,P,hP,he,?_⟩
  intro v hv
  apply real_integer_minimum_of_mem_K (lt_min hδ (by norm_num)) (min_le_right _ _)
    R P hP _ v hv
  rw [he]
  exact K_mono (min_le_left _ _) hz

end VV.BBEKMahlerBounds
