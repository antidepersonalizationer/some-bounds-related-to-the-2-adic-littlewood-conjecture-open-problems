import VV.BBEKDiagonal
import VV.BBEKOrbit

/-! The compact averaging group preserves the actual no-short-vector sets.
The real sign and the 2-adic unit coefficients preserve every vector norm. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups Topology

namespace VV.BBEKCompactPreservation
open BBEKDynamics BBEKQuotient BBEKLattice BBEKDiagonal

theorem unitDiagonal_mulVec_norm {F : Type*} [NormedField F]
    {a : SL(2,F)} (ha : a ∈ unitDiagonal F) (v : Fin 2 → F) :
    ‖a.val *ᵥ v‖ = ‖v‖ := by
  obtain ⟨b,hb,hn,rfl⟩ := ha
  have hi (i : Fin 2) : ‖(BBEKDynamics.diagonal b hb).val.mulVec v i‖ = ‖v i‖ := by
    fin_cases i <;>
      simp [BBEKDynamics.diagonal,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
        norm_mul,norm_inv,hn]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    rw [hi]
    exact norm_le_pi_norm v i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [← hi]
    exact norm_le_pi_norm _ i

theorem compact_vectorImage_norm (k : K) (M : G) (r : BBEKOrbit.Coefficients) :
    ‖vectorImage dyadicToReal dyadicToQ2 ((k:G)*M) r‖ =
      ‖vectorImage dyadicToReal dyadicToQ2 M r‖ := by
  change max ‖((k:G).1.val*M.1.val) *ᵥ (dyadicToReal ∘ r)‖
    ‖((k:G).2.val*M.2.val) *ᵥ (dyadicToQ2 ∘ r)‖ =
      max ‖M.1.val *ᵥ (dyadicToReal ∘ r)‖ ‖M.2.val *ᵥ (dyadicToQ2 ∘ r)‖
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    unitDiagonal_mulVec_norm k.property.1,unitDiagonal_mulVec_norm k.property.2]

theorem compact_smul_mem_K_iff (k : K) (q : X) (δ : ℝ) :
    (k:G) • q ∈ BBEKOrbit.K δ ↔ q ∈ BBEKOrbit.K δ := by
  induction q using Quotient.inductionOn with
  | h M =>
    change (k:G) • mk M ∈ BBEKOrbit.K δ ↔ mk M ∈ BBEKOrbit.K δ
    rw [smul_mk,BBEKOrbit.mem_K_mk_iff,BBEKOrbit.mem_K_mk_iff]
    simp only [compact_vectorImage_norm]

theorem compact_preimage_K (k : K) (δ : ℝ) :
    (fun q : X => k • q) ⁻¹' BBEKOrbit.K δ = BBEKOrbit.K δ := by
  ext q
  exact compact_smul_mem_K_iff k q δ

end VV.BBEKCompactPreservation
