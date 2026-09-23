import VV.BBEKDiagonal

/-!
The algebraic root-group step in the first branch of EL Corollary 6.2.
An additive subgroup of a characteristic-zero field stable under all square
scalings is either zero or the whole field. Consequently a subgroup normalized
by the full split diagonal group that contains a nontrivial element of one
actual lower root group contains that entire root group.
This does not assume, or prove, the preceding low-entropy dichotomy.
-/
noncomputable section
open scoped MatrixGroups
namespace VV.BBEKRootSubgroups
open BBEKDynamics BBEKDiagonal

theorem additive_eq_top_of_square_stable {F : Type*} [Field F] [CharZero F]
    (H : AddSubgroup F) (hs : ∀ a : F, a ≠ 0 → ∀ u ∈ H, a^2*u ∈ H)
    {u : F} (hu : u ∈ H) (hu0 : u ≠ 0) : H = ⊤ := by
  have hs' (a : F) : a^2*u ∈ H := by
    by_cases ha : a = 0
    · simpa only [ha, zero_pow (by decide : 2 ≠ 0), zero_mul] using H.zero_mem
    · exact hs a ha u hu
  apply top_unique
  intro v _
  have he : ((v/u+1)/2)^2*u - ((v/u-1)/2)^2*u = v := by
    field_simp
    <;> ring
  rw [← he]
  exact H.sub_mem (hs' _) (hs' _)

def lowerParameters {F J : Type*} [Field F] [Group J]
    (H : Subgroup J) (ι : SL(2,F) →* J) : AddSubgroup F where
  carrier := {u | ι (lower u) ∈ H}
  zero_mem' := by
    change ι (lower 0) ∈ H
    simpa only [lower_zero, map_one] using H.one_mem
  add_mem' := by
    intro a b ha hb
    change ι (lower (a+b)) ∈ H
    rw [lower_add, map_mul]
    exact H.mul_mem ha hb
  neg_mem' := by
    intro a ha
    have he : lower (-a) = (lower a)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← lower_add]
      simp
    change ι (lower (-a)) ∈ H
    rw [he, map_inv]
    exact H.inv_mem ha

/-- Normalization by every diagonal is the actual group-theoretic hypothesis;
no closedness or algebraicity of the root intersection is needed. -/
theorem all_lower_mem_of_diagonal_normalizes {F J : Type*}
    [Field F] [CharZero F] [Group J] (H : Subgroup J) (ι : SL(2,F) →* J)
    (hn : ∀ a (ha : a ≠ 0), ι (diagonal a ha) ∈ H.normalizer)
    {u : F} (hu0 : u ≠ 0) (hu : ι (lower u) ∈ H) :
    ∀ v : F, ι (lower v) ∈ H := by
  have hs : ∀ a : F, a ≠ 0 → ∀ u ∈ lowerParameters H ι,
      a^2*u ∈ lowerParameters H ι := by
    intro a ha u hu
    have hh := (Subgroup.mem_normalizer_iff.mp (hn a⁻¹ (inv_ne_zero ha))
      (ι (lower u))).mp hu
    rw [← map_inv, ← map_mul, ← map_mul, diagonal_conjugate, inv_inv] at hh
    exact hh
  have ht := additive_eq_top_of_square_stable (lowerParameters H ι) hs hu hu0
  intro v
  change v ∈ lowerParameters H ι
  rw [ht]
  trivial

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The actual real lower root of SL₂(R) × SL₂(Q₂). -/
theorem all_real_lower_mem (H : Subgroup G) (hn : A ≤ H.normalizer)
    {u : ℝ} (hu0 : u ≠ 0) (hu : x u 0 ∈ H) : ∀ v : ℝ, x v 0 ∈ H := by
  have hh := all_lower_mem_of_diagonal_normalizes H
    (MonoidHom.inl SL(2,ℝ) SL(2,Q2)) (fun a ha => hn
      ⟨⟨a,ha,rfl⟩,(diagonalGroup Q2).one_mem⟩) hu0
  exact fun v => by
    simpa only [x, lower_zero, MonoidHom.inl_apply] using
      hh (by simpa only [x, lower_zero, MonoidHom.inl_apply] using hu) v

/-- The actual 2-adic lower root of SL₂(R) × SL₂(Q₂). -/
theorem all_padic_lower_mem (H : Subgroup G) (hn : A ≤ H.normalizer)
    {u : Q2} (hu0 : u ≠ 0) (hu : x 0 u ∈ H) : ∀ v : Q2, x 0 v ∈ H := by
  have hh := all_lower_mem_of_diagonal_normalizes H
    (MonoidHom.inr SL(2,ℝ) SL(2,Q2)) (fun a ha => hn
      ⟨(diagonalGroup ℝ).one_mem,⟨a,ha,rfl⟩⟩) hu0
  exact fun v => by
    simpa only [x, lower_zero, MonoidHom.inr_apply] using
      hh (by simpa only [x, lower_zero, MonoidHom.inr_apply] using hu) v

end VV.BBEKRootSubgroups
