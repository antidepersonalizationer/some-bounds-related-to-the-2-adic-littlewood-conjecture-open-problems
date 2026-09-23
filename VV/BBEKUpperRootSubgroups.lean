import VV.BBEKRootSubgroups
import VV.BBEKMautner

/-!
The upper-root counterpart of `BBEKRootSubgroups`.  Everything here is
proved by explicit two-by-two matrix identities.  Thus an actual subgroup of
the BBEK product group which is normalized by the full split diagonal and
contains one nonzero upper unipotent contains that whole local root group.
-/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace VV.BBEKUpperRootSubgroups
open BBEKDynamics BBEKDiagonal BBEKMautner

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem diagonal_conjugate_upper {F : Type*} [Field F]
    (a u : F) (ha : a ≠ 0) :
    diagonal a ha * BBEKFiniteQuotients.upper u * (diagonal a ha)⁻¹ =
      BBEKFiniteQuotients.upper (a^2 * u) := by
  rw [diagonal_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [BBEKDynamics.diagonal, BBEKFiniteQuotients.upper, Matrix.mul_apply,
      Fin.sum_univ_two, ha, pow_two] <;> ring

def upperParameters {F J : Type*} [Field F] [Group J]
    (H : Subgroup J) (ι : SL(2,F) →* J) : AddSubgroup F where
  carrier := {u | ι (BBEKFiniteQuotients.upper u) ∈ H}
  zero_mem' := by
    change ι (BBEKFiniteQuotients.upper 0) ∈ H
    simpa only [BBEKFiniteQuotients.upper_zero, map_one] using H.one_mem
  add_mem' := by
    intro a b ha hb
    change ι (BBEKFiniteQuotients.upper (a+b)) ∈ H
    rw [BBEKFiniteQuotients.upper_add, map_mul]
    exact H.mul_mem ha hb
  neg_mem' := by
    intro a ha
    have he : BBEKFiniteQuotients.upper (-a) =
        (BBEKFiniteQuotients.upper a)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← BBEKFiniteQuotients.upper_add]
      simp
    change ι (BBEKFiniteQuotients.upper (-a)) ∈ H
    rw [he, map_inv]
    exact H.inv_mem ha

theorem all_upper_mem_of_diagonal_normalizes {F J : Type*}
    [Field F] [CharZero F] [Group J] (H : Subgroup J) (ι : SL(2,F) →* J)
    (hn : ∀ a (ha : a ≠ 0), ι (diagonal a ha) ∈ H.normalizer)
    {u : F} (hu0 : u ≠ 0) (hu : ι (BBEKFiniteQuotients.upper u) ∈ H) :
    ∀ v : F, ι (BBEKFiniteQuotients.upper v) ∈ H := by
  have hs : ∀ a : F, a ≠ 0 → ∀ u ∈ upperParameters H ι,
      a^2*u ∈ upperParameters H ι := by
    intro a ha u hu
    have hh := (Subgroup.mem_normalizer_iff.mp (hn a ha)
      (ι (BBEKFiniteQuotients.upper u))).mp hu
    rw [← map_inv, ← map_mul, ← map_mul, diagonal_conjugate_upper] at hh
    exact hh
  have ht := BBEKRootSubgroups.additive_eq_top_of_square_stable
    (upperParameters H ι) hs hu hu0
  intro v
  change v ∈ upperParameters H ι
  rw [ht]
  trivial

theorem all_real_upper_mem (H : Subgroup G) (hn : A ≤ H.normalizer)
    {u : ℝ} (hu0 : u ≠ 0) (hu : upperPoint u 0 ∈ H) :
    ∀ v : ℝ, upperPoint v 0 ∈ H := by
  have hh := all_upper_mem_of_diagonal_normalizes H
    (MonoidHom.inl SL(2,ℝ) SL(2,Q2)) (fun a ha => hn
      ⟨⟨a,ha,rfl⟩,(diagonalGroup Q2).one_mem⟩) hu0
  exact fun v => by
    simpa only [upperPoint, BBEKFiniteQuotients.upper_zero,
      MonoidHom.inl_apply] using
      hh (by simpa only [upperPoint, BBEKFiniteQuotients.upper_zero,
        MonoidHom.inl_apply] using hu) v

theorem all_padic_upper_mem (H : Subgroup G) (hn : A ≤ H.normalizer)
    {u : Q2} (hu0 : u ≠ 0) (hu : upperPoint 0 u ∈ H) :
    ∀ v : Q2, upperPoint 0 v ∈ H := by
  have hh := all_upper_mem_of_diagonal_normalizes H
    (MonoidHom.inr SL(2,ℝ) SL(2,Q2)) (fun a ha => hn
      ⟨(diagonalGroup ℝ).one_mem,⟨a,ha,rfl⟩⟩) hu0
  exact fun v => by
    simpa only [upperPoint, BBEKFiniteQuotients.upper_zero,
      MonoidHom.inr_apply] using
      hh (by simpa only [upperPoint, BBEKFiniteQuotients.upper_zero,
        MonoidHom.inr_apply] using hu) v

end VV.BBEKUpperRootSubgroups
