import VV.BBEKOneRootFullSupport
import VV.BBEKZariskiRoots
import VV.BBEKAlgebraicOrbit
import VV.BBEKRootSubgroups

/-! A non-Dirac canonical root leaf forces its polynomial-defined supporting
root subgroup to be the entire root. This connects the actual measure support
threshold to the groups denoted the two opposite root support groups in EL; it does not assert that
positive KS entropy supplies the non-Dirac premise. -/
noncomputable section
open Matrix Set MeasureTheory
open scoped Topology MatrixGroups
namespace VV.BBEKAlgebraicRootSupport
open BBEKDynamics BBEKRootSubgroups BBEKOneRootFullSupport
open BBEKZariskiRoots BBEKAlgebraicTrichotomy BBEKAlgebraicOrbit BBEKMahlerPadic

variable {F : Type*} [NormedField F] [MeasurableSpace F]

/-- Upper-root parameters in an actual matrix subgroup. -/
def upperParameters (H : Subgroup SL(2,F)) : AddSubgroup F where
  carrier := {u | upper u ∈ H}
  zero_mem' := by
    change BBEKFiniteQuotients.upper (0 : F) ∈ H
    simpa only [BBEKFiniteQuotients.upper_zero] using H.one_mem
  add_mem' := by
    intro a b ha hb
    change BBEKFiniteQuotients.upper (a+b) ∈ H
    rw [BBEKFiniteQuotients.upper_add]
    exact H.mul_mem ha hb
  neg_mem' := by
    intro a ha
    have he : upper (-a) = (upper a)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      change BBEKFiniteQuotients.upper (-a) * BBEKFiniteQuotients.upper a = 1
      rw [← BBEKFiniteQuotients.upper_add]
      simp
    change upper (-a) ∈ H
    rw [he]
    exact H.inv_mem ha

theorem lowerRoot_le_of_nonDirac_support (η : Measure F)
    (hfull : NonDiracRootSupport η) (hnd : η ≠ Measure.dirac 0)
    (P : Subgroup SL(2,F)) (hclosed : IsClosed (P : Set SL(2,F)))
    (hsupport : ∀ᵐ u ∂η, lower u ∈ P) : lowerRoot F ≤ P := by
  let S := lowerParameters P (MonoidHom.id SL(2,F))
  have hSclosed : IsClosed (S : Set F) := hclosed.preimage continuous_lower
  have hStop : S = ⊤ := (hfull hnd).2 S hSclosed hsupport
  intro g hg
  obtain ⟨u,rfl⟩ := (mem_lowerRoot_iff g).mp hg
  have hu : u ∈ S := hStop ▸ AddSubgroup.mem_top u
  exact hu

theorem upperRoot_le_of_nonDirac_support (η : Measure F)
    (hfull : NonDiracRootSupport η) (hnd : η ≠ Measure.dirac 0)
    (P : Subgroup SL(2,F)) (hclosed : IsClosed (P : Set SL(2,F)))
    (hsupport : ∀ᵐ u ∂η, upper u ∈ P) : upperRoot F ≤ P := by
  let S := upperParameters P
  have hSclosed : IsClosed (S : Set F) := hclosed.preimage continuous_upper
  have hStop : S = ⊤ := (hfull hnd).2 S hSclosed hsupport
  intro g hg
  obtain ⟨u,rfl⟩ := (mem_upperRoot_iff g).mp hg
  have hu : u ∈ S := hStop ▸ AddSubgroup.mem_top u
  exact hu

/-- The polynomial subgroup P on the lower root is exactly that root.
Neither algebraic connectedness nor a normalization hypothesis is needed. -/
theorem polynomial_lower_support_eq_root (η : Measure F)
    (hfull : NonDiracRootSupport η) (hnd : η ≠ Measure.dirac 0)
    (P : Subgroup SL(2,F)) (hpoly : PolynomialClosed (P : Set SL(2,F)))
    (hle : P ≤ lowerRoot F) (hsupport : ∀ᵐ u ∂η, lower u ∈ P) : P = lowerRoot F := by
  obtain ⟨eqs,heqs⟩ := hpoly
  have hclosed : IsClosed (P : Set SL(2,F)) := heqs ▸ matrixZeroSet_isClosed eqs
  exact le_antisymm hle (lowerRoot_le_of_nonDirac_support η hfull hnd P hclosed hsupport)

/-- The identical upper-root support-generation statement. -/
theorem polynomial_upper_support_eq_root (η : Measure F)
    (hfull : NonDiracRootSupport η) (hnd : η ≠ Measure.dirac 0)
    (P : Subgroup SL(2,F)) (hpoly : PolynomialClosed (P : Set SL(2,F)))
    (hle : P ≤ upperRoot F) (hsupport : ∀ᵐ u ∂η, upper u ∈ P) : P = upperRoot F := by
  obtain ⟨eqs,heqs⟩ := hpoly
  have hclosed : IsClosed (P : Set SL(2,F)) := heqs ▸ matrixZeroSet_isClosed eqs
  exact le_antisymm hle (upperRoot_le_of_nonDirac_support η hfull hnd P hclosed hsupport)

end VV.BBEKAlgebraicRootSupport



