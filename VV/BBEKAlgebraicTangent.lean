import VV.BBEKPolynomialDifferential

/-! The actual tangent space to a matrix subgroup's vanishing ideal.
It is constructed from formal differentials, not supplied as auxiliary data. -/
noncomputable section
open Matrix MvPolynomial
open scoped MatrixGroups
namespace VV.BBEKAlgebraicTangent
open BBEKPolynomialDifferential

variable {K : Type*} [Field K]
abbrev Mat2 (K : Type*) := Matrix (Fin 2) (Fin 2) K
abbrev Polys (K : Type*) [CommSemiring K] := MvPolynomial (Fin 2 × Fin 2) K

def entries (M : Mat2 K) : Fin 2 × Fin 2 → K := fun ij => M ij.1 ij.2
def identityEntries : Fin 2 × Fin 2 → K := entries (1 : Mat2 K)

/-- All actual polynomial equations vanishing on the subgroup's points. -/
def vanishingIdeal (L : Subgroup SL(2,K)) : Ideal (Polys K) where
  carrier := {p | ∀ g ∈ L, eval (entries g.val) p=0}
  zero_mem' := by intros; simp
  add_mem' := by intro p q hp hq g hg; simp [map_add,hp g hg,hq g hg]
  smul_mem' := by intro a p hp g hg; simp [smul_eq_mul,map_mul,hp g hg]

/-- The Zariski tangent space at the identity, as a literal matrix subspace. -/
def tangent (L : Subgroup SL(2,K)) : Submodule K (Mat2 K) where
  carrier := {M | ∀ p ∈ vanishingIdeal L, differential identityEntries p (entries M)=0}
  zero_mem' := by intro p hp; exact map_zero _
  add_mem' := by
    intro M N hM hN p hp
    change differential identityEntries p (entries M+entries N)=0
    rw [map_add,hM p hp,hN p hp,add_zero]
  smul_mem' := by
    intro a M hM p hp
    change differential identityEntries p (a • entries M)=0
    rw [map_smul,hM p hp,smul_zero]

def determinantEquation : Polys K :=
  X (0,0)*X (1,1)-X (0,1)*X (1,0)-C 1

theorem determinantEquation_mem (L : Subgroup SL(2,K)) :
    determinantEquation ∈ vanishingIdeal L := by
  intro g hg
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  simpa [determinantEquation,entries] using sub_eq_zero.mpr hd

theorem tangent_trace_zero (L : Subgroup SL(2,K)) {M : Mat2 K} (hM : M ∈ tangent L) :
    Matrix.trace M=0 := by
  have hm := hM determinantEquation (determinantEquation_mem L)
  simpa [determinantEquation,differential_mul,identityEntries,entries,
    Matrix.trace,Fin.sum_univ_two,add_comm] using hm

def conjugationVariables (g : SL(2,K)) (ij : Fin 2 × Fin 2) : Polys K :=
  ∑ k : Fin 2, ∑ l : Fin 2, C (g ij.1 k)*X (k,l)*C ((g⁻¹) l ij.2)

theorem eval_conjugationVariables (g : SL(2,K)) (M : Mat2 K) (ij : Fin 2 × Fin 2) :
    eval (entries M) (conjugationVariables g ij)=entries (g.val*M*(g⁻¹).val) ij := by
  simp [conjugationVariables,entries,Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem differential_conjugationVariables (g : SL(2,K))
    (x : Fin 2 × Fin 2 → K) (M : Mat2 K) (ij : Fin 2 × Fin 2) :
    differential x (conjugationVariables g ij) (entries M)=
      entries (g.val*M*(g⁻¹).val) ij := by
  simp [conjugationVariables,Fin.sum_univ_two,differential_mul,entries,Matrix.mul_apply]
  ring

def conjugationPullback (g : SL(2,K)) (p : Polys K) : Polys K :=
  p.eval₂ C (conjugationVariables g)

theorem eval_conjugationPullback (g : SL(2,K)) (M : Mat2 K) (p : Polys K) :
    eval (entries M) (conjugationPullback g p)=eval (entries (g.val*M*(g⁻¹).val)) p := by
  unfold conjugationPullback
  rw [eval₂_comp_left]
  have hc : (eval (entries M)).comp C=RingHom.id K := by ext a; simp
  rw [hc]
  congr 1
  funext ij
  exact eval_conjugationVariables g M ij

theorem conjugationPullback_mem (L : Subgroup SL(2,K)) {g : SL(2,K)} (hg : g ∈ L)
    {p : Polys K} (hp : p ∈ vanishingIdeal L) : conjugationPullback g p ∈ vanishingIdeal L := by
  intro h hh
  rw [eval_conjugationPullback]
  exact hp (g*h*g⁻¹) (L.mul_mem (L.mul_mem hg hh) (L.inv_mem hg))

/-- Adjoint stability of the tangent is proved from actual subgroup
closure and substitution of its actual vanishing equations. -/
theorem tangent_adjoint_mem (L : Subgroup SL(2,K)) {g : SL(2,K)} (hg : g ∈ L)
    {M : Mat2 K} (hM : M ∈ tangent L) : g.val*M*(g⁻¹).val ∈ tangent L := by
  intro p hp
  have hz := hM (conjugationPullback g p) (conjugationPullback_mem L hg hp)
  unfold conjugationPullback at hz
  rw [differential_substitute] at hz
  have he : (fun ij => eval identityEntries (conjugationVariables g ij))=identityEntries := by
    funext ij
    rw [identityEntries,eval_conjugationVariables]
    simp only [Matrix.mul_one,← Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  simpa only [he,differential_conjugationVariables] using hz

end VV.BBEKAlgebraicTangent
