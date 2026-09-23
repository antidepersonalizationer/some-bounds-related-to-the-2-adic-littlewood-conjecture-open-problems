import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Coset.Basic

/-! The lattice attached to a pair of determinant-one matrices, and its
descent to the diagonal arithmetic quotient. These algebraic statements
apply in particular to Z[1/2] embedded in R and Q_2. -/

namespace VV.BBEKLattice
open Matrix
open scoped MatrixGroups

variable {R K L : Type*} [CommRing R] [CommRing K] [CommRing L]

def diagonalMap (f : R →+* K) (g : R →+* L) :
    SL(2,R) →* (SL(2,K) × SL(2,L)) :=
  (SpecialLinearGroup.map f).prod (SpecialLinearGroup.map g)

def vectorImage (f : R →+* K) (g : R →+* L)
    (M : SL(2,K) × SL(2,L)) (v : Fin 2 → R) :
    (Fin 2 → K) × (Fin 2 → L) :=
  ((M.1 : Matrix (Fin 2) (Fin 2) K) *ᵥ (f ∘ v),
   (M.2 : Matrix (Fin 2) (Fin 2) L) *ᵥ (g ∘ v))

def lattice (f : R →+* K) (g : R →+* L) (M : SL(2,K) × SL(2,L)) :
    Set ((Fin 2 → K) × (Fin 2 → L)) := Set.range (vectorImage f g M)

@[simp] theorem vectorImage_zero (f : R →+* K) (g : R →+* L)
    (M : SL(2,K) × SL(2,L)) : vectorImage f g M 0 = 0 := by
  apply Prod.ext
  · funext i
    change (∑ j : Fin 2, M.1 i j * f (0:R)) = 0
    simp
  · funext i
    change (∑ j : Fin 2, M.2 i j * g (0:R)) = 0
    simp

theorem vectorImage_injective (f : R →+* K) (g : R →+* L)
    (hf : Function.Injective f) (M : SL(2,K) × SL(2,L)) :
    Function.Injective (vectorImage f g M) := by
  intro v w h
  have hh := congrArg Prod.fst h
  have hv : f ∘ v = f ∘ w := (M.1.toLin').injective hh
  funext i
  exact hf (congrFun hv i)

theorem vectorImage_mul_diagonal (f : R →+* K) (g : R →+* L)
    (M : SL(2,K) × SL(2,L)) (A : SL(2,R)) (v : Fin 2 → R) :
    vectorImage f g (M * diagonalMap f g A) v =
      vectorImage f g M ((A : Matrix (Fin 2) (Fin 2) R) *ᵥ v) := by
  apply Prod.ext
  · change ((M.1 : Matrix (Fin 2) (Fin 2) K) * (A.val.map f)) *ᵥ (f ∘ v) =
      (M.1 : Matrix (Fin 2) (Fin 2) K) *ᵥ (f ∘ (A.val *ᵥ v))
    rw [← Matrix.mulVec_mulVec]
    apply congrArg (fun w => (M.1 : Matrix (Fin 2) (Fin 2) K) *ᵥ w)
    funext i
    exact (f.map_mulVec A.val v i).symm
  · change ((M.2 : Matrix (Fin 2) (Fin 2) L) * (A.val.map g)) *ᵥ (g ∘ v) =
      (M.2 : Matrix (Fin 2) (Fin 2) L) *ᵥ (g ∘ (A.val *ᵥ v))
    rw [← Matrix.mulVec_mulVec]
    apply congrArg (fun w => (M.2 : Matrix (Fin 2) (Fin 2) L) *ᵥ w)
    funext i
    exact (g.map_mulVec A.val v i).symm

/-- A determinant-one change of arithmetic basis preserves the full
actual lattice, in both directions. -/
theorem lattice_mul_diagonal (f : R →+* K) (g : R →+* L)
    (M : SL(2,K) × SL(2,L)) (A : SL(2,R)) :
    lattice f g (M * diagonalMap f g A) = lattice f g M := by
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨(A : Matrix (Fin 2) (Fin 2) R) *ᵥ v,
      (vectorImage_mul_diagonal f g M A v).symm⟩
  · rintro ⟨v,rfl⟩
    obtain ⟨w,hw⟩ := (A.toLin').surjective v
    refine ⟨w,?_⟩
    rw [vectorImage_mul_diagonal]
    exact congrArg (vectorImage f g M) hw

theorem lattice_eq_of_leftRel (f : R →+* K) (g : R →+* L)
    {M N : SL(2,K) × SL(2,L)}
    (h : QuotientGroup.leftRel (diagonalMap f g).range M N) :
    lattice f g M = lattice f g N := by
  obtain ⟨A,hA⟩ := QuotientGroup.leftRel_apply.mp h
  have hN : N = M * diagonalMap f g A := by
    rw [hA,mul_inv_cancel_left]
  rw [hN,lattice_mul_diagonal]

/-- The actual set of lattice vectors attached to an arithmetic coset. -/
def quotientLattice (f : R →+* K) (g : R →+* L) :
    ((SL(2,K) × SL(2,L)) ⧸ (diagonalMap f g).range) →
      Set ((Fin 2 → K) × (Fin 2 → L)) :=
  Quotient.lift (lattice f g) (fun _ _ h => lattice_eq_of_leftRel f g h)

@[simp] theorem quotientLattice_mk (f : R →+* K) (g : R →+* L)
    (M : SL(2,K) × SL(2,L)) :
    quotientLattice f g (QuotientGroup.mk M) = lattice f g M := rfl

theorem zero_mem_quotientLattice (f : R →+* K) (g : R →+* L)
    (q : (SL(2,K) × SL(2,L)) ⧸ (diagonalMap f g).range) :
    0 ∈ quotientLattice f g q := by
  induction q using Quotient.inductionOn with
  | h M => exact ⟨0,vectorImage_zero f g M⟩

end VV.BBEKLattice
