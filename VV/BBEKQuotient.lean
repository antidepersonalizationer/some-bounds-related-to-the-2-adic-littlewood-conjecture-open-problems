import VV.BBEKDynamics
import VV.BBEKDyadic
import Mathlib.Topology.Algebra.Group.Quotient

/-! The literal S-arithmetic subgroup and homogeneous space in BBEK §5.
This file constructs the embeddings and quotient; lattice compactness and
measure rigidity are separate results, not part of these definitions. -/

noncomputable section
open Matrix
open scoped MatrixGroups Topology

namespace VV.BBEKQuotient
open BBEKDynamics

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def dyadicToReal : BBEKDyadic.dyadic →+* ℝ :=
  (Rat.castHom ℝ).comp BBEKDyadic.dyadic.subtype

def dyadicToQ2 : BBEKDyadic.dyadic →+* Q2 :=
  (Rat.castHom Q2).comp BBEKDyadic.dyadic.subtype

@[simp] theorem dyadicToReal_apply (q : BBEKDyadic.dyadic) : dyadicToReal q=(q.val:ℝ) := rfl
@[simp] theorem dyadicToQ2_apply (q : BBEKDyadic.dyadic) : dyadicToQ2 q=(q.val:Q2) := rfl

theorem dyadicToReal_injective : Function.Injective dyadicToReal := by
  intro a b h
  apply Subtype.ext
  change (a.val:ℝ)=(b.val:ℝ) at h
  exact_mod_cast h

theorem dyadicToQ2_injective : Function.Injective dyadicToQ2 := by
  intro a b h
  apply Subtype.ext
  change (a.val:Q2)=(b.val:Q2) at h
  exact_mod_cast h

def diagonalEmbedding : SL(2,BBEKDyadic.dyadic) →* G :=
  (Matrix.SpecialLinearGroup.map dyadicToReal).prod (Matrix.SpecialLinearGroup.map dyadicToQ2)

theorem diagonalEmbedding_injective : Function.Injective diagonalEmbedding := by
  intro A B h
  have hr := congrArg Prod.fst h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply dyadicToReal_injective
  exact congrArg (fun M : SL(2,ℝ) => M i j) hr

def Gamma : Subgroup G := diagonalEmbedding.range

theorem mem_Gamma_iff (g : G) : g ∈ Gamma ↔
    ∃ A : SL(2,BBEKDyadic.dyadic),diagonalEmbedding A=g := Iff.rfl

def X := G ⧸ Gamma

instance : TopologicalSpace X := inferInstanceAs (TopologicalSpace (G ⧸ Gamma))
instance : MulAction G X := inferInstanceAs (MulAction G (G ⧸ Gamma))
instance : ContinuousSMul G X := inferInstanceAs (ContinuousSMul G (G ⧸ Gamma))

def mk (g : G) : X := QuotientGroup.mk g
def basePoint : X := mk 1
def parameterPoint (u : ℝ) (v : Q2) : X := mk (x u v)

theorem continuous_mk : Continuous mk := QuotientGroup.continuous_mk

theorem mk_eq_iff (g h : G) : mk g=mk h ↔ g⁻¹*h ∈ Gamma :=
  QuotientGroup.eq

theorem mk_right_gamma (g : G) (A : SL(2,BBEKDyadic.dyadic)) :
    mk (g*diagonalEmbedding A)=mk g := by
  apply (mk_eq_iff _ _).mpr
  have he : (g*diagonalEmbedding A)⁻¹*g=(diagonalEmbedding A)⁻¹ := by group
  rw [he]
  exact Gamma.inv_mem ⟨A,rfl⟩

theorem smul_mk (g h : G) : g • mk h=mk (g*h) := rfl

theorem parameterPoint_continuous : Continuous (fun a : ℝ×Q2 => parameterPoint a.1 a.2) :=
  continuous_mk.comp continuous_x

def coneOrbit (z : X) : Set X :=
  {w | ∃ t : ℝ,∃ n : ℤ,Cone t n ∧ w=psi t n • z}

theorem mem_coneOrbit_self (z : X) : z ∈ coneOrbit z := by
  exact ⟨0,0,cone_zero,by simp⟩

theorem coneOrbit_forward {z : X} {t : ℝ} {n : ℤ} (h : Cone t n) {w : X}
    (hw : w ∈ coneOrbit z) : psi t n • w ∈ coneOrbit z := by
  obtain ⟨s,m,hs,rfl⟩ := hw
  refine ⟨t+s,n+m,h.add hs,?_⟩
  rw [psi_add,MulAction.mul_smul]

end VV.BBEKQuotient
