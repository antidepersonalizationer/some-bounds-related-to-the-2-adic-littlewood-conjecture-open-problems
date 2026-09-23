import VV.BBEKLeafwiseChart
import VV.BBEKKernelFiberRestriction
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Encodable.Pi

/-! Actual Gauss-coordinate changes under right multiplication. Their transverse
coordinate is independent of the lower leaf variable, and the leaf map is a
translation depending only on the transverse coordinate. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups
namespace VV.BBEKGaussTransition
open BBEKDynamics BBEKGaussChart BBEKLeafwiseKernel BBEKLeafwiseChart

abbrev TransverseF (F : Type*) [Zero F] := {a : F // a ≠ 0} × F

def rightDenom {F : Type*} [Field F] (M : SL(2,F)) (b : TransverseF F) : F :=
  M 0 0 + b.2 * M 1 0

def rightDomain {F : Type*} [Field F] (M : SL(2,F)) : Set (TransverseF F) :=
  {b | rightDenom M b ≠ 0}

def rightTransverse {F : Type*} [Field F] (M : SL(2,F)) (b : rightDomain M) :
    TransverseF F :=
  (⟨b.val.1 * rightDenom M b.val, mul_ne_zero b.val.1.property b.property⟩,
    (M 0 1 + b.val.2 * M 1 1) / rightDenom M b.val)

def rightLeafShift {F : Type*} [Field F] (M : SL(2,F)) (b : TransverseF F) : F :=
  M 1 0 / ((b.1 : F)^2 * rightDenom M b)

def rightParams {F : Type*} [Field F] (M : SL(2,F)) (b : rightDomain M) (u : F) :
    Params F := (u + rightLeafShift M b.val, rightTransverse M b)

theorem matrixOf_11 {F : Type*} [Field F] (p : Params F) :
    matrixOf p 1 1 = p.1 * p.2.1.val * p.2.2 + p.2.1.val⁻¹ := by
  simp [matrixOf,lower,BBEKDynamics.diagonal,BBEKMahlerPadic.upper,
    Matrix.mul_apply,Fin.sum_univ_two]

theorem mul_matrixOf_00 {F : Type*} [Field F] (M : SL(2,F))
    (b : TransverseF F) (u : F) :
    (matrixOf (u,b) * M) 0 0 = (b.1 : F) * rightDenom M b := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, rightDenom]
  ring

/-- The exact coordinate transition for one SL₂ factor. -/
theorem matrixOf_rightParams {F : Type*} [Field F] (M : SL(2,F))
    (b : rightDomain M) (u : F) :
    matrixOf (rightParams M b u) = matrixOf (u,b.val) * M := by
  have ha : (b.val.1 : F) ≠ 0 := b.val.1.property
  have hd : rightDenom M b.val ≠ 0 := b.property
  let N : domain F := ⟨matrixOf (u,b.val) * M, by
    change (matrixOf (u,b.val) * M) 0 0 ≠ 0
    rw [mul_matrixOf_00]
    exact mul_ne_zero ha hd⟩
  have he : coordinates N = rightParams M b u := by
    apply Prod.ext
    · change (matrixOf (u,b.val) * M) 1 0 / (matrixOf (u,b.val) * M) 0 0 = _
      rw [mul_matrixOf_00]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        matrixOf_10, matrixOf_11]
      dsimp [rightParams, rightLeafShift]
      field_simp
      <;> simp only [rightDenom]
      <;> ring
    · apply Prod.ext
      · apply Subtype.ext
        exact mul_matrixOf_00 M b.val u
      · change (matrixOf (u,b.val) * M) 0 1 / (matrixOf (u,b.val) * M) 0 0 = _
        rw [mul_matrixOf_00]
        simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          matrixOf_00, matrixOf_01]
        change ((b.val.1 : F)*M 0 1 + (b.val.1 : F)*b.val.2*M 1 1) /
          ((b.val.1 : F)*rightDenom M b.val) = _
        dsimp [rightParams, rightTransverse]
        field_simp
        <;> ring
  have hmatrix := congrArg Subtype.val (matrix_coordinates N)
  simpa only [he, matrixInDomain, N] using hmatrix

theorem continuous_rightDenom {F : Type*} [NormedField F] (M : SL(2,F)) :
    Continuous (rightDenom M) := by unfold rightDenom; fun_prop

theorem isOpen_rightDomain {F : Type*} [NormedField F] (M : SL(2,F)) :
    IsOpen (rightDomain M) :=
  (isClosed_eq (continuous_rightDenom M) continuous_const).isOpen_compl

theorem continuous_rightTransverse {F : Type*} [NormedField F] (M : SL(2,F)) :
    Continuous (rightTransverse M) := by
  apply Continuous.prodMk
  · exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).mul
      ((continuous_rightDenom M).comp continuous_subtype_val)).subtype_mk _
  · exact (continuous_const.add
      ((continuous_snd.comp continuous_subtype_val).mul continuous_const)).div
        ((continuous_rightDenom M).comp continuous_subtype_val) (fun b => b.property)

theorem continuous_rightLeafShift {F : Type*} [NormedField F] (M : SL(2,F)) :
    Continuous (fun b : rightDomain M => rightLeafShift M b.val) := by
  apply Continuous.div continuous_const
  · exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).pow 2).mul
      ((continuous_rightDenom M).comp continuous_subtype_val)
  · intro b
    exact mul_ne_zero (pow_ne_zero 2 b.val.1.property) b.property

theorem rightTransverse_mem_inverse {F : Type*} [Field F] (M : SL(2,F))
    (b : rightDomain M) : rightTransverse M b ∈ rightDomain M⁻¹ := by
  have he : matrixOf (rightParams M b 0) * M⁻¹ = matrixOf (0,b.val) := by
    rw [matrixOf_rightParams]
    group
  have he00 := congrArg (fun N : SL(2,F) => N 0 0) he
  change (matrixOf (rightParams M b 0) * M⁻¹) 0 0 = matrixOf (0,b.val) 0 0 at he00
  rw [matrixOf_00] at he00
  change (matrixOf (0 + rightLeafShift M b.val, rightTransverse M b) * M⁻¹) 0 0 = _ at he00
  rw [mul_matrixOf_00] at he00
  exact right_ne_zero_of_mul (he00.trans_ne b.val.1.property)

theorem rightParams_inverse {F : Type*} [Field F] (M : SL(2,F))
    (b : rightDomain M) (u : F) :
    rightParams M⁻¹ ⟨rightTransverse M b, rightTransverse_mem_inverse M b⟩
      (u + rightLeafShift M b.val) = (u,b.val) := by
  apply matrixOf_injective
  rw [matrixOf_rightParams]
  change matrixOf (rightParams M b u) * M⁻¹ = _
  rw [matrixOf_rightParams]
  group

theorem rightTransverse_inverse {F : Type*} [Field F] (M : SL(2,F))
    (b : rightDomain M) :
    rightTransverse M⁻¹ ⟨rightTransverse M b, rightTransverse_mem_inverse M b⟩ = b.val :=
  congrArg Prod.snd (rightParams_inverse M b 0)

/-- The transverse change is an actual homeomorphism between its open domains. -/
def rightTransverseHomeomorph {F : Type*} [NormedField F] (M : SL(2,F)) :
    rightDomain M ≃ₜ rightDomain M⁻¹ where
  toFun b := ⟨rightTransverse M b, rightTransverse_mem_inverse M b⟩
  invFun c := ⟨rightTransverse M⁻¹ c, by simpa using rightTransverse_mem_inverse M⁻¹ c⟩
  left_inv b := Subtype.ext (rightTransverse_inverse M b)
  right_inv c := by
    apply Subtype.ext
    simpa only [rightTransverse, rightDenom, inv_inv] using rightTransverse_inverse M⁻¹ c
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_rightTransverse M
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_rightTransverse M⁻¹

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev GroupRightDomain (g : G) := rightDomain g.1 × rightDomain g.2

def groupRightTransverse (g : G) (b : GroupRightDomain g) : Transverse :=
  (rightTransverse g.1 b.1, rightTransverse g.2 b.2)

def groupRightLeafShift (g : G) (b : GroupRightDomain g) : Leaf :=
  (rightLeafShift g.1 b.1.val, rightLeafShift g.2 b.2.val)

def groupTransverseBase {g : G} (b : GroupRightDomain g) : Transverse := (b.1.val,b.2.val)

theorem groupMatrix_right_transition (g : G) (b : GroupRightDomain g) (u : Leaf) :
    groupMatrixOf (splitCoordinates.symm (groupRightTransverse g b, u + groupRightLeafShift g b)) =
      groupMatrixOf (splitCoordinates.symm (groupTransverseBase b,u)) * g := by
  apply Prod.ext
  · exact matrixOf_rightParams g.1 b.1 u.1
  · exact matrixOf_rightParams g.2 b.2 u.2

open BBEKQuotient

/-- Each arithmetic branch of a genuine quotient-chart overlap has precisely
the displayed transverse map and leaf translation. -/
theorem quotient_transition (g h : G) (γ : Gamma)
    (b : GroupRightDomain (g*(γ:G)*h⁻¹)) (u : Leaf) :
    quotientCoordinates h (splitCoordinates.symm
      (groupRightTransverse (g*(γ:G)*h⁻¹) b, u + groupRightLeafShift (g*(γ:G)*h⁻¹) b)) =
      quotientCoordinates g (splitCoordinates.symm (groupTransverseBase b,u)) := by
  unfold quotientCoordinates
  rw [groupMatrix_right_transition]
  have he (k : G) : (k*(g*(γ:G)*h⁻¹))*h = (k*g)*(γ:G) := by group
  rw [he]
  symm
  apply (mk_eq_iff _ _).mpr
  convert γ.property using 1
  congr 1
  group

theorem rightDomain_of_matrix_product {F : Type*} [Field F]
    (M : SL(2,F)) {p q : Params F} (hpq : matrixOf p * M = matrixOf q) :
    p.2 ∈ rightDomain M := by
  have he := congrArg (fun N : SL(2,F) => N 0 0) hpq
  change (matrixOf (p.1,p.2) * M) 0 0 = matrixOf q 0 0 at he
  rw [mul_matrixOf_00, matrixOf_00] at he
  exact right_ne_zero_of_mul (he.trans_ne q.2.1.property)

/-- Every actual overlap arises in one arithmetic branch, rather than just
the previously constructed branch maps being valid when supplied. -/
theorem exists_transition_of_quotient_eq (g h : G) {p q : GroupParams}
    (he : quotientCoordinates g p = quotientCoordinates h q) :
    ∃ γ : Gamma, ∃ b : GroupRightDomain (g*(γ:G)*h⁻¹),
      groupTransverseBase b = (splitCoordinates p).1 ∧
      splitCoordinates q = (groupRightTransverse (g*(γ:G)*h⁻¹) b,
        (splitCoordinates p).2 + groupRightLeafShift (g*(γ:G)*h⁻¹) b) := by
  let γ : Gamma := ⟨(groupMatrixOf p*g)⁻¹*(groupMatrixOf q*h), (mk_eq_iff _ _).mp he⟩
  have hm : groupMatrixOf p * (g*(γ:G)*h⁻¹) = groupMatrixOf q := by
    dsimp [γ]
    group
  have hr := rightDomain_of_matrix_product (g*(γ:G)*h⁻¹).1 (congrArg Prod.fst hm)
  have hp := rightDomain_of_matrix_product (g*(γ:G)*h⁻¹).2 (congrArg Prod.snd hm)
  let b : GroupRightDomain (g*(γ:G)*h⁻¹) := (⟨p.1.2,hr⟩,⟨p.2.2,hp⟩)
  refine ⟨γ,b,rfl,?_⟩
  apply splitCoordinates.symm.injective
  simp only [Homeomorph.symm_apply_apply]
  apply groupMatrixOf_injective
  rw [groupMatrix_right_transition]
  exact hm.symm

instance gamma_countable : Countable Gamma := by
  classical
  letI : Encodable BBEKDyadic.dyadic := Encodable.ofCountable _
  letI : Encodable (Matrix (Fin 2) (Fin 2) BBEKDyadic.dyadic) :=
    inferInstanceAs (Encodable (Fin 2 → Fin 2 → BBEKDyadic.dyadic))
  letI : Countable SL(2,BBEKDyadic.dyadic) :=
    inferInstanceAs (Countable {m : Matrix (Fin 2) (Fin 2) BBEKDyadic.dyadic // m.det=1})
  exact (Set.countable_range diagonalEmbedding).to_subtype

end VV.BBEKGaussTransition
