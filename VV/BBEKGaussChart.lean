import VV.BBEKMahlerPadic
import VV.BBEKDiagonal

/-! Explicit Gauss coordinates and the actual diagonal centralizer.
All coordinates and conjugation identities are concrete matrix formulas. -/

noncomputable section
open Matrix
open scoped Topology MatrixGroups

namespace VV.BBEKGaussChart
open BBEKDynamics BBEKDiagonal BBEKMahlerPadic
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem mem_diagonalGroup_iff {F : Type*} [Field F] (M : SL(2,F)) :
    M ∈ diagonalGroup F ↔ M 0 1 = 0 ∧ M 1 0 = 0 := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    simp [BBEKDynamics.diagonal]
  · rintro ⟨hb,hc⟩
    have hd : M 0 0 * M 1 1 = 1 := by
      simpa only [Matrix.det_fin_two,hb,hc,mul_zero,sub_zero] using M.property
    have ha : M 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hd
    refine ⟨M 0 0,ha,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [BBEKDynamics.diagonal,hb,hc]
    exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hd)

theorem commute_diagonal_iff {F : Type*} [Field F] (M : SL(2,F))
    (a : F) (ha : a ≠ 0) (hreg : a ≠ a⁻¹) :
    Commute M (BBEKDynamics.diagonal a ha) ↔ M ∈ diagonalGroup F := by
  constructor
  · intro h
    apply (mem_diagonalGroup_iff M).mpr
    have hb := congrArg (fun N : SL(2,F) => N 0 1) h.eq
    have hc := congrArg (fun N : SL(2,F) => N 1 0) h.eq
    simp [BBEKDynamics.diagonal,Matrix.mul_apply,Fin.sum_univ_two] at hb hc
    constructor
    · have he : (a-a⁻¹)*M 0 1 = 0 := by linear_combination -hb
      exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hreg)
    · have he : (a-a⁻¹)*M 1 0 = 0 := by linear_combination hc
      exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hreg)
  · intro h
    exact diagonal_commute h ⟨a,ha,rfl⟩

theorem commute_psi_iff {t : ℝ} (ht : 0 < t) (g : G) :
    Commute g (psi t 1) ↔ g ∈ A := by
  have hr : Real.exp (-t) ≠ (Real.exp (-t))⁻¹ := by
    have h := (Real.exp_lt_exp.mpr (show -t < t by linarith)).ne
    simpa only [Real.exp_neg,inv_inv] using h
  have hp : (2:Q2)^(1:ℤ) ≠ ((2:Q2)^(1:ℤ))⁻¹ := by norm_num
  constructor
  · intro h
    exact ⟨(commute_diagonal_iff g.1 _ (Real.exp_ne_zero _) hr).mp (congrArg Prod.fst h.eq),
      (commute_diagonal_iff g.2 _ (zpow_ne_zero _ (by norm_num)) hp).mp (congrArg Prod.snd h.eq)⟩
  · intro h
    exact A_commute h (psi_mem_A t 1)

theorem centralizer_psi {t : ℝ} (ht : 0 < t) :
    {g : G | Commute g (psi t 1)} = (A : Set G) := by
  ext g
  exact commute_psi_iff ht g

abbrev Params (F : Type*) [Zero F] := F × ({a : F // a ≠ 0} × F)

def matrixOf {F : Type*} [Field F] (p : Params F) : SL(2,F) :=
  lower p.1 * BBEKDynamics.diagonal p.2.1.val p.2.1.property * upper p.2.2

@[simp] theorem matrixOf_00 {F : Type*} [Field F] (p : Params F) :
    matrixOf p 0 0 = p.2.1.val := by
  simp [matrixOf,lower,BBEKDynamics.diagonal,upper,Matrix.mul_apply,Fin.sum_univ_two]

@[simp] theorem matrixOf_01 {F : Type*} [Field F] (p : Params F) :
    matrixOf p 0 1 = p.2.1.val * p.2.2 := by
  simp [matrixOf,lower,BBEKDynamics.diagonal,upper,Matrix.mul_apply,Fin.sum_univ_two]

@[simp] theorem matrixOf_10 {F : Type*} [Field F] (p : Params F) :
    matrixOf p 1 0 = p.1 * p.2.1.val := by
  simp [matrixOf,lower,BBEKDynamics.diagonal,upper,Matrix.mul_apply,Fin.sum_univ_two]

def domain (F : Type*) [Field F] : Set SL(2,F) := {M | M 0 0 ≠ 0}

def coordinates {F : Type*} [Field F] (M : domain F) : Params F :=
  (M.val 1 0 / M.val 0 0, (⟨M.val 0 0,M.property⟩, M.val 0 1 / M.val 0 0))

def matrixInDomain {F : Type*} [Field F] (p : Params F) : domain F :=
  ⟨matrixOf p, by rw [domain,Set.mem_setOf_eq,matrixOf_00]; exact p.2.1.property⟩

theorem matrix_coordinates {F : Type*} [Field F] (M : domain F) :
    matrixInDomain (coordinates M) = M := by
  apply Subtype.ext
  exact (gaussian_factorization M.val M.property).symm

theorem coordinates_matrix {F : Type*} [Field F] (p : Params F) :
    coordinates (matrixInDomain p) = p := by
  rcases p with ⟨u,a,v⟩
  apply Prod.ext
  · simp [coordinates,matrixInDomain,a.property]
  · apply Prod.ext
    · apply Subtype.ext
      simp [coordinates,matrixInDomain]
    · simp [coordinates,matrixInDomain,a.property]

theorem matrixOf_injective {F : Type*} [Field F] : Function.Injective (matrixOf (F:=F)) := by
  intro p q h
  have he : matrixInDomain p = matrixInDomain q := Subtype.ext h
  simpa only [coordinates_matrix] using congrArg coordinates he

theorem isOpen_domain {F : Type*} [NormedField F] : IsOpen (domain F) := by
  exact (isClosed_eq (show Continuous (fun M : SL(2,F) => M 0 0) from
    (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val))
    continuous_const).isOpen_compl

theorem one_mem_domain {F : Type*} [Field F] : (1 : SL(2,F)) ∈ domain F := by
  simp [domain]

theorem continuous_coordinates {F : Type*} [NormedField F] :
    Continuous (coordinates (F:=F)) := by
  have hc (i j : Fin 2) : Continuous (fun M : domain F => M.val i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_subtype_val))
  exact (hc 1 0 |>.div (hc 0 0) (fun M => M.property)).prodMk
    ((hc 0 0 |>.subtype_mk (p := fun a : F => a ≠ 0) (fun M => M.property)).prodMk
      (hc 0 1 |>.div (hc 0 0) (fun M => M.property)))

theorem continuous_matrixOf {F : Type*} [NormedField F] :
    Continuous (matrixOf (F:=F)) := by
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_lower.comp continuous_fst
    · exact continuous_diagonal_map (by fun_prop) (fun p : Params F => p.2.1.property)
  · exact continuous_upper.comp (continuous_snd.comp continuous_snd)

/-- Genuine homeomorphic coordinates on the open big cell containing one. -/
def chart {F : Type*} [NormedField F] : domain F ≃ₜ Params F where
  toFun := coordinates
  invFun := matrixInDomain
  left_inv := matrix_coordinates
  right_inv := coordinates_matrix
  continuous_toFun := continuous_coordinates
  continuous_invFun := continuous_matrixOf.subtype_mk _

def conjugateParams {F : Type*} [Field F] (b : F) (p : Params F) : Params F :=
  (b⁻¹^2 * p.1, (p.2.1, b^2 * p.2.2))

theorem conjugate_matrixOf {F : Type*} [Field F] (b : F) (hb : b ≠ 0) (p : Params F) :
    BBEKDynamics.diagonal b hb * matrixOf p * (BBEKDynamics.diagonal b hb)⁻¹ =
      matrixOf (conjugateParams b p) := by
  rw [diagonal_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOf,conjugateParams,lower,BBEKDynamics.diagonal,upper,
      Matrix.mul_apply,Fin.sum_univ_two,hb,p.2.1.property]
  all_goals try field_simp [hb,p.2.1.property]
  all_goals try simp only [true_or]
  all_goals ring
  all_goals simp only [true_or]

def productDomain : Set G := domain ℝ ×ˢ domain Q2
abbrev GroupParams := Params ℝ × Params Q2

def groupMatrixOf (p : GroupParams) : G := (matrixOf p.1,matrixOf p.2)

def groupMatrixInDomain (p : GroupParams) : productDomain :=
  ⟨groupMatrixOf p, (matrixInDomain p.1).property, (matrixInDomain p.2).property⟩

def groupCoordinates (g : productDomain) : GroupParams :=
  (coordinates ⟨g.val.1,g.property.1⟩, coordinates ⟨g.val.2,g.property.2⟩)

theorem groupMatrix_coordinates (g : productDomain) :
    groupMatrixInDomain (groupCoordinates g) = g := by
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val (matrix_coordinates ⟨g.val.1,g.property.1⟩)
  · exact congrArg Subtype.val (matrix_coordinates ⟨g.val.2,g.property.2⟩)

theorem groupCoordinates_matrix (p : GroupParams) :
    groupCoordinates (groupMatrixInDomain p) = p := by
  apply Prod.ext
  · exact coordinates_matrix p.1
  · exact coordinates_matrix p.2

theorem continuous_groupMatrixOf : Continuous groupMatrixOf :=
  (continuous_matrixOf.comp continuous_fst).prodMk (continuous_matrixOf.comp continuous_snd)

theorem continuous_groupCoordinates : Continuous groupCoordinates := by
  apply Continuous.prodMk
  · exact continuous_coordinates.comp
      ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun g => g.property.1))
  · exact continuous_coordinates.comp
      ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun g => g.property.2))

/-- Continuous inverse coordinates on the actual open group neighborhood. -/
def groupChart : productDomain ≃ₜ GroupParams where
  toFun := groupCoordinates
  invFun := groupMatrixInDomain
  left_inv := groupMatrix_coordinates
  right_inv := groupCoordinates_matrix
  continuous_toFun := continuous_groupCoordinates
  continuous_invFun := continuous_groupMatrixOf.subtype_mk _

theorem isOpen_productDomain : IsOpen productDomain := isOpen_domain.prod isOpen_domain

theorem productDomain_mem_nhds_one : productDomain ∈ 𝓝 (1 : G) :=
  isOpen_productDomain.mem_nhds ⟨one_mem_domain,one_mem_domain⟩

theorem groupMatrixOf_injective : Function.Injective groupMatrixOf := by
  intro p q h
  exact Prod.ext (matrixOf_injective (congrArg Prod.fst h))
    (matrixOf_injective (congrArg Prod.snd h))

theorem existsUnique_factorization {g : G} (hg : g ∈ productDomain) :
    ∃! p : GroupParams, groupMatrixOf p = g := by
  refine ⟨groupCoordinates ⟨g,hg⟩, ?_, ?_⟩
  · exact congrArg Subtype.val (groupMatrix_coordinates ⟨g,hg⟩)
  · intro p hp
    apply groupMatrixOf_injective
    exact hp.trans (congrArg Subtype.val (groupMatrix_coordinates ⟨g,hg⟩)).symm

def psiParams (t : ℝ) (n : ℤ) (p : GroupParams) : GroupParams :=
  ((Real.exp (2*t)*p.1.1, (p.1.2.1, Real.exp (-2*t)*p.1.2.2)),
   ((2:Q2)^(-2*n)*p.2.1, (p.2.2.1, (2:Q2)^(2*n)*p.2.2.2)))

/-- Under diagonal conjugation, lower coordinates expand, upper coordinates
contract, and the two diagonal coordinates remain unchanged. -/
theorem psi_conjugate_coordinates (t : ℝ) (n : ℤ) (p : GroupParams) :
    psi t n * groupMatrixOf p * (psi t n)⁻¹ = groupMatrixOf (psiParams t n p) := by
  apply Prod.ext
  · change BBEKDynamics.diagonal (Real.exp (-t)) (Real.exp_ne_zero _) * matrixOf p.1 *
        (BBEKDynamics.diagonal (Real.exp (-t)) (Real.exp_ne_zero _))⁻¹ = _
    rw [conjugate_matrixOf]
    apply congrArg matrixOf
    apply Prod.ext
    · simp only [conjugateParams,psiParams,Real.exp_neg,inv_inv]
      rw [← Real.exp_nat_mul]
      congr 2
    · apply Prod.ext
      · rfl
      · change Real.exp (-t)^2 * p.1.2.2 = Real.exp (-2*t)*p.1.2.2
        rw [← Real.exp_nat_mul]
        congr 2
        ring
  · change BBEKDynamics.diagonal ((2:Q2)^n) (zpow_ne_zero _ (by norm_num)) * matrixOf p.2 *
        (BBEKDynamics.diagonal ((2:Q2)^n) (zpow_ne_zero _ (by norm_num)))⁻¹ = _
    rw [conjugate_matrixOf]
    apply congrArg matrixOf
    apply Prod.ext
    · change (((2:Q2)^n)⁻¹)^2 * p.2.1 = (2:Q2)^(-2*n)*p.2.1
      rw [← zpow_neg, ← zpow_natCast, ← zpow_mul]
      congr 2
      ring
    · apply Prod.ext
      · rfl
      · change ((2:Q2)^n)^2 * p.2.2.2 = (2:Q2)^(2*n)*p.2.2.2
        rw [← zpow_natCast, ← zpow_mul]
        congr 2
        ring

theorem psi_conjugate_mem_productDomain (t : ℝ) (n : ℤ) {g : G}
    (hg : g ∈ productDomain) : psi t n * g * (psi t n)⁻¹ ∈ productDomain := by
  obtain ⟨p,hp,_⟩ := existsUnique_factorization hg
  rw [← hp,psi_conjugate_coordinates]
  exact (groupMatrixInDomain (psiParams t n p)).property

theorem groupCoordinates_conjugate (t : ℝ) (n : ℤ) (g : productDomain) :
    groupCoordinates ⟨psi t n * g.val * (psi t n)⁻¹,
      psi_conjugate_mem_productDomain t n g.property⟩ = psiParams t n (groupCoordinates g) := by
  have hg : groupMatrixOf (groupCoordinates g) = g.val :=
    congrArg Subtype.val (groupMatrix_coordinates g)
  apply groupMatrixOf_injective
  rw [show groupMatrixOf (groupCoordinates ⟨psi t n * g.val * (psi t n)⁻¹,
      psi_conjugate_mem_productDomain t n g.property⟩) = psi t n * g.val * (psi t n)⁻¹ from
    congrArg Subtype.val (groupMatrix_coordinates _)]
  rw [← hg,psi_conjugate_coordinates]

end VV.BBEKGaussChart
