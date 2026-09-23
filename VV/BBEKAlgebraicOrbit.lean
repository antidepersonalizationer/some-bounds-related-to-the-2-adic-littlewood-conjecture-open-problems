import VV.BBEKDiagonalDensity
import Mathlib.Topology.Algebra.MvPolynomial

/-! Orbit invariance forces full diagonal containment for actual local
matrix subgroups defined by polynomial equations. -/
noncomputable section
open Set Matrix MeasureTheory MeasureTheory.Measure MulAction
open scoped Topology MatrixGroups
namespace VV.BBEKAlgebraicOrbit
open BBEKDynamics BBEKDiagonal BBEKQuotient BBEKDiagonalDensity BBEKOrbitBaire

theorem matrixZeroSet_isClosed {F : Type*} [NormedField F]
    (P : Set (MvPolynomial (Fin 2 × Fin 2) F)) : IsClosed (matrixZeroSet P) := by
  have hc : Continuous (fun g : SL(2,F) => fun ij : Fin 2 × Fin 2 => g ij.1 ij.2) :=
    continuous_pi (fun ij => (continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp continuous_subtype_val))
  simp only [matrixZeroSet,setOf_forall]
  exact isClosed_iInter (fun p => isClosed_iInter (fun _ =>
    isClosed_eq (p.continuous_eval.comp hc) continuous_const))

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def realDiagonalInA (a : ℝˣ) : A :=
  ⟨(unitDiagonalMatrix a,1),⟨a.val,a.ne_zero,rfl⟩,(diagonalGroup Q2).one_mem⟩

def padicDiagonalInA (a : Q2ˣ) : A :=
  ⟨(1,unitDiagonalMatrix a),(diagonalGroup ℝ).one_mem,⟨a.val,a.ne_zero,rfl⟩⟩

theorem continuous_realDiagonalInA : Continuous realDiagonalInA := by
  apply Continuous.subtype_mk
  exact (continuous_diagonal_map Units.continuous_val (fun a : ℝˣ => a.ne_zero)).prodMk
    continuous_const

theorem continuous_padicDiagonalInA : Continuous padicDiagonalInA := by
  apply Continuous.subtype_mk
  exact continuous_const.prodMk
    (continuous_diagonal_map Units.continuous_val (fun a : Q2ˣ => a.ne_zero))

@[simp] theorem realDiagonalInA_one : realDiagonalInA 1=1 := by
  apply Subtype.ext
  simp [realDiagonalInA,unitDiagonalMatrix,BBEKDynamics.diagonal_one]

@[simp] theorem padicDiagonalInA_one : padicDiagonalInA 1=1 := by
  apply Subtype.ext
  simp [padicDiagonalInA,unitDiagonalMatrix,BBEKDynamics.diagonal_one]

theorem diagonal_le_of_open_polynomial_intersection
    (LR : Subgroup SL(2,ℝ)) (LP : Subgroup SL(2,Q2))
    (PR : Set (MvPolynomial (Fin 2 × Fin 2) ℝ))
    (PP : Set (MvPolynomial (Fin 2 × Fin 2) Q2))
    (hR : (LR : Set SL(2,ℝ))=matrixZeroSet PR)
    (hP : (LP : Set SL(2,Q2))=matrixZeroSet PP)
    (hopen : IsOpen ((LR.prod LP).comap A.subtype : Set A)) : A ≤ LR.prod LP := by
  have hN := hopen.mem_nhds ((LR.prod LP).comap A.subtype).one_mem
  have hRnhds : {a : ℝˣ | unitDiagonalMatrix a ∈ matrixZeroSet PR} ∈ 𝓝 1 := by
    have hh : realDiagonalInA ⁻¹' ((LR.prod LP).comap A.subtype : Set A) ∈ 𝓝 (1:ℝˣ) := continuous_realDiagonalInA.continuousAt
      (by simpa only [realDiagonalInA_one] using hN)
    have he : realDiagonalInA ⁻¹' ((LR.prod LP).comap A.subtype : Set A) =
        {a : ℝˣ | unitDiagonalMatrix a ∈ matrixZeroSet PR} := by
      ext a
      change (unitDiagonalMatrix a ∈ LR ∧ 1 ∈ LP) ↔ _
      simp only [LP.one_mem,and_true]
      rw [← hR]
      rfl
    rwa [he] at hh
  have hPnhds : {a : Q2ˣ | unitDiagonalMatrix a ∈ matrixZeroSet PP} ∈ 𝓝 1 := by
    have hh : padicDiagonalInA ⁻¹' ((LR.prod LP).comap A.subtype : Set A) ∈ 𝓝 (1:Q2ˣ) := continuous_padicDiagonalInA.continuousAt
      (by simpa only [padicDiagonalInA_one] using hN)
    have he : padicDiagonalInA ⁻¹' ((LR.prod LP).comap A.subtype : Set A) =
        {a : Q2ˣ | unitDiagonalMatrix a ∈ matrixZeroSet PP} := by
      ext a
      change (1 ∈ LR ∧ unitDiagonalMatrix a ∈ LP) ↔ _
      simp only [LR.one_mem,true_and]
      rw [← hP]
      rfl
    rwa [he] at hh
  have hallR := diagonal_subset_zeroSet_of_nhds PR hRnhds
  have hallP := diagonal_subset_zeroSet_of_nhds PP hPnhds
  intro g hg
  rcases hg with ⟨⟨a,ha,he⟩,⟨b,hb,hf⟩⟩
  constructor
  · change g.1 ∈ (LR : Set SL(2,ℝ))
    rw [hR,he]
    exact hallR (Units.mk0 a ha)
  · change g.2 ∈ (LP : Set SL(2,Q2))
    rw [hP,hf]
    exact hallP (Units.mk0 b hb)

local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- The local-points form needed for an algebraic Q-subgroup in the real and
2-adic factors. The defining polynomial equations are the actual input;
Zariski density, A-containment and orbit-support invariance are all proved. -/
theorem diagonal_le_of_closed_polynomial_orbit
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    (LR : Subgroup SL(2,ℝ)) (LP : Subgroup SL(2,Q2))
    (PR : Set (MvPolynomial (Fin 2 × Fin 2) ℝ))
    (PP : Set (MvPolynomial (Fin 2 × Fin 2) Q2))
    (hR : (LR : Set SL(2,ℝ))=matrixZeroSet PR)
    (hP : (LP : Set SL(2,Q2))=matrixZeroSet PP)
    (q : X) (hq : IsClosed (orbit (LR.prod LP) q))
    (hμq : μ (orbit (LR.prod LP) q)=1) : A ≤ LR.prod LP := by
  apply diagonal_le_of_open_polynomial_intersection LR LP PR PP hR hP
  apply diagonal_intersection_isOpen_of_closed_full_orbit μ (LR.prod LP) _ q hq hμq
  change IsClosed ((LR : Set SL(2,ℝ)) ×ˢ (LP : Set SL(2,Q2)))
  rw [hR,hP]
  exact (matrixZeroSet_isClosed PR).prod (matrixZeroSet_isClosed PP)

end VV.BBEKAlgebraicOrbit


