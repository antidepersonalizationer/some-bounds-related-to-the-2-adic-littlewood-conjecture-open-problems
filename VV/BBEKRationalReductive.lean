import VV.BBEKMatrixReductive

/-! A field-points presentation of a rational algebraic matrix subgroup.
One common family of rational polynomial equations defines every group of
points. Geometric reductivity is its usual normal-connected-unipotent
condition in all extension fields. Properness and the BBEK local-points
entropy exclusion are then proved, not supplied as additional premises. -/
noncomputable section
open Matrix MvPolynomial Set MulAction MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups Topology Polynomial
namespace VV.BBEKRationalReductive
open BBEKAlgebraicTangent BBEKNilpotentTangent BBEKZariskiRoots BBEKMatrixReductive
open BBEKDiagonalDensity BBEKDiagonal BBEKDynamics BBEKMahlerPadic BBEKQuotient
open BBEKSl2Reductive (E F)

/-- A rational algebraic subgroup of SL₂ in field-points form. Group closure
is part of the group object; the carrier is required to be exactly the
common rational polynomial zero set, in every characteristic-zero field. -/
structure RationalMatrixGroup where
  equations : Set (Polys ℚ)
  points (K : Type) [Field K] [CharZero K] : Subgroup SL(2,K)
  points_eq (K : Type) [Field K] [CharZero K] :
    (points K : Set SL(2,K))=
      {g | ∀p∈equations,eval₂ (Rat.castHom K) (entries g.val) p=0}

namespace RationalMatrixGroup

variable (L : RationalMatrixGroup)

theorem mem_points_iff (K : Type) [Field K] [CharZero K] (g : SL(2,K)) :
    g∈L.points K ↔ ∀p∈L.equations,eval₂ (Rat.castHom K) (entries g.val) p=0 := by
  change g∈(L.points K : Set SL(2,K)) ↔ _
  rw [L.points_eq K]
  rfl

theorem mem_rational_points_iff (g : SL(2,ℚ)) :
    g∈L.points ℚ ↔ ∀p∈L.equations,eval (entries g.val) p=0 := by
  rw [L.mem_points_iff]
  have he : Rat.castHom ℚ=RingHom.id ℚ := Subsingleton.elim _ _
  rw [he]
  rfl

/-- Naturality is forced by the common defining equations. No compatibility
between the separately packaged point groups is assumed. -/
theorem map_points_mem {K F : Type} [Field K] [CharZero K] [Field F] [CharZero F]
    (f : K →+* F) {g : SL(2,K)} (hg : g∈L.points K) :
    Matrix.SpecialLinearGroup.map f g∈L.points F := by
  rw [L.mem_points_iff] at hg ⊢
  intro p hp
  have he := congrArg f (hg p hp)
  rw [eval₂_comp_left,map_zero] at he
  have hf : f.comp (Rat.castHom K)=Rat.castHom F := Subsingleton.elim _ _
  rw [hf] at he
  exact he

theorem map_points_le {K F : Type} [Field K] [CharZero K] [Field F] [CharZero F]
    (f : K →+* F) :
    (L.points K).map (Matrix.SpecialLinearGroup.map f) ≤ L.points F := by
  rintro g ⟨h,hh,rfl⟩
  exact L.map_points_mem f hh

theorem points_polynomialClosed (K : Type) [Field K] [CharZero K] :
    PolynomialClosed (L.points K : Set SL(2,K)) := by
  refine ⟨MvPolynomial.map (Rat.castHom K) '' L.equations,?_⟩
  ext g
  change g∈L.points K ↔ _
  rw [L.mem_points_iff]
  simp only [matrixZeroSet,mem_setOf_eq,mem_image,forall_exists_index,and_imp]
  constructor
  · intro h p q hq hp
    rw [← hp,eval_map]
    exact h q hq
  · intro h p hp
    simpa only [eval_map,entries] using h _ p hp rfl

/-- Geometric reductivity is the absence of nontrivial connected normal
unipotent algebraic subgroups after every characteristic-zero field
extension. This is a definition in terms of the actual polynomial groups,
not a hypothesis about their Lie algebra or periodic-orbit behavior. -/
def IsGeometricallyReductive : Prop :=
  ∀ (K : Type) [Field K] [CharZero K], IsReductive (L.points K)

/-- Properness is detected on rational points. Its equivalence to
properness on every extension field is proved below. -/
def IsProper : Prop := L.points ℚ ≠ ⊤

theorem points_proper (hL : L.IsProper) (K : Type) [Field K] [CharZero K] :
    L.points K ≠ ⊤ := by
  intro htop
  apply hL
  apply top_unique
  intro g _
  rw [L.mem_rational_points_iff]
  intro p hp
  let gK := Matrix.SpecialLinearGroup.map (Rat.castHom K) g
  have hgK : gK ∈ L.points K := by rw [htop]; trivial
  have he := (L.mem_points_iff K gK).mp hgK p hp
  have hm : entries gK.val=(Rat.castHom K) ∘ entries g.val := rfl
  rw [hm,← eval₂_comp] at he
  exact (Rat.castHom K).injective (by simpa only [map_zero] using he)

theorem eval₂_curve (K : Type) [Field K] [CharZero K]
    (M : Mat2 ℚ) (p : Polys ℚ) (u : K) :
    (curve M p).eval₂ (Rat.castHom K) u =
      eval₂ (Rat.castHom K) (entries (1+u • M.map (Rat.castHom K))) p := by
  change (Polynomial.eval₂RingHom (Rat.castHom K) u)
    (eval₂ Polynomial.C (curveVariables M) p)=_
  rw [eval₂_comp_left]
  have hc : (Polynomial.eval₂RingHom (Rat.castHom K) u).comp Polynomial.C=Rat.castHom K := by
    ext a
    simp
  rw [hc]
  congr 1
  funext ij
  rcases ij with ⟨i,j⟩
  change (Polynomial.C (identityEntries (i,j))+Polynomial.C (M i j)*Polynomial.X).eval₂
    (Rat.castHom K) u = _
  rw [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
    Polynomial.eval₂_C,Polynomial.eval₂_X]
  change (Rat.castHom K) ((1 : Mat2 ℚ) i j)+(Rat.castHom K) (M i j)*u=
    (1 : Mat2 K) i j+u*(Rat.castHom K) (M i j)
  by_cases hij : i=j
  · subst j; simp [mul_comm]
  · simp [Matrix.one_apply,hij,mul_comm]

theorem root_polynomial_vanishes (M : Mat2 ℚ) (p : Polys ℚ)
    (hp : ∀u : ℚ, eval (entries (1+u • M)) p=0)
    (K : Type) [Field K] [CharZero K] (u : K) :
    eval₂ (Rat.castHom K) (entries (1+u • M.map (Rat.castHom K))) p=0 := by
  have hc : curve M p=0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_univ.mono
    intro v _
    change (curve M p).eval v=0
    rw [eval_curve]
    exact hp v
  rw [← eval₂_curve K M p u,hc,Polynomial.eval₂_zero]

theorem points_eq_top_of_rational_eq_top (hL : L.points ℚ=⊤)
    (K : Type) [Field K] [CharZero K] : L.points K=⊤ := by
  have hall (g : SL(2,ℚ)) : g ∈ L.points ℚ := by rw [hL]; trivial
  have hu (u : K) : upper u∈L.points K := by
    rw [L.mem_points_iff]
    intro p hp
    have hq (v : ℚ) : eval (entries (1+v • (E : Mat2 ℚ))) p=0 := by
      have hv := (L.mem_rational_points_iff (upper v)).mp (hall _) p hp
      have hm : 1+v • (E : Mat2 ℚ)=(upper v).val := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [E,upper]
      simpa only [hm] using hv
    have he := root_polynomial_vanishes E p hq K u
    have hm : 1+u • (E : Mat2 ℚ).map (Rat.castHom K)=(upper u).val := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [E,upper]
    simpa only [hm] using he
  have hl (u : K) : lower u∈L.points K := by
    rw [L.mem_points_iff]
    intro p hp
    have hq (v : ℚ) : eval (entries (1+v • (F : Mat2 ℚ))) p=0 := by
      have hv := (L.mem_rational_points_iff (lower v)).mp (hall _) p hp
      have hm : 1+v • (F : Mat2 ℚ)=(lower v).val := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [F,lower]
      simpa only [hm] using hv
    have he := root_polynomial_vanishes F p hq K u
    have hm : 1+u • (F : Mat2 ℚ).map (Rat.castHom K)=(lower u).val := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [F,lower]
    simpa only [hm] using he
  exact sl2_eq_top_of_unipotents (L.points K) hu hl

theorem proper_iff_points_proper (K : Type) [Field K] [CharZero K] :
    L.IsProper ↔ L.points K ≠ ⊤ := by
  constructor
  · intro hL; exact L.points_proper hL K
  · intro hL hQ
    exact hL (L.points_eq_top_of_rational_eq_top hQ K)

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

def localPoints : Subgroup G := (L.points ℝ).prod (L.points Q2)

theorem localPoints_isClosed : IsClosed (L.localPoints : Set G) := by
  change IsClosed ((L.points ℝ : Set SL(2,ℝ)) ×ˢ (L.points Q2 : Set SL(2,Q2)))
  obtain ⟨PR,hR⟩ := L.points_polynomialClosed ℝ
  obtain ⟨PP,hP⟩ := L.points_polynomialClosed Q2
  rw [hR,hP]
  exact (BBEKAlgebraicOrbit.matrixZeroSet_isClosed PR).prod
    (BBEKAlgebraicOrbit.matrixZeroSet_isClosed PP)

/-- The actual proper reductive rational periodic-orbit exclusion used in
BBEK. Properness, reductivity, and the defining equations belong to one
rational group; both local factors and their normalizer containment are
derived. The full KS entropy is zero on the ambient quotient. -/
theorem proper_reductive_periodic_orbit_entropy_zero
    (hproper : L.IsProper) (hred : L.IsGeometricallyReductive)
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul A X μ]
    (q : X) (hq : IsClosed (orbit L.localPoints q))
    (hO : μ (orbit L.localPoints q)=1)
    {C : Set X} (hC : IsCompact C) (hfull : μ C=1) (t : ℝ) (n : ℤ) :
    ErgodicTheory.Entropy.ksEntropy
      (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ)=0 :=
  closed_reductive_orbit_entropy_zero μ (L.points ℝ) (L.points Q2)
    (L.points_polynomialClosed ℝ) (L.points_polynomialClosed Q2)
    (L.points_proper hproper ℝ) (L.points_proper hproper Q2)
    (hred ℝ) (hred Q2) q hq hO hC hfull t n

theorem no_positive_entropy_proper_reductive_periodic_orbit
    (hproper : L.IsProper) (hred : L.IsGeometricallyReductive)
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul A X μ]
    (q : X) (hq : IsClosed (orbit L.localPoints q))
    (hO : μ (orbit L.localPoints q)=1)
    {C : Set X} (hC : IsCompact C) (hfull : μ C=1) (t : ℝ) (n : ℤ)
    (hpos : 0 < ErgodicTheory.Entropy.ksEntropy
      (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ)) : False := by
  rw [L.proper_reductive_periodic_orbit_entropy_zero hproper hred μ q hq hO hC hfull t n] at hpos
  exact lt_irrefl _ hpos

end RationalMatrixGroup

/-- A concrete nontrivial proper example of the rational group presentation. -/
def diagonalRationalGroup : RationalMatrixGroup where
  equations := {X (0,1),X (1,0)}
  points K := diagonalGroup K
  points_eq K := by
    intro _ _
    ext g
    simp [BBEKGaussChart.mem_diagonalGroup_iff,entries]

theorem diagonalRationalGroup_isReductive :
    diagonalRationalGroup.IsGeometricallyReductive := by
  intro K _ _
  exact diagonal_isReductive

theorem diagonalRationalGroup_isProper : diagonalRationalGroup.IsProper := by
  intro he
  change diagonalGroup ℚ=⊤ at he
  have hu : upper (1:ℚ) ∈ diagonalGroup ℚ := by rw [he]; trivial
  have hz := ((BBEKGaussChart.mem_diagonalGroup_iff _).mp hu).1
  norm_num [upper] at hz

end VV.BBEKRationalReductive


