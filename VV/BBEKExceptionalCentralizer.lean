import VV.BBEKExceptionalFactorOrbit
import VV.BBEKSl2Shear
import VV.BBEKMautner

/-! The simultaneous centralizer of opposite roots has only a central
coordinate in the active factor. Its quotient orbit is an orbit of the other
local factor and cannot carry a probability invariant under that factor's
noncompact diagonal. This excludes the literal centralizer-concentration
endpoint, without a closed-orbit or reductive-presentation assumption. -/
noncomputable section
open Matrix Set MeasureTheory Function
open scoped MatrixGroups Topology
namespace VV.BBEKExceptionalCentralizer
open BBEKDynamics BBEKQuotient BBEKMautner BBEKSl2Shear BBEKExceptionalFactorOrbit
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The central negative identity, represented as a determinant-one matrix. -/
def negIdentity {F : Type*} [CommRing F] : SL(2,F) :=
  ⟨!![-1,0;0,-1],by simp [Matrix.det_fin_two]⟩

theorem negIdentity_commute {F : Type*} [CommRing F] (g : SL(2,F)) :
    negIdentity * g = g * negIdentity := by
  apply SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [negIdentity,Matrix.mul_apply,Fin.sum_univ_two]

theorem commutes_opposite_roots_iff {F : Type*} [Field F] (g : SL(2,F)) :
    ((∀ u : F, lower u * g = g * lower u) ∧
      (∀ u : F, BBEKFiniteQuotients.upper u * g = g * BBEKFiniteQuotients.upper u)) ↔
      g = 1 ∨ g = negIdentity := by
  constructor
  · rintro ⟨hl,hu⟩
    obtain ⟨h01,hdiag⟩ := (commutes_lower_iff g).mp hl
    obtain ⟨h10,_⟩ := (commutes_upper_iff g).mp hu
    have hdet := g.property
    rw [Matrix.det_fin_two,h01,h10,← hdiag] at hdet
    have hs : (g 0 0)^2 = 1 := by simpa only [pow_two,zero_mul,sub_zero] using hdet
    rcases sq_eq_one_iff.mp hs with he | he
    · left
      apply SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [h01,h10,← hdiag,he]
    · right
      apply SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [negIdentity,h01,h10,← hdiag,he]
  · rintro (rfl | rfl)
    · simp
    · exact ⟨fun u => (negIdentity_commute (lower u)).symm,
        fun u => (negIdentity_commute (BBEKFiniteQuotients.upper u)).symm⟩

def negPair : G := (negIdentity,negIdentity)

theorem negPair_mem_Gamma : negPair ∈ Gamma := by
  refine ⟨(negIdentity : SL(2,BBEKDyadic.dyadic)),?_⟩
  apply Prod.ext <;> apply SpecialLinearGroup.ext <;>
    intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalEmbedding,negIdentity,negPair,SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply]

theorem negPair_commute (g : G) : negPair * g = g * negPair :=
  Prod.ext (negIdentity_commute g.1) (negIdentity_commute g.2)

theorem negPair_smul (q : X) : negPair • q = q := by
  induction q using Quotient.inductionOn with
  | h M =>
    change negPair • mk M = mk M
    rw [smul_mk,negPair_commute]
    apply (mk_eq_iff _ _).mpr
    have he : (M * negPair)⁻¹ * M = negPair⁻¹ := by group
    rw [he]
    exact Gamma.inv_mem negPair_mem_Gamma

/-- Literal common centralizer of the lower and upper real root groups. -/
def realCommonCentralizer : Set G :=
  {g | (∀ u : ℝ, Commute (x u 0) g) ∧ (∀ u : ℝ, Commute (upperPoint u 0) g)}

/-- Literal common centralizer of the lower and upper 2-adic root groups. -/
def padicCommonCentralizer : Set G :=
  {g | (∀ u : Q2, Commute (x 0 u) g) ∧ (∀ u : Q2, Commute (upperPoint 0 u) g)}

def centralizerOrbit (S : Set G) (q : X) : Set X := (fun g : G => g • q) '' S

theorem realCommonCentralizer_first {g : G} (hg : g ∈ realCommonCentralizer) :
    g.1 = 1 ∨ g.1 = negIdentity := by
  apply (commutes_opposite_roots_iff g.1).mp
  exact ⟨fun u => congrArg Prod.fst (hg.1 u).eq,
    fun u => congrArg Prod.fst (hg.2 u).eq⟩

theorem padicCommonCentralizer_second {g : G} (hg : g ∈ padicCommonCentralizer) :
    g.2 = 1 ∨ g.2 = negIdentity := by
  apply (commutes_opposite_roots_iff g.2).mp
  exact ⟨fun u => congrArg Prod.snd (hg.1 u).eq,
    fun u => congrArg Prod.snd (hg.2 u).eq⟩

theorem real_centralizerOrbit_eq_factorOrbit (q : X) :
    centralizerOrbit realCommonCentralizer q = range (padicFactorOrbitMap q) := by
  ext z
  constructor
  · rintro ⟨g,hg,rfl⟩
    rcases realCommonCentralizer_first hg with hg1 | hg1
    · refine ⟨g.2,?_⟩
      simp only [padicFactorOrbitMap,← hg1,Prod.mk.eta]
    · refine ⟨g.2 * negIdentity,?_⟩
      have he : g * negPair = ((1 : SL(2,ℝ)),g.2 * negIdentity) := by
        apply Prod.ext
        · change g.1 * negIdentity = 1
          rw [hg1]
          apply SpecialLinearGroup.ext
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp [negIdentity,Matrix.mul_apply,Fin.sum_univ_two]
        · rfl
      change ((1 : SL(2,ℝ)),g.2 * negIdentity) • q = g • q
      rw [← he,MulAction.mul_smul,negPair_smul]
  · rintro ⟨h,rfl⟩
    refine ⟨(1,h),?_,rfl⟩
    constructor <;> intro u <;> change _ * _ = _ * _ <;> apply Prod.ext <;>
      simp [x,upperPoint,BBEKFiniteQuotients.upper_zero]

theorem padic_centralizerOrbit_eq_factorOrbit (q : X) :
    centralizerOrbit padicCommonCentralizer q = range (realFactorOrbitMap q) := by
  ext z
  constructor
  · rintro ⟨g,hg,rfl⟩
    rcases padicCommonCentralizer_second hg with hg2 | hg2
    · refine ⟨g.1,?_⟩
      simp only [realFactorOrbitMap,← hg2,Prod.mk.eta]
    · refine ⟨g.1 * negIdentity,?_⟩
      have he : g * negPair = (g.1 * negIdentity,(1 : SL(2,Q2))) := by
        apply Prod.ext
        · rfl
        · change g.2 * negIdentity = 1
          rw [hg2]
          apply SpecialLinearGroup.ext
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp [negIdentity,Matrix.mul_apply,Fin.sum_univ_two]
      change (g.1 * negIdentity,(1 : SL(2,Q2))) • q = g • q
      rw [← he,MulAction.mul_smul,negPair_smul]
  · rintro ⟨h,rfl⟩
    refine ⟨(h,1),?_,rfl⟩
    constructor <;> intro u <;> change _ * _ = _ * _ <;> apply Prod.ext <;>
      simp [x,upperPoint,BBEKFiniteQuotients.upper_zero]

/-- A real-root exceptional centralizer orbit cannot support a probability
invariant under the 2-adic diagonal contained in the kernel of the real root. -/
theorem no_real_centralizer_orbit_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X)
    (hT : MeasurePreserving (fun z : X =>
      ((1 : SL(2,ℝ)),diagonal (2 : Q2) (by norm_num)) • z) μ μ)
    (hmass : μ (centralizerOrbit realCommonCentralizer q) = 1) : False := by
  rw [real_centralizerOrbit_eq_factorOrbit] at hmass
  exact no_padic_factor_orbit_probability μ q hT hmass

/-- The symmetric 2-adic-root exceptional orbit is excluded by the real
kernel-of-root diagonal. -/
theorem no_padic_centralizer_orbit_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X)
    (hT : MeasurePreserving (fun z : X =>
      (diagonal (1/2 : ℝ) (by norm_num),(1 : SL(2,Q2))) • z) μ μ)
    (hmass : μ (centralizerOrbit padicCommonCentralizer q) = 1) : False := by
  rw [padic_centralizerOrbit_eq_factorOrbit] at hmass
  exact no_real_factor_orbit_probability μ q hT hmass

end VV.BBEKExceptionalCentralizer

