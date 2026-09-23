import VV.BBEKRationalReductive

/-! Conjugation and left translation for the exact periodic orbits appearing
in Theorem EL: g L(Q_S) Gamma. A non-rational g does not yield another
rational presentation; we instead prove every necessary local property
under the actual matrix conjugations. -/
noncomputable section
open Matrix MvPolynomial Set MulAction MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups Topology
namespace VV.BBEKReductiveConjugation
open BBEKAlgebraicTangent BBEKZariskiRoots BBEKMatrixReductive
open BBEKDiagonalDensity BBEKDiagonal BBEKDynamics BBEKQuotient
open BBEKRationalReductive

variable {K : Type*} [Field K]

def conjugated (L : Subgroup SL(2,K)) (g : SL(2,K)) : Subgroup SL(2,K) :=
  L.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_conjugated (L : Subgroup SL(2,K)) (g h : SL(2,K)) :
    h∈conjugated L g ↔ g⁻¹*h*g∈L := by
  simp only [conjugated,Subgroup.mem_comap,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv]

theorem conj_mem_conjugated (L : Subgroup SL(2,K)) (g h : SL(2,K)) :
    g*h*g⁻¹∈conjugated L g ↔ h∈L := by
  rw [mem_conjugated]
  simp [mul_assoc]

theorem conjugated_mono {L M : Subgroup SL(2,K)} (h : L≤M) (g : SL(2,K)) :
    conjugated L g ≤ conjugated M g := fun _ hx => h hx

theorem conjugated_inv (L : Subgroup SL(2,K)) (g : SL(2,K)) :
    conjugated (conjugated L g) g⁻¹=L := by
  ext h
  simp [mem_conjugated,mul_assoc]

theorem conjugated_bot (g : SL(2,K)) : conjugated (⊥ : Subgroup SL(2,K)) g=⊥ := by
  ext h
  change (MulAut.conj g⁻¹) h=1 ↔ h=1
  exact map_eq_one_iff (MulAut.conj g⁻¹) (MulAut.conj g⁻¹).injective

theorem conjugated_set_eq_image (L : Subgroup SL(2,K)) (g : SL(2,K)) :
    (conjugated L g : Set SL(2,K))=(fun h => g*h*g⁻¹) '' (L : Set SL(2,K)) := by
  ext h
  constructor
  · intro hh
    refine ⟨g⁻¹*h*g,(mem_conjugated L g h).mp hh,?_⟩
    simp [mul_assoc]
  · rintro ⟨h,hh,rfl⟩
    exact (conj_mem_conjugated L g h).mpr hh

theorem polynomialClosed_conj_preimage (g : SL(2,K)) {S : Set SL(2,K)}
    (hS : PolynomialClosed S) : PolynomialClosed ((fun h => g*h*g⁻¹) ⁻¹' S) := by
  obtain ⟨P,rfl⟩ := hS
  refine ⟨conjugationPullback g '' P,?_⟩
  ext h
  change (∀p∈P,eval (entries (g*h*g⁻¹).val) p=0) ↔ _
  constructor
  · intro hh p hp
    obtain ⟨q,hq,heq⟩ := hp
    change eval (entries h.val) p=0
    rw [← heq]
    rw [eval_conjugationPullback]
    exact hh q hq
  · intro hh p hp
    have he := hh _ ⟨p,hp,rfl⟩
    change eval (entries h.val) (conjugationPullback g p)=0 at he
    rw [eval_conjugationPullback] at he
    exact he

theorem continuous_zariski_conj (g : SL(2,K)) :
    @Continuous _ _ (zariski K) (zariski K) (fun h => g*h*g⁻¹) := by
  letI := zariski K
  apply continuous_iff_isClosed.mpr
  intro S hS
  exact (isClosed_zariski_iff _).mpr
    (polynomialClosed_conj_preimage g ((isClosed_zariski_iff S).mp hS))

theorem conjugated_polynomialClosed {L : Subgroup SL(2,K)}
    (hL : PolynomialClosed (L : Set SL(2,K))) (g : SL(2,K)) :
    PolynomialClosed (conjugated L g : Set SL(2,K)) := by
  have he : (conjugated L g : Set SL(2,K))=(fun h => g⁻¹*h*(g⁻¹)⁻¹) ⁻¹' (L : Set SL(2,K)) := rfl
  rw [he]
  exact polynomialClosed_conj_preimage g⁻¹ hL

theorem conjugated_connected {L : Subgroup SL(2,K)}
    (hL : @IsConnected _ (zariski K) (L : Set SL(2,K))) (g : SL(2,K)) :
    @IsConnected _ (zariski K) (conjugated L g : Set SL(2,K)) := by
  letI := zariski K
  rw [conjugated_set_eq_image]
  exact hL.image _ (continuous_zariski_conj g).continuousOn

theorem conjugated_normal {U L : Subgroup SL(2,K)} (hU : U≤L)
    (hn : (U.subgroupOf L).Normal) (g : SL(2,K)) :
    ((conjugated U g).subgroupOf (conjugated L g)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (conjugated_mono hU g)).mpr
  intro u l hu hl
  change (MulAut.conj g⁻¹) (l*u*l⁻¹) ∈ U
  simpa only [map_mul,map_inv] using
    (Subgroup.normal_subgroupOf_iff hU).mp hn _ _ hu hl

def matrixConj (g : SL(2,K)) : Mat2 K →+* Mat2 K where
  toFun M := g.val*M*(g⁻¹).val
  map_zero' := by simp
  map_add' := by intros; simp [Matrix.mul_add,Matrix.add_mul]
  map_one' := by
    simp only [Matrix.mul_one,← Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  map_mul' M N := by
    have hi : (g⁻¹).val*g.val=1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (g⁻¹).val g.val,hi,Matrix.one_mul]

theorem conjugate_unipotent {h : SL(2,K)} (hu : IsNilpotent (h.val-1))
    (g : SL(2,K)) : IsNilpotent ((g*h*g⁻¹).val-1) := by
  have he := hu.map (matrixConj g)
  simpa only [map_sub,map_one] using he

theorem conjugated_isReductive {L : Subgroup SL(2,K)} (hL : IsReductive L)
    (g : SL(2,K)) : IsReductive (conjugated L g) := by
  intro U hU hc hconn hn hu
  let V := conjugated U g⁻¹
  have hV : V≤L := by
    have he := conjugated_mono hU g⁻¹
    rwa [conjugated_inv] at he
  have hnV : (V.subgroupOf L).Normal := by
    have he := conjugated_normal hU hn g⁻¹
    rwa [conjugated_inv] at he
  have huV (v : SL(2,K)) (hv : v∈V) : IsNilpotent (v.val-1) := by
    have he : g*v*g⁻¹∈U := by
      simpa only [V,mem_conjugated,inv_inv] using hv
    have hz := conjugate_unipotent (hu _ he) g⁻¹
    simpa [mul_assoc] using hz
  have hbot := hL V hV (conjugated_polynomialClosed hc g⁻¹)
    (conjugated_connected hconn g⁻¹) hnV huV
  have he := congrArg (fun W => conjugated W g) hbot
  change conjugated V g=conjugated ⊥ g at he
  have hback : conjugated V g=U := by
    simpa only [inv_inv] using conjugated_inv U g⁻¹
  rwa [hback,conjugated_bot] at he

theorem conjugated_proper {L : Subgroup SL(2,K)} (hL : L≠⊤) (g : SL(2,K)) :
    conjugated L g≠⊤ := by
  intro he
  apply hL
  apply top_unique
  intro h _
  apply (conj_mem_conjugated L g h).mp
  rw [he]
  trivial

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

def translatedOrbit (L : RationalMatrixGroup) (g : G) : Set X :=
  (fun q : X => g • q) '' orbit L.localPoints (mk 1)

theorem translatedOrbit_eq (L : RationalMatrixGroup) (g : G) :
    translatedOrbit L g =
      orbit ((conjugated (L.points ℝ) g.1).prod (conjugated (L.points Q2) g.2)) (mk g) := by
  ext q
  constructor
  · rintro ⟨q,⟨l,hl⟩,rfl⟩
    change l.val • mk 1=q at hl
    have hlmem : g*l.val*g⁻¹∈
        (conjugated (L.points ℝ) g.1).prod (conjugated (L.points Q2) g.2) := by
      exact ⟨(conj_mem_conjugated _ _ _).mpr l.property.1,
        (conj_mem_conjugated _ _ _).mpr l.property.2⟩
    refine ⟨⟨g*l.val*g⁻¹,hlmem⟩,?_⟩
    change (g*l.val*g⁻¹) • mk g=g • q
    rw [← hl]
    simp [smul_mk,mul_assoc]
  · rintro ⟨l,hl⟩
    change l.val • mk g=q at hl
    have hlmem : g⁻¹*l.val*g∈L.localPoints := by
      exact ⟨(mem_conjugated _ _ _).mp l.property.1,
        (mem_conjugated _ _ _).mp l.property.2⟩
    refine ⟨(g⁻¹*l.val*g) • mk 1,⟨⟨g⁻¹*l.val*g,hlmem⟩,rfl⟩,?_⟩
    rw [← hl]
    simp [smul_mk,mul_assoc]

/-- Exact left-translated proper reductive orbit as written in Theorem EL.
Its conjugated local groups need not have rational coefficients; their
polynomiality, reductivity and properness are proved under conjugation. -/
theorem translated_reductive_orbit_entropy_zero
    (L : RationalMatrixGroup) (hproper : L.IsProper) (hred : L.IsGeometricallyReductive)
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul A X μ]
    (g : G) (hq : IsClosed (translatedOrbit L g))
    (hO : μ (translatedOrbit L g)=1)
    {C : Set X} (hC : IsCompact C) (hfull : μ C=1) (t : ℝ) (n : ℤ) :
    ErgodicTheory.Entropy.ksEntropy
      (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ)=0 := by
  rw [translatedOrbit_eq] at hq hO
  exact closed_reductive_orbit_entropy_zero μ
    (conjugated (L.points ℝ) g.1) (conjugated (L.points Q2) g.2)
    (conjugated_polynomialClosed (L.points_polynomialClosed ℝ) _)
    (conjugated_polynomialClosed (L.points_polynomialClosed Q2) _)
    (conjugated_proper (L.points_proper hproper ℝ) _)
    (conjugated_proper (L.points_proper hproper Q2) _)
    (conjugated_isReductive (hred ℝ) _) (conjugated_isReductive (hred Q2) _)
    (mk g) hq hO hC hfull t n

end VV.BBEKReductiveConjugation
