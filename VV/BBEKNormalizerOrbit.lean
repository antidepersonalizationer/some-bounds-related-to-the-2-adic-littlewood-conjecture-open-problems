import VV.BBEKOpenOrbit
import VV.BBEKSl2Normalizer

/-! The actual finite Weyl extension of the diagonal group. -/
noncomputable section
open Matrix Set MulAction MeasureTheory MeasureTheory.Measure
open scoped Matrix MatrixGroups Topology
namespace VV.BBEKNormalizerOrbit
open BBEKDynamics BBEKDiagonal BBEKQuotient BBEKGaussChart BBEKPeriodicOrbit

def monomialGroup (K : Type*) [Field K] : Subgroup SL(2,K) where
  carrier := {g | (g 0 1=0 ∧ g 1 0=0) ∨ (g 0 0=0 ∧ g 1 1=0)}
  one_mem' := Or.inl (by simp)
  mul_mem' := by
    rintro g h (⟨hb,hc⟩ | ⟨ha,hd⟩) (⟨hb',hc'⟩ | ⟨ha',hd'⟩)
    · left; simp [Matrix.mul_apply,Fin.sum_univ_two,hb,hc,hb',hc']
    · right; simp [Matrix.mul_apply,Fin.sum_univ_two,hb,hc,ha',hd']
    · right; simp [Matrix.mul_apply,Fin.sum_univ_two,ha,hd,hb',hc']
    · left; simp [Matrix.mul_apply,Fin.sum_univ_two,ha,hd,ha',hd']
  inv_mem' := by
    rintro g (⟨hb,hc⟩ | ⟨ha,hd⟩)
    · left; simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,hb,hc]
    · right; simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,ha,hd]

theorem diagonal_le_monomial {K : Type*} [Field K] : diagonalGroup K ≤ monomialGroup K :=
  fun g hg => Or.inl ((mem_diagonalGroup_iff g).mp hg)

theorem conjugate_diagonal_mem {K : Type*} [Field K] {g h : SL(2,K)}
    (hg : g ∈ monomialGroup K) (hh : h ∈ diagonalGroup K) :
    g*h*g⁻¹ ∈ diagonalGroup K := by
  obtain ⟨hb,hc⟩ := (mem_diagonalGroup_iff h).mp hh
  apply (mem_diagonalGroup_iff _).mpr
  rcases hg with ⟨gb,gc⟩ | ⟨ga,gd⟩
  · simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,hb,hc,gb,gc]
  · simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,hb,hc,ga,gd]

theorem monomial_le_normalizer {K : Type*} [Field K] :
    monomialGroup K ≤ (diagonalGroup K).normalizer := by
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro h
  constructor
  · exact conjugate_diagonal_mem hg
  · intro hh
    have he := conjugate_diagonal_mem ((monomialGroup K).inv_mem hg) hh
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using he

/-- In characteristic zero this is exactly the group-theoretic normalizer,
not merely a convenient finite extension containing the diagonal group. -/
theorem monomial_eq_normalizer {K : Type*} [Field K] [CharZero K] :
    monomialGroup K = (diagonalGroup K).normalizer := by
  apply le_antisymm monomial_le_normalizer
  intro g hg
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hconj := (Subgroup.mem_normalizer_iff.mp hg
    (BBEKDynamics.diagonal (2:K) (by norm_num))).mp ⟨2,by norm_num,rfl⟩
  obtain ⟨hb,hc⟩ := (mem_diagonalGroup_iff _).mp hconj
  simp [BBEKDynamics.diagonal,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Matrix.vecMul,vecHead,vecTail,Fin.sum_univ_two] at hb hc
  have hab : g 0 0*g 0 1=0 := by linear_combination (-2/3:K)*hb
  have hcd : g 1 0*g 1 1=0 := by linear_combination (2/3:K)*hc
  by_cases ha : g 0 0=0
  · right
    have hcn : g 1 0 ≠ 0 := by
      intro hz
      simp [ha,hz] at hd
    exact ⟨ha,(mul_eq_zero.mp hcd).resolve_left hcn⟩
  · left
    have hb' : g 0 1=0 := (mul_eq_zero.mp hab).resolve_left ha
    have hdn : g 1 1 ≠ 0 := by
      intro hz
      simp [hb',hz] at hd
    exact ⟨hb',(mul_eq_zero.mp hcd).resolve_right hdn⟩

def weyl (K : Type*) [Field K] : SL(2,K) :=
  ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

def weylChoice (K : Type*) [Field K] (b : Bool) : SL(2,K) := if b then weyl K else 1

theorem weylChoice_mem {K : Type*} [Field K] (b : Bool) :
    weylChoice K b ∈ monomialGroup K := by
  cases b
  · exact (monomialGroup K).one_mem
  · exact Or.inr (by simp [weylChoice,weyl])

theorem monomial_decomposition {K : Type*} [Field K] {g : SL(2,K)}
    (hg : g ∈ monomialGroup K) :
    ∃ b : Bool, ∃ a : SL(2,K), a ∈ diagonalGroup K ∧ g=a*weylChoice K b := by
  rcases hg with hdiag | ⟨ha,hd⟩
  · exact ⟨false,g,(mem_diagonalGroup_iff g).mpr hdiag,by simp [weylChoice]⟩
  · refine ⟨true,g*(weyl K)⁻¹,?_,by simp [weylChoice]⟩
    apply (mem_diagonalGroup_iff _).mpr
    simp [weyl,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,ha,hd]

theorem monomial_isClosed {K : Type*} [NormedField K] :
    IsClosed (monomialGroup K : Set SL(2,K)) := by
  have hc (i j : Fin 2) : Continuous (fun g : SL(2,K) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact ((isClosed_eq (hc 0 1) continuous_const).inter
    (isClosed_eq (hc 1 0) continuous_const)).union
      ((isClosed_eq (hc 0 0) continuous_const).inter (isClosed_eq (hc 1 1) continuous_const))

theorem diagonal_iff_entry_ne_zero {K : Type*} [Field K]
    {g : SL(2,K)} (hg : g ∈ monomialGroup K) :
    g ∈ diagonalGroup K ↔ g 0 0 ≠ 0 := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    simpa [BBEKDynamics.diagonal] using ha
  · intro ha
    rcases hg with h | h
    · exact (mem_diagonalGroup_iff g).mpr h
    · exact (ha h.1).elim

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def N : Subgroup G := (monomialGroup ℝ).prod (monomialGroup Q2)

theorem N_eq_normalizer : N = A.normalizer := by
  apply le_antisymm
  · intro g hg
    have hgr := monomial_le_normalizer hg.1
    have hgp := monomial_le_normalizer hg.2
    apply Subgroup.mem_normalizer_iff.mpr
    intro h
    exact and_congr (Subgroup.mem_normalizer_iff.mp hgr h.1)
      (Subgroup.mem_normalizer_iff.mp hgp h.2)
  · intro g hg
    change g.1 ∈ monomialGroup ℝ ∧ g.2 ∈ monomialGroup Q2
    rw [monomial_eq_normalizer,monomial_eq_normalizer]
    constructor
    · apply Subgroup.mem_normalizer_iff.mpr
      intro h
      constructor
      · intro hh
        exact ((Subgroup.mem_normalizer_iff.mp hg (h,1)).mp ⟨hh,(diagonalGroup Q2).one_mem⟩).1
      · intro hh
        exact ((Subgroup.mem_normalizer_iff.mp hg (h,1)).mpr ⟨hh,by simpa using (diagonalGroup Q2).one_mem⟩).1
    · apply Subgroup.mem_normalizer_iff.mpr
      intro h
      constructor
      · intro hh
        exact ((Subgroup.mem_normalizer_iff.mp hg (1,h)).mp ⟨(diagonalGroup ℝ).one_mem,hh⟩).2
      · intro hh
        exact ((Subgroup.mem_normalizer_iff.mp hg (1,h)).mpr ⟨by simpa using (diagonalGroup ℝ).one_mem,hh⟩).2

theorem A_le_N : A ≤ N := fun g hg =>
  ⟨diagonal_le_monomial hg.1,diagonal_le_monomial hg.2⟩

theorem N_isClosed : IsClosed (N : Set G) := monomial_isClosed.prod monomial_isClosed

instance N_sigmaCompact : SigmaCompactSpace N := N_isClosed.sigmaCompactSpace

def diagonalInN : Subgroup N := A.comap N.subtype

theorem diagonalInN_isOpen : IsOpen (diagonalInN : Set N) := by
  have he : (diagonalInN : Set N) =
      {g : N | g.val.1 0 0 ≠ 0} ∩ {g : N | g.val.2 0 0 ≠ 0} := by
    ext g
    exact and_congr (diagonal_iff_entry_ne_zero g.property.1)
      (diagonal_iff_entry_ne_zero g.property.2)
  rw [he]
  have hr : Continuous (fun g : N => g.val.1 0 0) :=
    (continuous_apply 0).comp ((continuous_apply 0).comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)))
  have hp : Continuous (fun g : N => g.val.2 0 0) :=
    (continuous_apply 0).comp ((continuous_apply 0).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)))
  exact (isClosed_eq hr continuous_const).isOpen_compl.inter (isClosed_eq hp continuous_const).isOpen_compl

theorem orbit_diagonalInN (q : X) : orbit diagonalInN q = orbit A q := by
  ext z
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨⟨a.val.val,a.property⟩,ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨⟨⟨a.val,A_le_N a.property⟩,a.property⟩,ha⟩

theorem closed_A_orbit_of_closed_N_orbit (q : X) (hq : IsClosed (orbit N q)) :
    IsClosed (orbit A q) := by
  rw [← orbit_diagonalInN q]
  exact BBEKOpenOrbit.closed_subgroup_orbit diagonalInN diagonalInN_isOpen q hq

def weylPair (b : Bool × Bool) : G := (weylChoice ℝ b.1,weylChoice Q2 b.2)

theorem weylPair_mem (b : Bool × Bool) : weylPair b ∈ N :=
  ⟨weylChoice_mem b.1,weylChoice_mem b.2⟩

theorem orbit_N_eq (q : X) : orbit N q = ⋃ b : Bool × Bool, orbit A (weylPair b • q) := by
  ext z
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨b,a,ha,he⟩ := monomial_decomposition g.property.1
    obtain ⟨c,d,hd,hf⟩ := monomial_decomposition g.property.2
    refine mem_iUnion.mpr ⟨(b,c),⟨⟨(a,d),ha,hd⟩,?_⟩⟩
    change (a,d) • (weylPair (b,c) • q) = g.val • q
    rw [← MulAction.mul_smul]
    congr 1
    exact Prod.ext he.symm hf.symm
  · intro hz
    obtain ⟨b,a,ha⟩ := mem_iUnion.mp hz
    refine ⟨⟨a.val*weylPair b,N.mul_mem (A_le_N a.property) (weylPair_mem b)⟩,?_⟩
    simpa only [subgroup_smul_def,MulAction.mul_smul] using ha

local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- The full finite Weyl-extension periodic-orbit exclusion on G/Gamma.
Only the big orbit's closedness is required; closedness and compactness of
the diagonal components are proved using open orbits and full support. -/
theorem closed_N_orbit_entropy_zero_on_quotient
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul A X μ]
    (q : X) (hq : IsClosed (orbit N q)) (hO : μ (orbit N q)=1)
    {C : Set X} (hC : IsCompact C) (hfull : μ C=1) (t : ℝ) (n : ℤ) :
    ErgodicTheory.Entropy.ksEntropy
      (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ)=0 := by
  apply countable_closed_A_orbits_entropy_zero_on_quotient μ
    (fun b : Bool × Bool => weylPair b • q) _ _ hC hfull t n
  · intro b
    apply closed_A_orbit_of_closed_N_orbit
    change IsClosed (orbit N ((⟨weylPair b,weylPair_mem b⟩ : N) • q))
    simpa only [orbit_smul] using hq
  · rwa [← orbit_N_eq]

end VV.BBEKNormalizerOrbit



