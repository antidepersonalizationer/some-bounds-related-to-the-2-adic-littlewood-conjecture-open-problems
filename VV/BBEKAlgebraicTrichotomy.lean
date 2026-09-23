import VV.BBEKNilpotentTangent

/-! A classification of proper polynomial matrix subgroups containing the
split torus. The two non-toral alternatives contain actual normal root groups;
no reductivity-to-Lie-algebra premise is used. -/
noncomputable section
open Matrix MvPolynomial
open scoped MatrixGroups
namespace VV.BBEKAlgebraicTrichotomy
open BBEKAlgebraicTangent BBEKTangentLie BBEKNilpotentTangent
open BBEKDiagonalDensity BBEKDiagonal BBEKNormalizerOrbit
open BBEKDynamics BBEKMahlerPadic
open BBEKSl2Reductive (E F H)

variable {K : Type*} [Field K]

def upperRoot (K : Type*) [Field K] : Subgroup SL(2,K) where
  carrier := {g | g 0 0=1 ∧ g 1 0=0 ∧ g 1 1=1}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨ha,hc,hd⟩ ⟨ha',hc',hd'⟩
    simp [Matrix.mul_apply,Fin.sum_univ_two,ha,hc,hd,ha',hc',hd']
  inv_mem' := by
    rintro g ⟨ha,hc,hd⟩
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,ha,hc,hd]

def lowerRoot (K : Type*) [Field K] : Subgroup SL(2,K) where
  carrier := {g | g 0 0=1 ∧ g 0 1=0 ∧ g 1 1=1}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨ha,hb,hd⟩ ⟨ha',hb',hd'⟩
    simp [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,hd,ha',hb',hd']
  inv_mem' := by
    rintro g ⟨ha,hb,hd⟩
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,ha,hb,hd]

theorem mem_upperRoot_iff (g : SL(2,K)) : g ∈ upperRoot K ↔ ∃u, g=upper u := by
  constructor
  · rintro ⟨ha,hc,hd⟩
    refine ⟨g 0 1,?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper,ha,hc,hd]
  · rintro ⟨u,rfl⟩
    simp [upperRoot,upper]

theorem mem_lowerRoot_iff (g : SL(2,K)) : g ∈ lowerRoot K ↔ ∃u, g=lower u := by
  constructor
  · rintro ⟨ha,hb,hd⟩
    refine ⟨g 1 0,?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lower,ha,hb,hd]
  · rintro ⟨u,rfl⟩
    simp [lowerRoot,lower]

theorem upper_conjugate_of_lower_zero (g : SL(2,K)) (hg : g 1 0=0) (u : K) :
    g*upper u*g⁻¹=upper (g 0 0^2*u) := by
  have hd : g 0 0*g 1 1=1 := by
    have he : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
    simpa only [hg,mul_zero,zero_mul,sub_zero] using he
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,hg,hd,mul_comm (g 1 1) (g 0 0)] <;> ring

theorem lower_conjugate_of_upper_zero (g : SL(2,K)) (hg : g 0 1=0) (u : K) :
    g*lower u*g⁻¹=lower (g 1 1^2*u) := by
  have hd : g 0 0*g 1 1=1 := by
    have he : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
    simpa only [hg,mul_zero,zero_mul,sub_zero] using he
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,hg,hd,mul_comm (g 1 1) (g 0 0)] <;> ring

theorem upper_normalizer_of_lower_zero {g : SL(2,K)} (hg : g 1 0=0) :
    g ∈ (upperRoot K).normalizer := by
  have hconj (a : SL(2,K)) (ha : a 1 0=0) (b : SL(2,K))
      (hb : b ∈ upperRoot K) : a*b*a⁻¹ ∈ upperRoot K := by
    obtain ⟨u,rfl⟩ := (mem_upperRoot_iff b).mp hb
    rw [upper_conjugate_of_lower_zero a ha]
    exact (mem_upperRoot_iff _).mpr ⟨_,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro b
  constructor
  · exact hconj g hg b
  · intro hb
    have hinv : g⁻¹ 1 0=0 := by
      simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,hg]
    have he := hconj g⁻¹ hinv _ hb
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using he

theorem lower_normalizer_of_upper_zero {g : SL(2,K)} (hg : g 0 1=0) :
    g ∈ (lowerRoot K).normalizer := by
  have hconj (a : SL(2,K)) (ha : a 0 1=0) (b : SL(2,K))
      (hb : b ∈ lowerRoot K) : a*b*a⁻¹ ∈ lowerRoot K := by
    obtain ⟨u,rfl⟩ := (mem_lowerRoot_iff b).mp hb
    rw [lower_conjugate_of_upper_zero a ha]
    exact (mem_lowerRoot_iff _).mpr ⟨_,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro b
  constructor
  · exact hconj g hg b
  · intro hb
    have hinv : g⁻¹ 0 1=0 := by
      simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,hg]
    have he := hconj g⁻¹ hinv _ hb
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using he

variable [CharZero K]

theorem tangent_roots_not_both (L : Subgroup SL(2,K)) (P : Set (Polys K))
    (hL : (L : Set SL(2,K))=matrixZeroSet P) (hproper : L ≠ ⊤)
    (hE : E ∈ tangentLie L) : F ∉ tangentLie L := by
  intro hF
  exact hproper (sl2_eq_top_of_unipotents L
    (upper_mem_of_E_tangent L P hL hE) (lower_mem_of_F_tangent L P hL hF))

theorem upper_triangular_of_E_mem (L : Subgroup SL(2,K))
    (hD : diagonalGroup K ≤ L) (hE : E ∈ tangentLie L) (hF : F ∉ tangentLie L)
    {g : SL(2,K)} (hg : g ∈ L) : g 1 0=0 := by
  have hm := tangent_adjoint_mem L hg hE
  have hz : (g.val*(E : Mat2 K)*(g⁻¹).val) 1 0=0 := by
    by_contra hc
    exact hF (BBEKSl2Reductive.F_mem_of_lower_ne_zero (tangentLie L)
      (H_mem_tangentLie L hD) hm hc)
  have he : g 1 0*g 1 0=0 := by
    simpa [E,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two] using hz
  exact (mul_self_eq_zero.mp he)

theorem lower_triangular_of_F_mem (L : Subgroup SL(2,K))
    (hD : diagonalGroup K ≤ L) (hE : E ∉ tangentLie L) (hF : F ∈ tangentLie L)
    {g : SL(2,K)} (hg : g ∈ L) : g 0 1=0 := by
  have hm := tangent_adjoint_mem L hg hF
  have hz : (g.val*(F : Mat2 K)*(g⁻¹).val) 0 1=0 := by
    by_contra hb
    exact hE (BBEKSl2Reductive.E_mem_of_upper_ne_zero (tangentLie L)
      (H_mem_tangentLie L hD) hm hb)
  have he : g 0 1*g 0 1=0 := by
    simpa [F,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two] using hz
  exact (mul_self_eq_zero.mp he)

theorem monomial_of_no_tangent_roots (L : Subgroup SL(2,K))
    (hD : diagonalGroup K ≤ L) (hE : E ∉ tangentLie L) (hF : F ∉ tangentLie L) :
    L ≤ monomialGroup K := by
  have hline {M : Mat2 K} (hM : M ∈ tangentLie L) : M=M 0 0 • H := by
    have hb : M 0 1=0 := by
      by_contra hb
      exact hE (BBEKSl2Reductive.E_mem_of_upper_ne_zero (tangentLie L)
        (H_mem_tangentLie L hD) hM hb)
    have hc : M 1 0=0 := by
      by_contra hc
      exact hF (BBEKSl2Reductive.F_mem_of_lower_ne_zero (tangentLie L)
        (H_mem_tangentLie L hD) hM hc)
    simpa only [hb,hc,zero_smul,add_zero] using
      BBEKSl2Reductive.traceZero_decomposition M (tangent_trace_zero L hM)
  intro g hg
  have hp := hline (tangent_adjoint_mem L hg (H_mem_tangentLie L hD))
  apply BBEKSl2Normalizer.diagonal_or_antidiagonal g ((g.val*(H : Mat2 K)*(g⁻¹).val) 0 0)
  have he := congrArg (fun M : Mat2 K => M*g.val) hp
  simpa only [Matrix.mul_assoc,← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.mul_one,
    Matrix.smul_mul] using he

/-- A proper polynomial subgroup containing the split torus either normalizes
the torus, or has a complete root group as a nontrivial normal subgroup. -/
theorem proper_polynomial_trichotomy (L : Subgroup SL(2,K)) (P : Set (Polys K))
    (hL : (L : Set SL(2,K))=matrixZeroSet P) (hproper : L ≠ ⊤)
    (hD : diagonalGroup K ≤ L) :
    L ≤ (diagonalGroup K).normalizer ∨
      (upperRoot K ≤ L ∧ ((upperRoot K).subgroupOf L).Normal) ∨
      (lowerRoot K ≤ L ∧ ((lowerRoot K).subgroupOf L).Normal) := by
  by_cases hE : E ∈ tangentLie L
  · have hF := tangent_roots_not_both L P hL hproper hE
    right; left
    constructor
    · intro g hg
      obtain ⟨u,rfl⟩ := (mem_upperRoot_iff g).mp hg
      exact upper_mem_of_E_tangent L P hL hE u
    · apply Subgroup.normal_subgroupOf_of_le_normalizer
      intro g hg
      exact upper_normalizer_of_lower_zero (upper_triangular_of_E_mem L hD hE hF hg)
  · by_cases hF : F ∈ tangentLie L
    · right; right
      constructor
      · intro g hg
        obtain ⟨u,rfl⟩ := (mem_lowerRoot_iff g).mp hg
        exact lower_mem_of_F_tangent L P hL hF u
      · apply Subgroup.normal_subgroupOf_of_le_normalizer
        intro g hg
        exact lower_normalizer_of_upper_zero (lower_triangular_of_F_mem L hD hE hF hg)
    · exact Or.inl ((monomial_of_no_tangent_roots L hD hE hF).trans monomial_le_normalizer)

end VV.BBEKAlgebraicTrichotomy

