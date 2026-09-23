import VV.BBEKParameter
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
The compact part of the full split diagonal group in BBEK Section 5.
Every diagonal element is a product of an actual psi(t,n) and a member
of the compact norm-one diagonal subgroup. This gives a concrete compact
group over which the averaging argument can integrate.
-/

noncomputable section
open Matrix Metric Set
open scoped MatrixGroups Topology

namespace VV.BBEKDiagonal
open BBEKDynamics
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def diagonalGroup (K : Type*) [Field K] : Subgroup SL(2,K) where
  carrier := {g | ∃ a : K, ∃ ha : a ≠ 0, g = BBEKDynamics.diagonal a ha}
  one_mem' := ⟨1, one_ne_zero, diagonal_one.symm⟩
  mul_mem' := by
    rintro g h ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    exact ⟨a*b,mul_ne_zero ha hb,(diagonal_mul a b ha hb).symm⟩
  inv_mem' := by
    rintro g ⟨a,ha,rfl⟩
    exact ⟨a⁻¹,inv_ne_zero ha,diagonal_inv a ha⟩

def unitDiagonal (K : Type*) [NormedField K] : Subgroup SL(2,K) where
  carrier := {g | ∃ a : K, ∃ ha : a ≠ 0, ‖a‖ = 1 ∧ g = BBEKDynamics.diagonal a ha}
  one_mem' := ⟨1, one_ne_zero, norm_one, diagonal_one.symm⟩
  mul_mem' := by
    rintro g h ⟨a,ha,hna,rfl⟩ ⟨b,hb,hnb,rfl⟩
    exact ⟨a*b,mul_ne_zero ha hb,by simp [norm_mul,hna,hnb],
      (diagonal_mul a b ha hb).symm⟩
  inv_mem' := by
    rintro g ⟨a,ha,hna,rfl⟩
    exact ⟨a⁻¹,inv_ne_zero ha,by simp [norm_inv,hna],diagonal_inv a ha⟩

theorem unitDiagonal_le (K : Type*) [NormedField K] :
    unitDiagonal K ≤ diagonalGroup K := by
  rintro g ⟨a,ha,_,he⟩
  exact ⟨a,ha,he⟩

theorem diagonal_commute {K : Type*} [Field K] {g h : SL(2,K)}
    (hg : g ∈ diagonalGroup K) (hh : h ∈ diagonalGroup K) : Commute g h := by
  rcases hg with ⟨a,ha,rfl⟩
  rcases hh with ⟨b,hb,rfl⟩
  show BBEKDynamics.diagonal a ha * BBEKDynamics.diagonal b hb =
    BBEKDynamics.diagonal b hb * BBEKDynamics.diagonal a ha
  rw [← BBEKDynamics.diagonal_mul,← BBEKDynamics.diagonal_mul]
  congr 1
  exact mul_comm a b

def sphereDiagonal {K : Type*} [NormedField K] (a : sphere (0:K) 1) : SL(2,K) :=
  BBEKDynamics.diagonal a (by
    have ha : ‖(a:K)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using a.property
    exact norm_ne_zero_iff.mp (by rw [ha]; norm_num))

theorem continuous_sphereDiagonal {K : Type*} [NormedField K] :
    Continuous (sphereDiagonal (K:=K)) := by
  have hn (a : sphere (0:K) 1) : (a:K) ≠ 0 := by
    have ha : ‖(a:K)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using a.property
    exact norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [sphereDiagonal,BBEKDynamics.diagonal,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one]
  · exact continuous_subtype_val
  · exact continuous_const
  · exact continuous_const
  · exact continuous_subtype_val.inv₀ hn

theorem unitDiagonal_eq_range {K : Type*} [NormedField K] :
    (unitDiagonal K : Set SL(2,K)) = range (sphereDiagonal (K:=K)) := by
  ext g
  constructor
  · rintro ⟨a,ha,hn,rfl⟩
    exact ⟨⟨a,by simpa only [mem_sphere,dist_zero_right] using hn⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨a,_,by simpa only [mem_sphere,dist_zero_right] using a.property,rfl⟩

theorem unitDiagonal_compact (K : Type*) [NormedField K] [ProperSpace K] :
    IsCompact (unitDiagonal K : Set SL(2,K)) := by
  letI : CompactSpace (sphere (0:K) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere (0:K) 1)
  rw [unitDiagonal_eq_range]
  exact isCompact_range continuous_sphereDiagonal

def A : Subgroup G := (diagonalGroup ℝ).prod (diagonalGroup Q2)
def K : Subgroup G := (unitDiagonal ℝ).prod (unitDiagonal Q2)

theorem K_le_A : K ≤ A := fun _ h => ⟨unitDiagonal_le ℝ h.1,unitDiagonal_le Q2 h.2⟩

theorem compact_K : IsCompact (K : Set G) :=
  (unitDiagonal_compact ℝ).prod (unitDiagonal_compact Q2)

instance : CompactSpace K := isCompact_iff_compactSpace.mp compact_K

theorem A_commute {g h : G} (hg : g ∈ A) (hh : h ∈ A) : Commute g h := by
  exact Prod.ext (diagonal_commute hg.1 hh.1).eq (diagonal_commute hg.2 hh.2).eq

theorem psi_mem_A (t : ℝ) (n : ℤ) : psi t n ∈ A :=
  ⟨⟨_,Real.exp_ne_zero _,rfl⟩,⟨_,zpow_ne_zero _ (by norm_num),rfl⟩⟩

theorem psi_commute_K (t : ℝ) (n : ℤ) (k : K) : Commute (psi t n) (k:G) :=
  A_commute (psi_mem_A t n) (K_le_A k.property)

/-- The p-adic unit coefficient is constructed using its valuation. -/
theorem exists_padic_unit_factor (b : Q2) (hb : b ≠ 0) :
    ∃ n : ℤ, ∃ u : Q2, ‖u‖ = 1 ∧ b = (2:Q2)^n*u := by
  refine ⟨b.valuation,b/(2:Q2)^b.valuation,?_,?_⟩
  · rw [norm_div,Padic.norm_eq_zpow_neg_valuation hb,show ‖(2:Q2)^b.valuation‖ = (2:ℝ)^(-b.valuation) from padicNormE.norm_p_zpow (p:=2) _]
    exact div_self (zpow_ne_zero _ (by norm_num))
  · field_simp [zpow_ne_zero _ (by norm_num : (2:Q2) ≠ 0)]

theorem exists_real_unit_factor (a : ℝ) (ha : a ≠ 0) :
    ∃ t : ℝ, ∃ u : ℝ, ‖u‖ = 1 ∧ a = Real.exp (-t)*u := by
  refine ⟨-Real.log |a|,a/|a|,?_,?_⟩
  · rw [norm_div,Real.norm_eq_abs,Real.norm_eq_abs,abs_abs]
    exact div_self (abs_ne_zero.mpr ha)
  · rw [neg_neg,Real.exp_log (abs_pos.mpr ha)]
    field_simp

/-- The full split diagonal group is psi(R x Z) times a concrete compact group. -/
theorem diagonal_decomposition {g : G} (hg : g ∈ A) :
    ∃ t : ℝ, ∃ n : ℤ, ∃ k : K, g = psi t n * (k:G) := by
  obtain ⟨a,ha,hga⟩ := hg.1
  obtain ⟨b,hb,hgb⟩ := hg.2
  obtain ⟨t,u,hu,hau⟩ := exists_real_unit_factor a ha
  obtain ⟨n,v,hv,hbv⟩ := exists_padic_unit_factor b hb
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  refine ⟨t,n,⟨(BBEKDynamics.diagonal u hu0,BBEKDynamics.diagonal v hv0),
    ⟨⟨u,hu0,hu,rfl⟩,⟨v,hv0,hv,rfl⟩⟩⟩,?_⟩
  apply Prod.ext
  · change g.1 = BBEKDynamics.diagonal (Real.exp (-t)) (Real.exp_ne_zero _) * BBEKDynamics.diagonal u hu0
    rw [hga,← BBEKDynamics.diagonal_mul]
    congr 1
  · change g.2 = BBEKDynamics.diagonal ((2:Q2)^n) (zpow_ne_zero _ (by norm_num)) * BBEKDynamics.diagonal v hv0
    rw [hgb,← BBEKDynamics.diagonal_mul]
    congr 1

theorem continuous_diagonal_map {F Z : Type*} [NormedField F] [TopologicalSpace Z]
    {a : Z → F} (ha : Continuous a) (hn : ∀ z, a z ≠ 0) :
    Continuous (fun z => BBEKDynamics.diagonal (a z) (hn z)) := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [BBEKDynamics.diagonal,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one]
  · exact ha
  · exact continuous_const
  · exact continuous_const
  · exact ha.inv₀ hn

theorem continuous_psiHom : Continuous psiHom := by
  change Continuous (fun a : Multiplicative (ℝ × ℤ) =>
    (BBEKDynamics.diagonal (Real.exp (-a.toAdd.1)) _,
      BBEKDynamics.diagonal ((2:Q2)^a.toAdd.2) _))
  apply Continuous.prodMk
  · exact continuous_diagonal_map (Real.continuous_exp.comp continuous_fst.neg)
      (fun _ => Real.exp_ne_zero _)
  · exact continuous_diagonal_map
      ((continuous_of_discreteTopology : Continuous (fun n : ℤ => (2:Q2)^n)).comp
        continuous_snd) (fun _ => zpow_ne_zero _ (by norm_num))

end VV.BBEKDiagonal

