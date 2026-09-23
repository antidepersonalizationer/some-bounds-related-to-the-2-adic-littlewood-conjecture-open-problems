import VV.BBEKParameter
import VV.BBEKFiniteQuotients
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.RingTheory.Coprime.Lemmas

/-! Two-dimensional real lattice reduction for S-arithmetic Mahler
compactness. All matrices, integer changes of basis, and bounds are actual. -/

noncomputable section
open Matrix Set MeasureTheory
open scoped MatrixGroups Topology

namespace VV.BBEKMahlerReal

abbrev V := Fin 2 → ℝ

def realBasis (g : SL(2,ℝ)) : Basis (Fin 2) ℝ V :=
  (Pi.basisFun ℝ (Fin 2)).map g.toLin'

@[simp] theorem realBasis_apply (g : SL(2,ℝ)) (i j : Fin 2) : realBasis g i j = g j i := by
  simp [realBasis,Matrix.SpecialLinearGroup.toLin'_apply,Matrix.toLin'_apply,
    Pi.basisFun_apply,Matrix.mulVec_single_one]

theorem fundamental_volume (g : SL(2,ℝ)) :
    volume (ZSpan.fundamentalDomain (realBasis g)) = 1 := by
  rw [ZSpan.volume_fundamentalDomain]
  have he : Matrix.of (realBasis g) = (g : Matrix (Fin 2) (Fin 2) ℝ)ᵀ := by
    ext i j
    exact realBasis_apply g i j
  rw [he,Matrix.det_transpose,g.property]
  norm_num

def cube : Set V := Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-2:ℝ) 2)

theorem cube_volume : volume cube = 16 := by
  change (Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ)))
    (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-2:ℝ) 2)) = 16
  rw [Measure.pi_pi]
  norm_num [Real.volume_Icc,Fin.prod_univ_two]

theorem exists_short_integer_vector (g : SL(2,ℝ)) :
    ∃ z : Fin 2 → ℤ, z ≠ 0 ∧ ∀ i : Fin 2,
      |((g : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (fun j => (z j : ℝ))) i| ≤ 2 := by
  let b := realBasis g
  let L := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  letI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hc : Convex ℝ cube := convex_pi fun _ _ => convex_Icc _ _
  have hneg : ∀ x ∈ cube, -x ∈ cube := by
    intro x hx i hi
    have hxi := hx i hi
    exact ⟨by change (-2:ℝ) ≤ -(x i); linarith [hxi.2],
      by change -(x i) ≤ (2:ℝ); linarith [hxi.1]⟩
  have hvol : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ V < volume cube := by
    rw [fundamental_volume g,cube_volume]
    norm_num [V,Module.finrank_pi]
  obtain ⟨v,hv0,hvc⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' b volume) hneg hc hvol
  have hm := (b.mem_span_iff_repr_mem ℤ (v : V)).mp v.property
  choose z hz using hm
  have hvec : (g : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (fun j => (z j : ℝ)) = (v : V) := by
    have hs := b.sum_repr (v : V)
    rw [← hs]
    funext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hz j]
    change g i j * (z j : ℝ) = (z j : ℝ) * realBasis g j i
    rw [realBasis_apply,mul_comm]
  refine ⟨z,?_,?_⟩
  · intro hz0
    apply hv0
    apply Subtype.ext
    rw [← hvec,hz0]
    funext i
    simp [Matrix.mulVec,dotProduct]
  · intro i
    rw [hvec]
    exact abs_le.mpr (hvc i (Set.mem_univ i))

def intToReal : ℤ →+* ℝ := Int.castRingHom ℝ

theorem exists_short_first_column (g : SL(2,ℝ)) :
    ∃ A : SL(2,ℤ), ∀ i : Fin 2,
      |(g * Matrix.SpecialLinearGroup.map intToReal A) i 0| ≤ 2 := by
  obtain ⟨z,hz,hbound⟩ := exists_short_integer_vector g
  have hg : 0 < Int.gcd (z 0) (z 1) := by
    apply Nat.pos_of_ne_zero
    intro h
    obtain ⟨h0,h1⟩ := Int.gcd_eq_zero_iff.mp h
    apply hz
    funext i
    fin_cases i <;> assumption
  obtain ⟨a,b,hab,hza,hzb⟩ := Int.exists_gcd_one hg
  obtain ⟨A,hA0,hA1⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr hab).exists_SL2_col 0
  refine ⟨A,?_⟩
  intro i
  have hzaR : (z 0 : ℝ) = (a:ℝ) * (Int.gcd (z 0) (z 1) : ℝ) := by exact_mod_cast hza
  have hzbR : (z 1 : ℝ) = (b:ℝ) * (Int.gcd (z 0) (z 1) : ℝ) := by exact_mod_cast hzb
  have he : (g * Matrix.SpecialLinearGroup.map intToReal A) i 0 * (Int.gcd (z 0) (z 1) : ℝ) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (fun j => (z j : ℝ))) i := by
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.mulVec,dotProduct,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,intToReal,Int.coe_castRingHom]
    rw [hA0,hA1,hzaR,hzbR]
    ring
  have hgr : (1:ℝ) ≤ (Int.gcd (z 0) (z 1) : ℝ) := by exact_mod_cast hg
  have hlarge := hbound i
  have hgabs : |(Int.gcd (z 0) (z 1) : ℝ)| = (Int.gcd (z 0) (z 1) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [← he,abs_mul,hgabs] at hlarge
  nlinarith [abs_nonneg ((g * Matrix.SpecialLinearGroup.map intToReal A) i 0)]

theorem exists_integer_shear (x y : ℝ) (hy : y ≠ 0) :
    ∃ k : ℤ, |x - (k:ℝ)*y| ≤ |y| := by
  refine ⟨⌊x/y⌋,?_⟩
  have he : x - (⌊x/y⌋:ℝ)*y = y * Int.fract (x/y) := by
    rw [Int.fract]
    field_simp
    ring
  rw [he,abs_mul,Int.abs_fract]
  exact (mul_le_mul_of_nonneg_left (Int.fract_lt_one (x/y)).le (abs_nonneg y)).trans_eq
    (mul_one _)

private theorem bound_other {r d x : ℝ} (hr : 0 < r) (hrd : r ≤ |d|)
    (hb : |d| * |x| ≤ 1 + |d| * 2) : |x| ≤ 2 + 1/r := by
  have hd : 0 < |d| := hr.trans_le hrd
  have hx : |x| ≤ 2 + 1/|d| := by
    apply (mul_le_mul_left hd).mp
    calc
      _ ≤ 1 + |d| * 2 := hb
      _ = |d| * (2 + 1/|d|) := by field_simp; ring
  exact hx.trans (add_le_add_left (one_div_le_one_div_of_le hr hrd) 2)

theorem scalar_shear_bound {a b c d r : ℝ} (hdet : a*d-b*c=1)
    (hr : 0 < r) (hmin : r ≤ max |a| |c|) (ha : |a| ≤ 2) (hc : |c| ≤ 2) :
    ∃ k : ℤ, |b-(k:ℝ)*a| ≤ 2+1/r ∧ |d-(k:ℝ)*c| ≤ 2+1/r := by
  have h2 : (2:ℝ) ≤ 2+1/r := by linarith [one_div_pos.mpr hr]
  by_cases hac : |c| ≤ |a|
  · have hra : r ≤ |a| := by simpa only [max_eq_left hac] using hmin
    have ha0 : a ≠ 0 := abs_pos.mp (hr.trans_le hra)
    obtain ⟨k,hk⟩ := exists_integer_shear b a ha0
    refine ⟨k,(hk.trans ha).trans h2,?_⟩
    apply bound_other hr hra
    calc
      |a| * |d-(k:ℝ)*c| = |1+(b-(k:ℝ)*a)*c| := by
        rw [← abs_mul]
        congr 1
        nlinarith [hdet]
      _ ≤ 1 + |b-(k:ℝ)*a| * |c| := by simpa only [abs_one,abs_mul] using abs_add 1 ((b-(k:ℝ)*a)*c)
      _ ≤ 1 + |a| * 2 := by gcongr
  · have hca : |a| ≤ |c| := (lt_of_not_ge hac).le
    have hrc : r ≤ |c| := by simpa only [max_eq_right hca] using hmin
    have hc0 : c ≠ 0 := abs_pos.mp (hr.trans_le hrc)
    obtain ⟨k,hk⟩ := exists_integer_shear d c hc0
    refine ⟨k,?_,(hk.trans hc).trans h2⟩
    apply bound_other hr hrc
    calc
      |c| * |b-(k:ℝ)*a| = |a*(d-(k:ℝ)*c)-1| := by
        rw [← abs_mul]
        congr 1
        nlinarith [hdet]
      _ ≤ |a| * |d-(k:ℝ)*c| + 1 := by simpa only [abs_one,abs_mul] using abs_sub (a*(d-(k:ℝ)*c)) 1
      _ ≤ 2*|c|+1 := by gcongr
      _ = 1+|c| * 2 := by ring

@[simp] theorem map_int_apply (A : SL(2,ℤ)) (i j : Fin 2) :
    Matrix.SpecialLinearGroup.map intToReal A i j = (A i j : ℝ) := rfl

theorem matrix_shear_bound (M : SL(2,ℝ)) {r : ℝ} (hr : 0 < r)
    (hmin : r ≤ max |M 0 0| |M 1 0|) (hbound : ∀ i, |M i 0| ≤ 2) :
    ∃ B : SL(2,ℤ), ∀ i j, |(M * Matrix.SpecialLinearGroup.map intToReal B) i j| ≤ 2+1/r := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.property
  obtain ⟨k,hk0,hk1⟩ := scalar_shear_bound hdet hr hmin (hbound 0) (hbound 1)
  refine ⟨BBEKFiniteQuotients.upper (-k),?_⟩
  intro i j
  have he : (M * Matrix.SpecialLinearGroup.map intToReal (BBEKFiniteQuotients.upper (-k))) i j =
      if j=0 then M i 0 else M i 1-(k:ℝ)*M i 0 := by
    fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,BBEKFiniteQuotients.upper] <;> ring
  rw [he]
  fin_cases j
  · simp only [ite_true]
    exact (hbound i).trans (by linarith [one_div_pos.mpr hr])
  · simp only [show (1:Fin 2) ≠ 0 by decide,ite_false]
    fin_cases i
    · exact hk0
    · exact hk1

theorem exists_bounded_integer_basis (g : SL(2,ℝ)) {r : ℝ} (hr : 0 < r)
    (hmin : ∀ v : Fin 2 → ℤ, v ≠ 0 →
      r ≤ ‖g.val *ᵥ (fun i => (v i : ℝ))‖) :
    ∃ A : SL(2,ℤ), ∀ i j,
      |(g * Matrix.SpecialLinearGroup.map intToReal A) i j| ≤ 2+1/r := by
  obtain ⟨A,hA⟩ := exists_short_first_column g
  let M := g * Matrix.SpecialLinearGroup.map intToReal A
  have hne : (fun i : Fin 2 => A i 0) ≠ 0 := by
    intro he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using A.property
    simp only [Pi.zero_apply] at h0 h1
    rw [h0,h1] at hd
    norm_num at hd
  have hvec : g.val *ᵥ (fun i => (A i 0 : ℝ)) = (fun i => M i 0) := by
    funext i
    simp [M,Matrix.mulVec,dotProduct,Matrix.mul_apply,Fin.sum_univ_two]
  have hrM : r ≤ max |M 0 0| |M 1 0| := by
    have hh := hmin (fun i => A i 0) hne
    rw [hvec] at hh
    apply hh.trans
    apply (pi_norm_le_iff_of_nonneg ((abs_nonneg (M 0 0)).trans (le_max_left _ _))).mpr
    intro i
    fin_cases i
    · exact (Real.norm_eq_abs _).trans_le (le_max_left _ _)
    · exact (Real.norm_eq_abs _).trans_le (le_max_right _ _)
  obtain ⟨B,hB⟩ := matrix_shear_bound M hr hrM hA
  refine ⟨A*B,?_⟩
  intro i j
  rw [map_mul,← mul_assoc]
  exact hB i j

end VV.BBEKMahlerReal
