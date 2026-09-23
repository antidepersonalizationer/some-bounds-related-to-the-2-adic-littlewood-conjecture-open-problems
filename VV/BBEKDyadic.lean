import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

/-! The actual ring Z[1/2] and the integrality step in BBEK Proposition 5.1.
The ring is embedded in Q, then in the real and 2-adic fields by their
ordinary rational casts. No lattice or rigidity assertion is assumed. -/

namespace VV.BBEKDyadic

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def dyadic : Subring ℚ where
  carrier := {q | ∃ m : ℤ, ∃ k : ℕ, q = (m : ℚ) / 2^k}
  zero_mem' := ⟨0,0,by norm_num⟩
  one_mem' := ⟨1,0,by norm_num⟩
  neg_mem' := by
    rintro q ⟨m,k,rfl⟩
    exact ⟨-m,k,by push_cast; ring⟩
  add_mem' := by
    rintro q r ⟨m,k,rfl⟩ ⟨n,l,rfl⟩
    refine ⟨m*2^l+n*2^k,k+l,?_⟩
    push_cast
    rw [pow_add]
    field_simp
  mul_mem' := by
    rintro q r ⟨m,k,rfl⟩ ⟨n,l,rfl⟩
    refine ⟨m*n,k+l,?_⟩
    push_cast
    rw [pow_add,div_mul_div_comm]

theorem mem_dyadic_iff (q : ℚ) : q ∈ dyadic ↔
    ∃ m : ℤ, ∃ k : ℕ, q = (m : ℚ)/2^k := Iff.rfl

theorem int_mem_dyadic (m : ℤ) : (m : ℚ) ∈ dyadic :=
  ⟨m,0,by simp⟩

theorem inv_two_mem_dyadic : (2 : ℚ)⁻¹ ∈ dyadic :=
  ⟨1,1,by norm_num⟩

/-- In the dyadic subring, 2-adic integrality is ordinary integrality. -/
theorem dyadic_integral_of_norm_le_one {q : ℚ} (hq : q ∈ dyadic)
    (hn : ‖(q : ℚ_[2])‖ ≤ 1) : ∃ m : ℤ, q = m := by
  obtain ⟨m,k,rfl⟩ := hq
  have hpow : (0:ℝ) < ‖(2 : ℚ_[2])^k‖ := by
    apply norm_pos_iff.mpr
    exact pow_ne_zero _ (by norm_num)
  have hnum : ‖(m : ℚ_[2])‖ ≤ (2 : ℝ)^(-(k:ℤ)) := by
    have he : ‖(m : ℚ_[2]) / (2 : ℚ_[2])^k‖ ≤ 1 := by simpa using hn
    rw [norm_div,div_le_one hpow] at he
    convert he using 1
    exact (padicNormE.norm_p_pow (p:=2) k).symm
  obtain ⟨z,hz⟩ := (padicNormE.norm_int_le_pow_iff_dvd (p:=2) m k).mp hnum
  refine ⟨z,?_⟩
  rw [hz]
  push_cast
  field_simp

theorem dyadic_integral_iff {q : ℚ} (hq : q ∈ dyadic) :
    ‖(q : ℚ_[2])‖ ≤ 1 ↔ ∃ m : ℤ, q = m := by
  constructor
  · exact dyadic_integral_of_norm_le_one hq
  · rintro ⟨m,rfl⟩
    simpa using padicNormE.norm_int_le_one (p:=2) m

/-- The fourth short coordinate, together with v in Z_2, makes the
second dyadic coefficient an integer as well. -/
theorem dyadic_pair_integral {a b : ℚ} (ha : a ∈ dyadic) (hb : b ∈ dyadic)
    (v : ℤ_[2]) (haNorm : ‖(a : ℚ_[2])‖ ≤ 1)
    (hresidual : ‖(a : ℚ_[2])*(v : ℚ_[2])-(b : ℚ_[2])‖ ≤ 1) :
    ∃ m n : ℤ, a=m ∧ b=n := by
  obtain ⟨m,hm⟩ := dyadic_integral_of_norm_le_one ha haNorm
  have hav : ‖(a : ℚ_[2])*(v : ℚ_[2])‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ haNorm (norm_nonneg _) v.property
  have hbn : ‖(b : ℚ_[2])‖ ≤ 1 := by
    have he : (b : ℚ_[2]) = (a : ℚ_[2])*(v : ℚ_[2]) +
        -((a : ℚ_[2])*(v : ℚ_[2])-(b : ℚ_[2])) := by ring
    rw [he]
    exact (padicNormE.nonarchimedean _ _).trans
      (max_le hav (by rw [norm_neg]; exact hresidual))
  obtain ⟨n,hn⟩ := dyadic_integral_of_norm_le_one hb hbn
  exact ⟨m,n,hm,hn⟩

end VV.BBEKDyadic
