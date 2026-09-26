import VV.P4UniformDigits

/-!
# An actual successful class of least period four

The quadratic (5 + sqrt 33) / 2 has the purely periodic continued fraction
[5,2,1,2], satisfies the original triple-tail condition, has least eventual
period four, and has B = 5. This module proves existence, not uniqueness
of the period-four class.
-/

noncomputable section
namespace VV.Problem4
open Hurwitz

def periodFourValue : ℝ := (5+Real.sqrt 33)/2

theorem periodFourValue_irrational : Irrational periodFourValue := by
  have hi : Irrational (Real.sqrt 33) := by
    apply irrational_sqrt_natCast_iff.mpr
    rintro ⟨n,hn⟩
    have h : n≤5 ∨ 6≤n := by omega
    rcases h with h|h <;> nlinarith
  simpa [periodFourValue] using (hi.intCast_add 5).div_natCast (by decide : (2:ℕ)≠0)

theorem periodFourValue_positive : 0<periodFourValue := by
  dsimp [periodFourValue]
  positivity

theorem periodFourValue_quadratic : periodFourValue^2-5*periodFourValue-2=0 := by
  have h := Real.sq_sqrt (show (0:ℝ)≤33 by norm_num)
  dsimp [periodFourValue]
  nlinarith

theorem periodFourValue_model : CycleModel periodFourValue [5,2,1,2] := by
  have hp := periodFourValue_positive
  have hq := periodFourValue_quadratic
  refine ⟨periodFourValue_irrational,hp,by simp,?_,by norm_num [trace,word,mul,digit,one]⟩
  simp only [value,Int.cast_ofNat,Int.cast_one]
  have h0 : periodFourValue≠0 := ne_of_gt hp
  have h1 : 2*periodFourValue+1≠0 := by linarith
  have h2 : 3*periodFourValue+1≠0 := by linarith
  have h3 : 8*periodFourValue+3≠0 := by linarith
  field_simp
  nlinarith

theorem periodFourValue_triple : Problem3Triple periodFourValue := by
  apply (problem3_fixed_representative periodFourValue_irrational
    (by decide : (1:ℤ)≠0)
    (show Problem3.PrimitiveTriple 1 (-5) (-2) from ⟨1,0,0,by norm_num⟩)
    (show ((1:ℤ):ℝ)*periodFourValue^2+(-5:ℤ)*periodFourValue+(-2:ℤ)=0 by
      convert periodFourValue_quadratic using 1 <;> norm_num <;> ring)).mpr
  refine ⟨by decide,5,1,by decide,by decide,Or.inr ?_⟩
  norm_num [Problem3.discriminant]

theorem periodFourValue_digits :
    partialQuotient periodFourValue 0=5 ∧ partialQuotient periodFourValue 1=2 ∧
      partialQuotient periodFourValue 2=1 ∧ partialQuotient periodFourValue 3=2 := by
  have hd := periodFourValue_model.digitBlock (by simp)
  simpa only [List.length_cons,List.length_nil,P5Period.digitBlock,
    List.cons.injEq,true_and,and_true] using hd

theorem periodFourValue_period : DigitPeriod periodFourValue 4 :=
  periodFourValue_model.digitPeriod (by simp)

theorem periodFourValue_least : ExactEventualPeriod periodFourValue 4 := by
  refine ⟨by decide,periodFourValue_period.eventual,?_⟩
  intro k hk hk4 hperiod
  have hh := period_at_least_three_of_triple periodFourValue_triple hk hperiod
  have hk3 : k=3 := by omega
  subst k
  obtain ⟨N,hN⟩ := hperiod
  have he := hN (4*N+3) (by omega)
  rw [period_digit_mod periodFourValue_period (4*N+3+3+1),
    period_digit_mod periodFourValue_period (4*N+3+1)] at he
  have h0 : (4*N+3+1)%4=0 := by omega
  have h3 : (4*N+3+3+1)%4=3 := by omega
  rw [h0,h3,periodFourValue_digits.1,periodFourValue_digits.2.2.2] at he
  norm_num at he

def periodFourRepresentative : Representative 4 :=
  ⟨periodFourValue,periodFourValue_triple,periodFourValue_least⟩

theorem class_four_nonempty : Nonempty (Class 4) := ⟨toClass periodFourRepresentative⟩

theorem card_class_four_pos : 0<Nat.card (Class 4) := by
  letI : Finite (Class 4) := (problem4_all_periods 4).1
  letI : Nonempty (Class 4) := class_four_nonempty
  exact Nat.card_pos

theorem periodFourValue_B : B periodFourValue=5 := by
  apply le_antisymm
  · apply (B_le_iff periodFourValue 5).mpr
    refine ⟨0,fun n _ => ?_⟩
    rw [period_digit_mod periodFourValue_period]
    have hm : (n+1)%4<4 := Nat.mod_lt _ (by decide)
    obtain ⟨h0,h1,h2,h3⟩ := periodFourValue_digits
    interval_cases (n+1)%4 <;> simp_all
  · apply (B_atLeast_succ_iff periodFourValue 4).mpr
    intro N
    refine ⟨4*N+3,by omega,?_⟩
    rw [period_digit_mod periodFourValue_period]
    have he : (4*N+3+1)%4=0 := by omega
    rw [he,periodFourValue_digits.1]
    norm_num

/-- In particular, a uniform period-four digit bound cannot be smaller than 5. -/
theorem five_le_uniformDigitBound_four : 5≤uniformDigitBound 4 := by
  have h := B_le_uniformDigitBound
    (show HasTripleRepresentative periodFourValue from
      ⟨periodFourValue,TailEquivalent.refl _,periodFourValue_triple⟩)
    periodFourValue_least
  rw [periodFourValue_B] at h
  exact_mod_cast h

/-- A concrete, entirely proved existence answer at period four. -/
theorem period_four_example :
    Problem3Triple periodFourValue ∧ ExactEventualPeriod periodFourValue 4 ∧
      B periodFourValue=5 :=
  ⟨periodFourValue_triple,periodFourValue_least,periodFourValue_B⟩

end VV.Problem4

