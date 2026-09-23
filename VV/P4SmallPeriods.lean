import VV.Problem4Real
import VV.Classification
import VV.P5Period

/-!
Unconditional small-period conclusions for Problem 4. The original actual
tail classes of periods one and two are empty. The proof is theoretical:
a period-two quadratic relation contradicts the parity forced by Problem 3.
No list of digits or discriminants is searched.
-/

namespace VV.Problem4
open Problem3 QuadraticScaling

theorem not_eventualPeriod_two_of_hasTripleRepresentative {x : ℝ}
    (hx : Irrational x) (hclass : HasTripleRepresentative x) :
    ¬ EventualPeriod x 2 := by
  rintro ⟨N, hN⟩
  let z := completeQuotient x (N + 1)
  have hz : Irrational z := completeQuotient_irrational hx _
  have hzc : HasTripleRepresentative z := by
    obtain ⟨y, hxy, hy⟩ := hclass
    exact ⟨y, (tailEquivalent_completeQuotient x (N + 1)).symm.trans hxy, hy⟩
  obtain ⟨A, B, C, hA, hp, hr, hPell⟩ := (problem3_classification hz).mp hzc
  have hper : ∀ k : ℕ, partialQuotient x (N + 1 + 2 + k) =
      partialQuotient x (N + 1 + k) := by
    intro k
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hN (N + k) (by omega)
  let a := partialQuotient x (N + 1)
  let b := partialQuotient x (N + 2)
  have hrel : (b : ℝ) * z ^ 2 + ((-a * b : ℤ) : ℝ) * z + (-a : ℤ) = 0 := by
    have h := P5Period.periodQuadratic_root hx (N + 1) 2 hper
    simpa [P5Period.periodQuadratic, P5Period.digitBlock, P5Period.matrix,
      P5Period.prepend, P5Period.identity, Quadratic.eval, z, a, b, Nat.add_assoc] using h
  obtain ⟨v, hb, hB, ha⟩ := relation_multiple hz hA hp hr hrel
  have hbpos : 1 ≤ b := one_le_partialQuotient_succ hx (N + 1)
  have hv : v ≠ 0 := by intro h; rw [h, mul_zero] at hb; omega
  have ha' : a = -C * v := by linear_combination -ha
  have hB' : B = A * C * v := by
    apply mul_right_cancel₀ hv
    calc
      B * v = -a * b := hB.symm
      _ = (A * C * v) * v := by rw [ha', hb]; ring
  obtain ⟨hodd, heven⟩ := coefficient_parity_of_pell hPell
  have hBeven : Even B := by rw [hB']; exact heven.mul_right v
  obtain ⟨o, ho⟩ := hodd
  obtain ⟨e, he⟩ := hBeven
  omega

theorem eventualPeriod_two_of_one {x : ℝ} (h : EventualPeriod x 1) :
    EventualPeriod x 2 := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  have h₁ := hN n hn
  have h₂ := hN (n + 1) (by omega)
  simpa only [Nat.add_assoc] using h₂.trans h₁

theorem not_eventualPeriod_one_of_hasTripleRepresentative {x : ℝ}
    (hx : Irrational x) (hclass : HasTripleRepresentative x) :
    ¬ EventualPeriod x 1 :=
  fun h => not_eventualPeriod_two_of_hasTripleRepresentative hx hclass
    (eventualPeriod_two_of_one h)

theorem period_at_least_three_of_triple {x : ℝ} (h : Problem3Triple x)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hp : EventualPeriod x ℓ) : 3 ≤ ℓ := by
  have hc : HasTripleRepresentative x := ⟨x, TailEquivalent.refl x, h⟩
  have h₁ := not_eventualPeriod_one_of_hasTripleRepresentative h.1 hc
  have h₂ := not_eventualPeriod_two_of_hasTripleRepresentative h.1 hc
  by_contra! hlt
  have cases : ℓ = 1 ∨ ℓ = 2 := by omega
  rcases cases with rfl | rfl
  · exact h₁ hp
  · exact h₂ hp

theorem isEmpty_representative_small {ℓ : ℕ} (hℓ : ℓ ≤ 2) :
    IsEmpty (Representative ℓ) := by
  refine ⟨fun x => ?_⟩
  have h := period_at_least_three_of_triple x.property.1 x.property.2.1 x.property.2.2.1
  omega

theorem isEmpty_class_small {ℓ : ℕ} (hℓ : ℓ ≤ 2) : IsEmpty (Class ℓ) := by
  letI := isEmpty_representative_small hℓ
  refine ⟨fun x => ?_⟩
  induction x using Quotient.inductionOn with
  | h x => exact isEmptyElim x

theorem actual_class_count_small {ℓ : ℕ} (hℓ : ℓ ≤ 2) : Nat.card (Class ℓ) = 0 := by
  letI := isEmpty_class_small hℓ
  exact Nat.card_of_isEmpty

end VV.Problem4
