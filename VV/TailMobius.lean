import VV.TailEquivalence
import VV.Problem3
import VV.CylinderGeometry

/-!
Elementary matrix steps connecting the actual complete-quotient recurrence
to the integer unimodular relation. These are independent of Serret's theorem.
-/
namespace VV
open Problem3

theorem mobius_refl (x : ℝ) : MobiusEquiv x x :=
  ⟨1, 0, 0, 1, Or.inl (by norm_num), by simp⟩

theorem mobius_trans {α β γ : ℝ} (h₁ : MobiusEquiv α β) (h₂ : MobiusEquiv β γ) :
    MobiusEquiv α γ := by
  obtain ⟨a, b, c, d, hd₁, he₁⟩ := h₁
  obtain ⟨e, f, g, h, hd₂, he₂⟩ := h₂
  refine ⟨e*a+f*c, e*b+f*d, g*a+h*c, g*b+h*d, ?_, ?_⟩
  · have hdet : (e*a+f*c)*(g*b+h*d)-(e*b+f*d)*(g*a+h*c) =
        (e*h-f*g)*(a*d-b*c) := by ring
    rw [hdet]
    rcases hd₁ with hd₁ | hd₁ <;> rcases hd₂ with hd₂ | hd₂ <;>
      simp [hd₁, hd₂]
  · push_cast
    linear_combination ((c : ℝ)*α+d)*he₂ + ((e : ℝ)-γ*g)*he₁

theorem mobius_gauss {x : ℝ} (hx : Irrational x) :
    MobiusEquiv x (Int.fract x)⁻¹ := by
  refine ⟨0, 1, 1, -⌊x⌋, Or.inr (by norm_num), ?_⟩
  have hz : Int.fract x ≠ 0 := completeQuotient_fract_ne_zero hx 0
  simpa [Int.fract, sub_eq_add_neg] using inv_mul_cancel₀ hz

theorem mobius_completeQuotient {x : ℝ} (hx : Irrational x) (n : ℕ) :
    MobiusEquiv x (completeQuotient x n) := by
  induction n with
  | zero => exact mobius_refl x
  | succ n ih => exact mobius_trans ih (mobius_gauss (completeQuotient_irrational hx n))

theorem mobius_of_completeQuotient_eq {x y : ℝ}
    (hx : Irrational x) (hy : Irrational y) {m n : ℕ}
    (h : completeQuotient x m = completeQuotient y n) : MobiusEquiv x y := by
  apply mobius_trans (mobius_completeQuotient hx m)
  rw [h]
  exact Problem3.mobius_symm (mobius_completeQuotient hy n)

/-- Equality of literal digit tails gives equality of complete quotients;
uniqueness uses the proved exponential cylinder contraction. -/
theorem TailEquivalent.exists_completeQuotient_eq {x y : ℝ}
    (hx : Irrational x) (hy : Irrational y) (h : TailEquivalent x y) :
    ∃ m n : ℕ, completeQuotient x m = completeQuotient y n := by
  obtain ⟨m, n, h⟩ := h
  refine ⟨m + 1, n + 1, ?_⟩
  apply CylinderGeometry.eq_of_all_partialQuotients_eq
    (completeQuotient_irrational hx _) (completeQuotient_irrational hy _)
  intro k
  simp only [partialQuotient, completeQuotient_add]
  simpa only [partialQuotient, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h k

theorem TailEquivalent.mobius {x y : ℝ} (hx : Irrational x) (hy : Irrational y)
    (h : TailEquivalent x y) : MobiusEquiv x y := by
  obtain ⟨m, n, heq⟩ := h.exists_completeQuotient_eq hx hy
  exact mobius_of_completeQuotient_eq hx hy heq

end VV
