import VV.TailMobius
import VV.TailGenerators
import VV.MobiusGenerators
import VV.QuadraticScaling

/-!
# Problem 3 in the original continued-fraction language

Serret's equivalence is proved here, using the Euclidean matrix reduction,
explicit continued-fraction generators, and exponential cylinder shrinking.
Consequently none of the classification theorems takes Serret's theorem as
a hypothesis. Every theorem is a kernel-checked proof with no `sorry`.
-/
namespace VV
open Problem3 QuadraticScaling

theorem tailEquivalent_of_mobius {x y : ℝ} (hx : Irrational x)
    (h : MobiusEquiv x y) : TailEquivalent x y :=
  relation_of_mobius TailEquivalent (fun h₁ h₂ => h₁.trans h₂)
    (fun _ z => tailEquivalent_add_int _ z)
    tailEquivalent_inv tailEquivalent_neg hx h

/-- Serret's theorem for the literal tail relation used by this project. -/
theorem serret {x y : ℝ} (hx : Irrational x) (hy : Irrational y) :
    TailEquivalent x y ↔ MobiusEquiv x y :=
  ⟨fun h => h.mobius hx hy, tailEquivalent_of_mobius hx⟩

theorem problem3Triple_iff_mobius {x : ℝ} (hx : Irrational x) :
    Problem3Triple x ↔ Triple x := by
  have hh : Irrational (x / 2) := hx.div_natCast (by decide : (2 : ℕ) ≠ 0)
  have hs : Irrational ((x+1) / 2) := by
    simpa only [Int.cast_one, Nat.cast_ofNat] using
      (hx.add_intCast 1).div_natCast (by decide : (2 : ℕ) ≠ 0)
  simp only [Problem3Triple, Triple, hx, true_and, serret hx hh, serret hx hs]

/-- The exact fixed-representative criterion. -/
theorem problem3_fixed_representative {x : ℝ} {A B C : ℤ}
    (hx : Irrational x) (hA : A ≠ 0) (hp : PrimitiveTriple A B C)
    (hroot : (A : ℝ) * x^2 + B*x + C = 0) :
    Problem3Triple x ↔ Odd A ∧ SignedPellEight (discriminant A B C) := by
  rw [problem3Triple_iff_mobius hx]
  exact fixed_representative_classification_short hx hA hp hroot

def HasTripleRepresentative (x : ℝ) : Prop :=
  ∃ y : ℝ, TailEquivalent x y ∧ Problem3Triple y

/-- All tail classes with a specified primitive quadratic representative:
the criterion depends only on its primitive discriminant. -/
theorem problem3_equivalence_class {x : ℝ} {A B C : ℤ}
    (hx : Irrational x) (hp : PrimitiveTriple A B C)
    (hroot : (A : ℝ) * x^2 + B*x + C = 0) :
    HasTripleRepresentative x ↔ SignedPellEight (discriminant A B C) := by
  rw [← equivalence_class_classification hx hp hroot]
  constructor
  · rintro ⟨y, hxy, hy⟩
    exact ⟨y, hxy.mobius hx hy.1, (problem3Triple_iff_mobius hy.1).mp hy⟩
  · rintro ⟨y, hxy, hy⟩
    have hiy := irrational_of_mobius hx hxy
    exact ⟨y, tailEquivalent_of_mobius hx hxy, (problem3Triple_iff_mobius hiy).mpr hy⟩

/-- Existence of a primitive quadratic equation follows from the property;
quadraticity is not an extra assumption on a successful class. -/
theorem primitive_quadratic_of_hasTripleRepresentative {x : ℝ}
    (hx : Irrational x) (h : HasTripleRepresentative x) :
    ∃ Q : Quadratic, Q.A ≠ 0 ∧ PrimitiveTriple Q.A Q.B Q.C ∧ Q.eval x = 0 := by
  obtain ⟨y, hxy, hy⟩ := h
  have hmy := (problem3Triple_iff_mobius hy.1).mp hy
  obtain ⟨A, B, C, hA, hroot⟩ := quadratic_of_half_equiv hy.1 hmy.1
  let Q : Quadratic := ⟨A, B, C⟩
  have hp := normalize_primitive Q hA
  have hr := normalize_root Q hA hroot
  obtain ⟨a, b, c, d, hd, he⟩ := mobius_symm (hxy.mobius hx hy.1)
  let R : Quadratic :=
    ⟨transA Q.normalize.A Q.normalize.B Q.normalize.C a b c d,
     transB Q.normalize.A Q.normalize.B Q.normalize.C a b c d,
     transC Q.normalize.A Q.normalize.B Q.normalize.C a b c d⟩
  have hpR : PrimitiveTriple R.A R.B R.C := transformed_primitive hp hd
  have hrR : R.eval x = 0 := transformed_root hr he
  exact ⟨R, A_ne_zero_of_primitive_irrational_root R hx hrR hpR, hpR, hrR⟩

/-- Full classification without presupposing that `x` is quadratic. -/
theorem problem3_classification {x : ℝ} (hx : Irrational x) :
    HasTripleRepresentative x ↔
      ∃ A B C : ℤ, A ≠ 0 ∧ PrimitiveTriple A B C ∧
        (A : ℝ) * x^2 + B*x + C = 0 ∧ SignedPellEight (discriminant A B C) := by
  constructor
  · intro h
    obtain ⟨Q, hA, hp, hr⟩ := primitive_quadratic_of_hasTripleRepresentative hx h
    exact ⟨Q.A, Q.B, Q.C, hA, hp, hr, (problem3_equivalence_class hx hp hr).mp h⟩
  · rintro ⟨A, B, C, _hA, hp, hr, hPell⟩
    exact (problem3_equivalence_class hx hp hr).mpr hPell

end VV
