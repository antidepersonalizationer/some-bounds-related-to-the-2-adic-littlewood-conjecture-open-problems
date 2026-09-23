import Mathlib.Data.Real.Irrational
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Problem 3: exact algebraic certificates

The equivalence relation in this file is explicitly the integer unimodular
Möbius relation. Identifying it with equality of continued-fraction tails is
Serret's theorem, which is kept separate from the algebra proved here.
-/

namespace VV.Problem3

def discriminant (A B C : ℤ) : ℤ := B ^ 2 - 4 * A * C

def normForm (A B C s v : ℤ) : ℤ := s ^ 2 - B * s * v + A * C * v ^ 2

def SignedPellEight (D : ℤ) : Prop :=
  ∃ t v : ℤ, Odd t ∧ Odd v ∧ (t ^ 2 - D * v ^ 2 = 8 ∨ t ^ 2 - D * v ^ 2 = -8)

def NormTwo (A B C : ℤ) : Prop :=
  ∃ s v : ℤ, Odd v ∧ (normForm A B C s v = 2 ∨ normForm A B C s v = -2)

def MobiusEquiv (α β : ℝ) : Prop :=
  ∃ a b c d : ℤ,
    (a * d - b * c = 1 ∨ a * d - b * c = -1) ∧
    β * ((c : ℝ) * α + d) = (a : ℝ) * α + b

def Triple (α : ℝ) : Prop :=
  MobiusEquiv α (α / 2) ∧ MobiusEquiv α ((α + 1) / 2)

/-- Bézout formulation of a primitive integer coefficient triple. -/
def PrimitiveTriple (A B C : ℤ) : Prop :=
  ∃ x y z : ℤ, x * A + y * B + z * C = 1

theorem irrational_linear {α : ℝ} (hα : Irrational α) {a b : ℤ}
    (h : (a : ℝ) * α + b = 0) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    by_contra ha
    exact ((hα.intCast_mul ha).add_intCast b).ne_zero h
  refine ⟨ha, ?_⟩
  simp only [ha, Int.cast_zero, zero_mul, zero_add] at h
  exact_mod_cast h

theorem relation_multiple {α : ℝ} {A B C c d e : ℤ}
    (hα : Irrational α) (hA : A ≠ 0) (hp : PrimitiveTriple A B C)
    (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0)
    (hrel : (c : ℝ) * α ^ 2 + d * α + e = 0) :
    ∃ v : ℤ, c = A * v ∧ d = B * v ∧ e = C * v := by
  have hl : ((A * d - c * B : ℤ) : ℝ) * α + (A * e - c * C : ℤ) = 0 := by
    push_cast
    linear_combination (A : ℝ) * hrel - (c : ℝ) * hroot
  obtain ⟨hd, he⟩ := irrational_linear hα hl
  obtain ⟨x, y, z, hp⟩ := hp
  let v := c * x + d * y + e * z
  have hc : A * v = c := by
    dsimp [v]
    linear_combination y * hd + z * he + c * hp
  refine ⟨v, hc.symm, ?_, ?_⟩
  · apply mul_left_cancel₀ hA
    linear_combination hd - B * hc
  · apply mul_left_cancel₀ hA
    linear_combination he - C * hc

theorem odd_v_of_norm {A B C s v : ℤ}
    (hn : normForm A B C s v = 2 ∨ normForm A B C s v = -2) : Odd v := by
  rcases Int.even_or_odd v with hv | hv
  · exfalso
    rcases Int.even_or_odd s with hs | hs
    · obtain ⟨x, hx⟩ := even_iff_exists_two_mul.mp hs
      obtain ⟨y, hy⟩ := even_iff_exists_two_mul.mp hv
      have he : normForm A B C s v = 4 * (x ^ 2 - B * x * y + A * C * y ^ 2) := by
        rw [hx, hy]; unfold normForm; ring
      rcases hn with hn | hn <;> omega
    · have ho : Odd (normForm A B C s v) :=
        ((hs.pow (n := 2)).sub_even (hv.mul_left (B * s))).add_even
          ((hv.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)).mul_left (A * C))
      rcases ho with ⟨k, hk⟩
      rcases hn with hn | hn <;> omega
  · exact hv

theorem pell_identity (A B C s v : ℤ) :
    (2 * s - B * v) ^ 2 - discriminant A B C * v ^ 2 =
      4 * normForm A B C s v := by
  unfold discriminant normForm
  ring

theorem norm_conjugate (A B C s v : ℤ) :
    normForm A B C (s - B * v) (-v) = normForm A B C s v := by
  unfold normForm
  ring

theorem pell_iff_norm (A B C : ℤ) (hB : Odd B) :
    SignedPellEight (discriminant A B C) ↔ NormTwo A B C := by
  constructor
  · rintro ⟨t, v, ht, hv, h⟩
    obtain ⟨s, hs⟩ := even_iff_exists_two_mul.mp (ht.add_odd (hB.mul hv))
    refine ⟨s, v, hv, ?_⟩
    have heq : 2 * s - B * v = t := by omega
    have hid := pell_identity A B C s v
    rw [heq] at hid
    rcases h with h | h
    · left; omega
    · right; omega
  · rintro ⟨s, v, hv, h⟩
    refine ⟨2 * s - B * v, v, ?_, hv, ?_⟩
    · exact (even_two_mul s).sub_odd (hB.mul hv)
    · rw [pell_identity]
      rcases h with h | h
      · left; omega
      · right; omega

theorem mobius_denominator_ne_zero {α β : ℝ} {a b c d : ℤ}
    (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1)
    (heq : β * ((c : ℝ) * α + d) = (a : ℝ) * α + b) :
    (c : ℝ) * α + d ≠ 0 := by
  intro hz
  have hn : (a : ℝ) * α + b = 0 := by rw [hz, mul_zero] at heq; linarith
  have hd : (a : ℝ) * d - b * c = 0 := by
    linear_combination (a : ℝ) * hz - (c : ℝ) * hn
  have hd' : a * d - b * c = 0 := by exact_mod_cast hd
  rcases hdet with h | h <;> omega

theorem half_of_odd_norm {α : ℝ} {A B C s v : ℤ}
    (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0)
    (hB : Odd B) (hC : Even C) (hv : Odd v) (hs : Odd s)
    (hnorm : normForm A B C s v = 2 ∨ normForm A B C s v = -2) :
    MobiusEquiv α (α / 2) := by
  obtain ⟨u, hu⟩ := even_iff_exists_two_mul.mp (hs.sub_odd (hB.mul hv))
  obtain ⟨w, hw⟩ := even_iff_exists_two_mul.mp ((hC.mul_right v).neg)
  refine ⟨u, w, A * v, s, ?_, ?_⟩
  · have hd : 2 * (u * s - w * (A * v)) = normForm A B C s v := by
      unfold normForm
      linear_combination -s * hu + (A * v) * hw
    rcases hnorm with h | h
    · left; omega
    · right; omega
  · have huR : (s : ℝ) - B * v = 2 * u := by exact_mod_cast hu
    have hwR : -((C : ℝ) * v) = 2 * w := by exact_mod_cast hw
    push_cast
    linear_combination (v / 2 : ℝ) * hroot + (α / 2) * huR + hwR / 2

theorem shifted_half_of_even_norm {α : ℝ} {A B C s v : ℤ}
    (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0)
    (hA : Odd A) (hB : Odd B) (hC : Even C) (hs : Even s)
    (hnorm : normForm A B C s v = 2 ∨ normForm A B C s v = -2) :
    MobiusEquiv α ((α + 1) / 2) := by
  obtain ⟨u, hu⟩ := even_iff_exists_two_mul.mp (hs.add ((hA.sub_odd hB).mul_right v))
  obtain ⟨w, hw⟩ := even_iff_exists_two_mul.mp (hs.sub (hC.mul_right v))
  refine ⟨u, w, A * v, s, ?_, ?_⟩
  · have hd : 2 * (u * s - w * (A * v)) = normForm A B C s v := by
      unfold normForm
      linear_combination -s * hu + (A * v) * hw
    rcases hnorm with h | h
    · left; omega
    · right; omega
  · have huR : (s : ℝ) + (A - B) * v = 2 * u := by exact_mod_cast hu
    have hwR : (s : ℝ) - C * v = 2 * w := by exact_mod_cast hw
    push_cast
    linear_combination (v / 2 : ℝ) * hroot + (α / 2) * huR + hwR / 2

theorem triple_of_norm {α : ℝ} {A B C : ℤ}
    (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0)
    (hA : Odd A) (hB : Odd B) (hC : Even C)
    (hnorm : NormTwo A B C) : Triple α := by
  rcases hnorm with ⟨s, v, hv, hn⟩
  have hc : normForm A B C (s - B * v) (-v) = 2 ∨
      normForm A B C (s - B * v) (-v) = -2 := by
    simpa only [norm_conjugate] using hn
  rcases Int.even_or_odd s with hs | hs
  · exact ⟨half_of_odd_norm hroot hB hC hv.neg (hs.sub_odd (hB.mul hv)) hc,
      shifted_half_of_even_norm hroot hA hB hC hs hn⟩
  · exact ⟨half_of_odd_norm hroot hB hC hv hs hn,
      shifted_half_of_even_norm hroot hA hB hC (hs.sub_odd (hB.mul hv)) hc⟩

theorem triple_of_pell {α : ℝ} {A B C : ℤ}
    (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0)
    (hA : Odd A) (hB : Odd B) (hC : Even C)
    (hpell : SignedPellEight (discriminant A B C)) : Triple α :=
  triple_of_norm hroot hA hB hC ((pell_iff_norm A B C hB).mp hpell)

theorem branch_norm {α : ℝ} {A B C : ℤ} (j : ℤ)
    (hα : Irrational α) (hA : A ≠ 0) (hp : PrimitiveTriple A B C)
    (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0)
    (hbranch : MobiusEquiv α ((α + j) / 2)) :
    ∃ a b c d v : ℤ, Odd v ∧
      c = A * v ∧ j * c + d - 2 * a = B * v ∧ j * d - 2 * b = C * v ∧
      (normForm A B C d v = 2 ∨ normForm A B C d v = -2) := by
  obtain ⟨a, b, c, d, hdet, heq⟩ := hbranch
  have hrel : (c : ℝ) * α ^ 2 + (j * c + d - 2 * a : ℤ) * α +
      (j * d - 2 * b : ℤ) = 0 := by
    push_cast
    linear_combination 2 * heq
  obtain ⟨v, hc, hd, hb⟩ := relation_multiple hα hA hp hroot hrel
  have hn : normForm A B C d v = 2 * (a * d - b * c) := by
    unfold normForm
    linear_combination d * hd - c * hb - C * v * hc
  have hn' : normForm A B C d v = 2 ∨ normForm A B C d v = -2 := by
    rcases hdet with h | h
    · left; omega
    · right; omega
  exact ⟨a, b, c, d, v, odd_v_of_norm hn', hc, hd, hb, hn'⟩

theorem even_of_mul_odd {x y : ℤ} (h : Even (x * y)) (hy : Odd y) : Even x := by
  rcases Int.even_mul.mp h with hx | hy'
  · exact hx
  · exact False.elim (Int.not_even_iff_odd.mpr hy hy')

theorem parity_of_triple {α : ℝ} {A B C : ℤ}
    (hα : Irrational α) (hA : A ≠ 0) (hp : PrimitiveTriple A B C)
    (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0)
    (ht : Triple α) : Odd A ∧ Odd B ∧ Even C := by
  obtain ⟨a, b, c, d, v, hv, hc, hd, hb, hn⟩ :=
    branch_norm 0 hα hA hp hroot (by simpa using ht.1)
  have hC : Even C := by
    apply even_of_mul_odd (y := v) _ hv
    rw [← hb]
    simpa using (even_two_mul b).neg
  obtain ⟨a', b', c', d', v', hv', hc', hd', hb', hn'⟩ :=
    branch_norm 1 hα hA hp hroot (by simpa using ht.2)
  have hABC : Even (A - B + C) := by
    apply even_of_mul_odd (y := v') _ hv'
    have he : (A - B + C) * v' = 2 * (a' - b') := by
      linear_combination -hc' + hd' - hb'
    rw [he]
    exact even_two_mul _
  have hAB : Even (A - B) := by simpa using hABC.sub hC
  have hAo : Odd A := by
    apply Int.not_even_iff_odd.mp
    intro hAe
    have hBe : Even B := by
      convert hAe.sub hAB using 1 <;> ring
    obtain ⟨x, y, z, hp'⟩ := hp
    have hE := ((hAe.mul_left x).add (hBe.mul_left y)).add (hC.mul_left z)
    rw [hp'] at hE
    norm_num at hE
  have hBo : Odd B := by
    convert hAo.sub_even hAB using 1 <;> ring
  exact ⟨hAo, hBo, hC⟩

/-- Complete arithmetic criterion for a fixed primitive quadratic representative,
using the unimodular Möbius definition of equivalence. No finite computation
and no admitted theorem is used. -/
theorem fixed_representative_classification {α : ℝ} {A B C : ℤ}
    (hα : Irrational α) (hA : A ≠ 0) (hp : PrimitiveTriple A B C)
    (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0) :
    Triple α ↔ Odd A ∧ Odd B ∧ Even C ∧ SignedPellEight (discriminant A B C) := by
  constructor
  · intro ht
    obtain ⟨hAo, hBo, hCe⟩ := parity_of_triple hα hA hp hroot ht
    refine ⟨hAo, hBo, hCe, (pell_iff_norm A B C hBo).mpr ?_⟩
    obtain ⟨a, b, c, d, v, hv, hc, hd, hb, hn⟩ :=
      branch_norm 0 hα hA hp hroot (by simpa using ht.1)
    exact ⟨d, v, hv, hn⟩
  · rintro ⟨hAo, hBo, hCe, hpell⟩
    exact triple_of_pell hroot hAo hBo hCe hpell

theorem quadratic_of_half_equiv {α : ℝ} (hα : Irrational α)
    (he : MobiusEquiv α (α / 2)) :
    ∃ A B C : ℤ, A ≠ 0 ∧ (A : ℝ) * α ^ 2 + B * α + C = 0 := by
  obtain ⟨a, b, c, d, hd, he⟩ := he
  have hr : (c : ℝ) * α ^ 2 + (d - 2 * a : ℤ) * α + (-2 * b : ℤ) = 0 := by
    push_cast
    linear_combination 2 * he
  refine ⟨c, d - 2 * a, -2 * b, ?_, hr⟩
  intro hc
  have hlin : ((d - 2 * a : ℤ) : ℝ) * α + (-2 * b : ℤ) = 0 := by
    simpa [hc] using hr
  obtain ⟨hda, hb⟩ := irrational_linear hα hlin
  have hb' : b = 0 := by omega
  have hd' : d = 2 * a := by omega
  rcases hd with hd | hd <;> rw [hc, hb', hd'] at hd
  · have he : 2 * (a * a) = 1 := by nlinarith only [hd]
    omega
  · nlinarith [sq_nonneg a]

theorem odd_square_eight {t : ℤ} (ht : Odd t) : ∃ k : ℤ, t ^ 2 = 8 * k + 1 := by
  obtain ⟨a, ha⟩ := ht
  have he : Even (a * (a + 1)) := by
    rcases Int.even_or_odd a with h | h
    · exact h.mul_right _
    · exact h.add_one.mul_left _
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp he
  refine ⟨k, ?_⟩
  rw [ha]
  linear_combination 4 * hk

theorem pell_one_mod_eight {D : ℤ} (h : SignedPellEight D) :
    ∃ k : ℤ, D = 8 * k + 1 := by
  obtain ⟨t, v, ht, hv, he⟩ := h
  obtain ⟨a, ha⟩ := odd_square_eight ht
  obtain ⟨b, hb⟩ := odd_square_eight hv
  rcases he with he | he
  · refine ⟨a - D * b - 1, ?_⟩
    linear_combination ha - D * hb - he
  · refine ⟨a - D * b + 1, ?_⟩
    linear_combination ha - D * hb - he

theorem coefficient_parity_of_pell {A B C : ℤ}
    (h : SignedPellEight (discriminant A B C)) : Odd B ∧ Even (A * C) := by
  obtain ⟨k, hk⟩ := pell_one_mod_eight h
  unfold discriminant at hk
  have hB : Odd B := by
    rcases Int.even_or_odd B with hB | hB
    · obtain ⟨b, hb⟩ := even_iff_exists_two_mul.mp hB
      have he : 4 * (b ^ 2 - A * C - 2 * k) = 1 := by
        rw [hb] at hk
        linear_combination hk
      omega
    · exact hB
  refine ⟨hB, ?_⟩
  obtain ⟨b, hb⟩ := odd_square_eight hB
  apply even_iff_exists_two_mul.mpr
  refine ⟨b - k, ?_⟩
  nlinarith only [hb, hk]

theorem fixed_representative_classification_short {α : ℝ} {A B C : ℤ}
    (hα : Irrational α) (hA : A ≠ 0) (hp : PrimitiveTriple A B C)
    (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0) :
    Triple α ↔ Odd A ∧ SignedPellEight (discriminant A B C) := by
  rw [fixed_representative_classification hα hA hp hroot]
  constructor
  · rintro ⟨ha, hb, hc, h⟩; exact ⟨ha, h⟩
  · rintro ⟨ha, h⟩
    obtain ⟨hb, hac⟩ := coefficient_parity_of_pell h
    have hc : Even C := even_of_mul_odd (by simpa [mul_comm] using hac) ha
    exact ⟨ha, hb, hc, h⟩

/-- Explicit representative normalization: keep α, invert α, or invert α+1. -/
theorem exists_triple_representative_of_pell {α : ℝ} {A B C : ℤ}
    (hα : Irrational α) (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0)
    (h : SignedPellEight (discriminant A B C)) :
    ∃ β : ℝ, MobiusEquiv α β ∧ Triple β := by
  obtain ⟨hB, hAC⟩ := coefficient_parity_of_pell h
  rcases Int.even_or_odd A with hA | hA
  · rcases Int.even_or_odd C with hC | hC
    · have hden : α + 1 ≠ 0 := by simpa using (hα.add_intCast 1).ne_zero
      have hroot' : ((A - B + C : ℤ) : ℝ) * (1 / (α + 1)) ^ 2 +
          (B - 2 * A : ℤ) * (1 / (α + 1)) + A = 0 := by
        push_cast
        field_simp [hden]
        nlinarith [hroot]
      have hd : discriminant (A - B + C) (B - 2 * A) A = discriminant A B C := by
        unfold discriminant; ring
      have ha' : Odd (A - B + C) := (hA.sub_odd hB).add_even hC
      have hb' : Odd (B - 2 * A) := hB.sub_even (even_two_mul _)
      refine ⟨1 / (α + 1), ⟨0, 1, 1, 1, Or.inr (by norm_num), ?_⟩,
        triple_of_pell hroot' ha' hb' hA (by simpa only [hd] using h)⟩
      norm_num
      exact inv_mul_cancel₀ hden
    · have hroot' : (C : ℝ) * (1 / α) ^ 2 + B * (1 / α) + A = 0 := by
        field_simp [hα.ne_zero]
        linear_combination α * hroot
      have hd : discriminant C B A = discriminant A B C := by unfold discriminant; ring
      refine ⟨1 / α, ⟨0, 1, 1, 0, Or.inr (by norm_num), ?_⟩,
        triple_of_pell hroot' hC hB hA (by simpa only [hd] using h)⟩
      norm_num
      exact inv_mul_cancel₀ hα.ne_zero
  · have hC : Even C := even_of_mul_odd (by simpa [mul_comm] using hAC) hA
    refine ⟨α, ⟨1, 0, 0, 1, Or.inl (by norm_num), by simp⟩,
      triple_of_pell hroot hA hB hC h⟩

theorem mobius_symm {α β : ℝ} (h : MobiusEquiv α β) : MobiusEquiv β α := by
  obtain ⟨a, b, c, d, hd, he⟩ := h
  refine ⟨d, -b, -c, a, ?_, ?_⟩
  · convert hd using 1 <;> ring
  · push_cast
    nlinarith only [he]

theorem irrational_of_mobius {α β : ℝ} (hα : Irrational α) (h : MobiusEquiv α β) :
    Irrational β := by
  obtain ⟨a, b, c, d, hd, he⟩ := mobius_symm h
  have hden := mobius_denominator_ne_zero hd he
  intro hb
  obtain ⟨q, hq⟩ := hb
  apply hα
  refine ⟨((a : ℚ) * q + b) / ((c : ℚ) * q + d), ?_⟩
  push_cast
  rw [hq]
  exact (eq_div_iff hden).mpr he |>.symm

def transA (A B C a b c d : ℤ) : ℤ := A * d ^ 2 - B * c * d + C * c ^ 2
def transB (A B C a b c d : ℤ) : ℤ := -2 * A * b * d + B * (a * d + b * c) - 2 * C * a * c
def transC (A B C a b c d : ℤ) : ℤ := A * b ^ 2 - B * a * b + C * a ^ 2

theorem transformed_discriminant (A B C a b c d : ℤ) :
    discriminant (transA A B C a b c d) (transB A B C a b c d) (transC A B C a b c d) =
      (a * d - b * c) ^ 2 * discriminant A B C := by
  unfold discriminant transA transB transC
  ring

theorem transformed_primitive {A B C a b c d : ℤ}
    (hp : PrimitiveTriple A B C) (hd : a * d - b * c = 1 ∨ a * d - b * c = -1) :
    PrimitiveTriple (transA A B C a b c d) (transB A B C a b c d) (transC A B C a b c d) := by
  obtain ⟨x, y, z, hp⟩ := hp
  refine ⟨x * a ^ 2 + 2 * y * a * b + z * b ^ 2,
    x * a * c + y * (a * d + b * c) + z * b * d,
    x * c ^ 2 + 2 * y * c * d + z * d ^ 2, ?_⟩
  have hd2 : (a * d - b * c) ^ 2 = 1 := by rcases hd with hd | hd <;> rw [hd] <;> norm_num
  calc
    _ = (a * d - b * c) ^ 2 * (x * A + y * B + z * C) := by
      unfold transA transB transC
      ring
    _ = 1 := by rw [hd2, hp]; norm_num

theorem transformed_root {α β : ℝ} {A B C a b c d : ℤ}
    (hr : (A : ℝ) * α ^ 2 + B * α + C = 0)
    (he : β * ((c : ℝ) * α + d) = (a : ℝ) * α + b) :
    (transA A B C a b c d : ℝ) * β ^ 2 + transB A B C a b c d * β +
      transC A B C a b c d = 0 := by
  have he' : (d : ℝ) * β - b = α * (a - c * β) := by nlinarith only [he]
  calc
    _ = A * ((d : ℝ) * β - b) ^ 2 + B * ((d : ℝ) * β - b) * (a - c * β) +
        C * ((a : ℝ) - c * β) ^ 2 := by
      unfold transA transB transC
      push_cast
      ring
    _ = ((a : ℝ) - c * β) ^ 2 * ((A : ℝ) * α ^ 2 + B * α + C) := by
      rw [he']; ring
    _ = 0 := by rw [hr]; ring

/-- Full equivalence-class classification in the explicitly defined Möbius
relation. The only missing link to the original CF wording is Serret's theorem. -/
theorem equivalence_class_classification {α : ℝ} {A B C : ℤ}
    (hα : Irrational α) (hp : PrimitiveTriple A B C)
    (hroot : (A : ℝ) * α ^ 2 + B * α + C = 0) :
    (∃ β : ℝ, MobiusEquiv α β ∧ Triple β) ↔ SignedPellEight (discriminant A B C) := by
  constructor
  · rintro ⟨β, he, ht⟩
    have hβ := irrational_of_mobius hα he
    obtain ⟨a, b, c, d, hd, he⟩ := he
    have hp' := transformed_primitive hp hd
    have hr' := transformed_root hroot he
    have hA' : transA A B C a b c d ≠ 0 := by
      intro hz
      have hl : (transB A B C a b c d : ℝ) * β + transC A B C a b c d = 0 := by
        simpa [hz] using hr'
      obtain ⟨hb, hc⟩ := irrational_linear hβ hl
      obtain ⟨x, y, z, hp'⟩ := hp'
      simp [hz, hb, hc] at hp'
    have hP := (fixed_representative_classification_short hβ hA' hp' hr').mp ht |>.2
    have hd2 : (a * d - b * c) ^ 2 = 1 := by rcases hd with hd | hd <;> rw [hd] <;> norm_num
    simpa only [transformed_discriminant, hd2, one_mul] using hP
  · exact exists_triple_representative_of_pell hα hroot

end VV.Problem3
