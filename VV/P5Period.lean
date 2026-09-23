import VV.TailMobius
import VV.Problem5Real
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Sigma

/-!
The infinite theoretical step from an actual eventually periodic digit
tail to a primitive quadratic equation, retaining its discriminant.
Nothing in this file is a finite-computation assumption.
-/

namespace VV.P5Period
open QuadraticScaling Problem3

structure PrefixMatrix where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

def identity : PrefixMatrix := ⟨1, 0, 0, 1⟩

def prepend (a : ℤ) (M : PrefixMatrix) : PrefixMatrix :=
  ⟨a * M.a + M.c, a * M.b + M.d, M.a, M.b⟩

def matrix : List ℤ → PrefixMatrix
  | [] => identity
  | a :: w => prepend a (matrix w)

def periodQuadratic (w : List ℤ) : Quadratic :=
  let M := matrix w
  ⟨M.c, M.d - M.a, -M.b⟩

noncomputable def digitBlock (x : ℝ) (n : ℕ) : ℕ → List ℤ
  | 0 => []
  | p + 1 => partialQuotient x n :: digitBlock x (n + 1) p

theorem digitBlock_length (x : ℝ) (n p : ℕ) : (digitBlock x n p).length = p := by
  induction p generalizing n with
  | zero => rfl
  | succ p ih => simp only [digitBlock, List.length_cons, ih]

theorem digitBlock_positive {x : ℝ} (hx : Irrational x) (n p : ℕ)
    (hn : 0 < n) : ∀ a ∈ digitBlock x n p, 1 ≤ a := by
  induction p generalizing n with
  | zero => simp [digitBlock]
  | succ p ih =>
      intro a ha
      simp only [digitBlock, List.mem_cons] at ha
      rcases ha with rfl | ha
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        exact one_le_partialQuotient_succ hx m
      · exact ih (n + 1) (by omega) a ha

theorem matrix_positive (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a) :
    1 ≤ (matrix w).a ∧ 0 ≤ (matrix w).b ∧
      0 ≤ (matrix w).c ∧ 0 ≤ (matrix w).d := by
  induction w with
  | nil => norm_num [matrix, identity]
  | cons a w ih =>
      have ha := hw a (by simp)
      obtain ⟨hA, hB, hC, hD⟩ := ih (fun b hb => hw b (by simp [hb]))
      dsimp [matrix, prepend]
      refine ⟨?_, ?_, by omega, hB⟩
      · nlinarith
      · exact add_nonneg (mul_nonneg (by omega) hB) hD

theorem periodQuadratic_A_pos (w : List ℤ) (h : w ≠ [])
    (hw : ∀ a ∈ w, 1 ≤ a) : 0 < (periodQuadratic w).A := by
  cases w with
  | nil => exact False.elim (h rfl)
  | cons a w =>
      have ha := (matrix_positive w (fun b hb => hw b (by simp [hb]))).1
      exact lt_of_lt_of_le (by decide : (0 : ℤ) < 1) ha

theorem completeQuotient_step {x : ℝ} (hx : Irrational x) (n : ℕ) :
    completeQuotient x n * completeQuotient x (n + 1) =
      (partialQuotient x n : ℝ) * completeQuotient x (n + 1) + 1 := by
  have hn := completeQuotient_fract_ne_zero hx n
  have h := mul_inv_cancel₀ hn
  simp only [completeQuotient, partialQuotient] at h ⊢
  simp only [Int.fract] at h ⊢
  linear_combination h

theorem digitBlock_realizes {x : ℝ} (hx : Irrational x) (n p : ℕ) :
    let M := matrix (digitBlock x n p)
    completeQuotient x n *
        ((M.c : ℝ) * completeQuotient x (n + p) + M.d) =
      (M.a : ℝ) * completeQuotient x (n + p) + M.b := by
  induction p generalizing n with
  | zero => simp [digitBlock, matrix, identity]
  | succ p ih =>
      let M := matrix (digitBlock x (n + 1) p)
      have hs : completeQuotient x (n + 1) *
          ((M.c : ℝ) * completeQuotient x (n + (p + 1)) + M.d) =
        (M.a : ℝ) * completeQuotient x (n + (p + 1)) + M.b := by
        simpa [M, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1)
      have ht := completeQuotient_step hx n
      change completeQuotient x n *
          ((M.a : ℝ) * completeQuotient x (n + (p + 1)) + M.b) =
        ((partialQuotient x n * M.a + M.c : ℤ) : ℝ) *
          completeQuotient x (n + (p + 1)) +
        ((partialQuotient x n * M.b + M.d : ℤ) : ℝ)
      push_cast
      linear_combination
        ((M.c : ℝ) * completeQuotient x (n + (p + 1)) + M.d) * ht +
        ((partialQuotient x n : ℝ) - completeQuotient x n) * hs

theorem completeQuotient_eq_of_periodic {x : ℝ} (hx : Irrational x)
    (n p : ℕ)
    (hper : ∀ k : ℕ, partialQuotient x (n + p + k) = partialQuotient x (n + k)) :
    completeQuotient x (n + p) = completeQuotient x n := by
  apply CylinderGeometry.eq_of_all_partialQuotients_eq
    (completeQuotient_irrational hx _) (completeQuotient_irrational hx _)
  intro k
  simpa only [partialQuotient, completeQuotient_add] using hper k

theorem periodQuadratic_root {x : ℝ} (hx : Irrational x) (n p : ℕ)
    (hper : ∀ k : ℕ, partialQuotient x (n + p + k) = partialQuotient x (n + k)) :
    (periodQuadratic (digitBlock x n p)).eval (completeQuotient x n) = 0 := by
  have hr := digitBlock_realizes hx n p
  have he := completeQuotient_eq_of_periodic hx n p hper
  rw [he] at hr
  dsimp [periodQuadratic, Quadratic.eval]
  push_cast
  linear_combination hr

/-- Move a primitive equation through an actual unimodular equivalence;
the discriminant is preserved exactly, including its sign. -/
theorem transport_primitive_equation {x y : ℝ} (hx : Irrational x)
    (hxy : MobiusEquiv x y) (Q : Quadratic)
    (hp : PrimitiveTriple Q.A Q.B Q.C) (hr : Q.eval y = 0) :
    ∃ R : Quadratic, R.A ≠ 0 ∧ PrimitiveTriple R.A R.B R.C ∧
      R.eval x = 0 ∧ R.disc = Q.disc := by
  obtain ⟨a, b, c, d, hdet, he⟩ := mobius_symm hxy
  let R : Quadratic := ⟨transA Q.A Q.B Q.C a b c d,
    transB Q.A Q.B Q.C a b c d, transC Q.A Q.B Q.C a b c d⟩
  have hpR : PrimitiveTriple R.A R.B R.C := transformed_primitive hp hdet
  have hrR : R.eval x = 0 := transformed_root hr he
  refine ⟨R, A_ne_zero_of_primitive_irrational_root R hx hrR hpR, hpR, hrR, ?_⟩
  change discriminant (transA Q.A Q.B Q.C a b c d)
      (transB Q.A Q.B Q.C a b c d) (transC Q.A Q.B Q.C a b c d) =
    discriminant Q.A Q.B Q.C
  rw [transformed_discriminant]
  rcases hdet with hdet | hdet <;> rw [hdet] <;> norm_num

theorem primitive_equation_of_periodic_tail {x : ℝ} (hx : Irrational x)
    (n p : ℕ) (hn : 0 < n) (hp : 0 < p)
    (hper : ∀ k : ℕ, partialQuotient x (n + p + k) = partialQuotient x (n + k)) :
    ∃ R : Quadratic, R.A ≠ 0 ∧ PrimitiveTriple R.A R.B R.C ∧ R.eval x = 0 ∧
      R.disc = (periodQuadratic (digitBlock x n p)).normalize.disc := by
  let Q := periodQuadratic (digitBlock x n p)
  have hne : digitBlock x n p ≠ [] := by
    intro h
    have := digitBlock_length x n p
    rw [h, List.length_nil] at this
    omega
  have hA : Q.A ≠ 0 := (periodQuadratic_A_pos _ hne (digitBlock_positive hx n p hn)).ne'
  exact transport_primitive_equation hx (mobius_completeQuotient hx n) Q.normalize
    (normalize_primitive Q hA) (normalize_root Q hA (periodQuadratic_root hx n p hper))

theorem digitBlock_eq_ofFn (x : ℝ) (n p : ℕ) :
    digitBlock x n p = List.ofFn (fun i : Fin p => partialQuotient x (n + i.val)) := by
  induction p generalizing n with
  | zero => simp [digitBlock]
  | succ p ih =>
      rw [digitBlock, List.ofFn_succ]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
      rw [ih]
      congr 1
      apply congrArg List.ofFn
      funext i
      congr 1
      omega

/-- An actual periodic tail with a uniform bound on its period and digits. -/
def BoundedPeriod (x : ℝ) (C K : ℕ) : Prop :=
  ∃ n p : ℕ, 0 < n ∧ 0 < p ∧ p ≤ K ∧
    (∀ k : ℕ, partialQuotient x (n + p + k) = partialQuotient x (n + k)) ∧
    (∀ k : ℕ, partialQuotient x (n + k) ≤ (C : ℤ))

abbrev WordCode (C K : ℕ) := Σ p : Fin (K + 1), Fin p.val → Fin (C + 1)

def decode {C K : ℕ} (w : WordCode C K) : List ℤ :=
  List.ofFn (fun i : Fin w.1.val => ((w.2 i).val : ℤ))

def codeDiscriminant {C K : ℕ} (w : WordCode C K) : ℕ :=
  (periodQuadratic (decode w)).normalize.disc.natAbs

noncomputable def discriminantTable (C K : ℕ) : Finset ℕ :=
  Finset.univ.image (codeDiscriminant (C := C) (K := K))

/-- All bounded periodic tails use a fixed finite discriminant table. No
period list is enumerated, no Lagrange theorem is assumed, and the finite
exceptional prefix does not enlarge the table. -/
theorem finite_discriminants_of_bounded_period (C K : ℕ) {x : ℝ}
    (hx : Irrational x) (h : BoundedPeriod x C K) :
    ∃ R : Quadratic, R.A ≠ 0 ∧ PrimitiveTriple R.A R.B R.C ∧ R.eval x = 0 ∧
      R.disc.natAbs ∈ discriminantTable C K := by
  classical
  obtain ⟨n, p, hn, hp, hpK, hper, hbound⟩ := h
  let code : WordCode C K := ⟨⟨p, by omega⟩,
    fun i => ⟨(partialQuotient x (n + i.val)).toNat,
      Nat.lt_succ_of_le (Int.toNat_le.mpr (hbound i.val))⟩⟩
  have heq : decode code = digitBlock x n p := by
    rw [digitBlock_eq_ofFn]
    apply congrArg List.ofFn
    funext i
    change ((partialQuotient x (n + i.val)).toNat : ℤ) = partialQuotient x (n + i.val)
    apply Int.toNat_of_nonneg
    have hpos : 0 < n + i.val := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n + i.val ≠ 0)
    rw [hm]
    exact (show (0 : ℤ) ≤ 1 by decide).trans (one_le_partialQuotient_succ hx m)
  obtain ⟨R, hA, hprim, hroot, hdisc⟩ := primitive_equation_of_periodic_tail hx n p hn hp hper
  refine ⟨R, hA, hprim, hroot, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨code, Finset.mem_univ _, ?_⟩
  simp only [codeDiscriminant, heq, hdisc]

/-- This reduction removes the periodic-tail-to-quadratic and finite-table
theory from the Problem 5 graph task. The remaining statement concerns
actual periodic digit tails, not a black-box discriminant invariant. -/
theorem windowClassification_of_bounded_period
    (K : ℕ)
    (h : ∀ x : ℝ, Irrational x →
      (∀ k : ℕ, k ≤ 30 → EventualBound ((2 : ℝ) ^ k * x) 10) →
      BoundedPeriod ((2 : ℝ) ^ 15 * x) 10 K) :
    Problem5Real.WindowClassification := by
  refine ⟨discriminantTable 10 K, ?_⟩
  intro x hx hlow
  obtain ⟨R, _, hprim, hroot, hdisc⟩ := finite_discriminants_of_bounded_period
    10 K (irrational_dyadic_mul hx 15) (h x hx hlow)
  exact ⟨R, hroot, hprim, hdisc⟩

theorem digitBlock_append (x : ℝ) (n p q : ℕ) :
    digitBlock x n (p + q) = digitBlock x n p ++ digitBlock x (n + p) q := by
  induction p generalizing n with
  | zero => simp [digitBlock]
  | succ p ih =>
      simp only [Nat.succ_add, digitBlock, List.cons_append]
      rw [ih]
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem digitBlock_periodic_shift (x : ℝ) (n p q : ℕ)
    (hper : ∀ k : ℕ, partialQuotient x (n + p + k) = partialQuotient x (n + k)) :
    digitBlock x (n + p) q = digitBlock x n q := by
  rw [digitBlock_eq_ofFn, digitBlock_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  exact hper i.val

theorem digitBlock_repeat (x : ℝ) (n p k : ℕ)
    (hper : ∀ j : ℕ, partialQuotient x (n + p + j) = partialQuotient x (n + j)) :
    digitBlock x n (p * k) = (List.replicate k (digitBlock x n p)).flatten := by
  induction k with
  | zero => simp [digitBlock]
  | succ k ih =>
      rw [Nat.mul_succ, Nat.add_comm (p * k) p, digitBlock_append]
      rw [digitBlock_periodic_shift x n p (p * k) hper, ih]
      simp only [List.replicate_succ, List.flatten_cons]

end VV.P5Period
