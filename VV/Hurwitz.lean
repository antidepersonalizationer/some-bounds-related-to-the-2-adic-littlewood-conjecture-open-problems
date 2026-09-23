import VV.Problem3
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact three-state Hurwitz transducer

All identities below are symbolic over arbitrary integer digits. `H1` means
`(x-1)/2`, not `(x+1)/2`; those two differ by an integer and have the same tail.
For positive input digits the recorded digits are nonnegative. Zero removal
is an exact matrix identity, so this module contains no computation certificate.
-/

namespace VV.Hurwitz

structure Mat where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

@[ext] theorem Mat.ext {M N : Mat} (ha : M.a = N.a) (hb : M.b = N.b)
    (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  cases M; cases N; simp_all

def one : Mat := ⟨1, 0, 0, 1⟩
def mul (M N : Mat) : Mat :=
  ⟨M.a*N.a+M.b*N.c, M.a*N.b+M.b*N.d,
   M.c*N.a+M.d*N.c, M.c*N.b+M.d*N.d⟩
def det (M : Mat) : ℤ := M.a*M.d-M.b*M.c
def digit (a : ℤ) : Mat := ⟨a,1,1,0⟩
def word : List ℤ → Mat
  | [] => one
  | a :: w => mul (digit a) (word w)

theorem mul_assoc (A B C : Mat) : mul (mul A B) C = mul A (mul B C) := by
  ext <;> simp [mul] <;> ring
@[simp] theorem one_mul (A : Mat) : mul one A = A := by ext <;> simp [mul, one]
@[simp] theorem mul_one (A : Mat) : mul A one = A := by ext <;> simp [mul, one]
theorem det_mul (A B : Mat) : det (mul A B) = det A * det B := by
  simp [det, mul]; ring
theorem word_append (u v : List ℤ) : word (u ++ v) = mul (word u) (word v) := by
  induction u with
  | nil => simp [word]
  | cons a u ih => simp only [List.cons_append, word, ih, mul_assoc]

theorem word_det_unit (w : List ℤ) : det (word w) = 1 ∨ det (word w) = -1 := by
  induction w with
  | nil => left; norm_num [word, det, one]
  | cons a w ih =>
      rw [word, det_mul]
      have hd : det (digit a) = -1 := by simp [det, digit]
      rw [hd]
      rcases ih with ih | ih
      · right; rw [ih]; ring
      · left; rw [ih]; ring

inductive State where
  | D | H0 | H1
  deriving DecidableEq, Fintype

def stateMatrix : State → Mat
  | .D => ⟨2,0,0,1⟩
  | .H0 => ⟨1,0,0,2⟩
  | .H1 => ⟨1,-1,0,2⟩

def next (s : State) (a : ℤ) : State :=
  match s with
  | .D => .H0
  | .H0 => if a % 2 = 0 then .D else .H1
  | .H1 => if a % 2 = 0 then .H1 else .D

def emit (s : State) (a : ℤ) : List ℤ :=
  match s with
  | .D => [2*a]
  | .H0 => if a % 2 = 0 then [a/2] else [a/2,1,1]
  | .H1 => if a % 2 = 0 then [a/2-1,1,1] else [a/2]

theorem next_injective (a : ℤ) : Function.Injective (fun s => next s a) := by
  intro s t h
  cases s <;> cases t <;> by_cases ha : a % 2 = 0 <;> simp_all [next]

theorem next_bijective (a : ℤ) : Function.Bijective (fun s => next s a) :=
  ⟨next_injective a, by
    intro s
    cases s
    · by_cases h : a % 2 = 0
      · exact ⟨.H0, by simp [next, h]⟩
      · exact ⟨.H1, by simp [next, h]⟩
    · exact ⟨.D, rfl⟩
    · by_cases h : a % 2 = 0
      · exact ⟨.H1, by simp [next, h]⟩
      · exact ⟨.H0, by simp [next, h]⟩⟩

theorem step_matrix (s : State) (a : ℤ) :
    mul (stateMatrix s) (digit a) = mul (word (emit s a)) (stateMatrix (next s a)) := by
  have hdiv := Int.ediv_add_emod a 2
  have hmod : a % 2 = 0 ∨ a % 2 = 1 := by omega
  cases s <;> rcases hmod with hmod | hmod <;>
    ext <;> simp [stateMatrix, digit, word, emit, next, hmod, mul, one] <;> omega

theorem emit_nonnegative (s : State) {a : ℤ} (ha : 1 ≤ a) :
    ∀ b ∈ emit s a, 0 ≤ b := by
  have hdiv := Int.ediv_add_emod a 2
  have hmod : a % 2 = 0 ∨ a % 2 = 1 := by omega
  cases s <;> rcases hmod with hmod | hmod <;>
    simp [emit, hmod] <;> omega

theorem emit_nonempty (s : State) (a : ℤ) : emit s a ≠ [] := by
  cases s <;> by_cases ha : a % 2 = 0 <;> simp [emit, ha]

def run (s : State) : List ℤ → List ℤ × State
  | [] => ([], s)
  | a :: w => let r := run (next s a) w; (emit s a ++ r.1, r.2)

theorem run_append (s : State) (u v : List ℤ) :
    run s (u ++ v) =
      ((run s u).1 ++ (run (run s u).2 v).1, (run (run s u).2 v).2) := by
  induction u generalizing s with
  | nil => simp [run]
  | cons a u ih => simp [run, ih, List.append_assoc]

theorem run_matrix (s : State) (w : List ℤ) :
    mul (stateMatrix s) (word w) = mul (word (run s w).1) (stateMatrix (run s w).2) := by
  induction w generalizing s with
  | nil => simp [run, word]
  | cons a w ih =>
      simp only [run, word, word_append]
      rw [← mul_assoc, step_matrix, mul_assoc, ih, ← mul_assoc]

theorem run_state_injective (w : List ℤ) :
    Function.Injective (fun s => (run s w).2) := by
  induction w with
  | nil => intro s t h; exact h
  | cons a w ih =>
      intro s t h
      exact next_injective a (ih h)

theorem run_nonnegative (s : State) (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a) :
    ∀ b ∈ (run s w).1, 0 ≤ b := by
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih =>
      simp only [run, List.mem_append]
      intro b hb
      rcases hb with hb | hb
      · exact emit_nonnegative s (hw a (by simp)) b hb
      · exact ih (next s a) (fun a ha => hw a (by simp [ha])) b hb

/-- Zero cleanup preserves the exact matrix, not merely the represented real. -/
theorem zero_cleanup (x y : ℤ) : word [x,0,y] = word [x+y] := by
  ext <;> simp [word, digit, mul, one]

theorem zero_cleanup_context (u v : List ℤ) (x y : ℤ) :
    word (u ++ [x,0,y] ++ v) = word (u ++ [x+y] ++ v) := by
  simp only [word_append, zero_cleanup]

inductive CleansTo : List ℤ → List ℤ → Prop where
  | refl (u) : CleansTo u u
  | step (u v) (x y) : CleansTo (u ++ [x,0,y] ++ v) (u ++ [x+y] ++ v)
  | trans {u v w} : CleansTo u v → CleansTo v w → CleansTo u w

theorem CleansTo.word_eq {u v : List ℤ} (h : CleansTo u v) : word u = word v := by
  induction h with
  | refl => rfl
  | step => exact zero_cleanup_context _ _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def EvenVec (M : Mat) (u v : ℤ) : Prop :=
  Even (M.a*u+M.b*v) ∧ Even (M.c*u+M.d*v)

theorem evenVec_cancel_left {N M : Mat} {u v : ℤ}
    (hdet : det N = 1 ∨ det N = -1) (h : EvenVec (mul N M) u v) : EvenVec M u v := by
  let x := M.a*u+M.b*v
  let y := M.c*u+M.d*v
  have h₁ : Even (N.a*x+N.b*y) := by
    convert h.1 using 1 <;> simp [x, y, mul] <;> ring
  have h₂ : Even (N.c*x+N.d*y) := by
    convert h.2 using 1 <;> simp [x, y, mul] <;> ring
  have hd : Odd (det N) := by
    rcases hdet with hd | hd
    · rw [hd]; exact odd_one
    · rw [hd]; exact odd_one.neg
  have hx : Even (x * det N) := by
    convert (h₁.mul_left N.d).sub (h₂.mul_left N.b) using 1 <;> simp [det] <;> ring
  have hy : Even (y * det N) := by
    convert (h₂.mul_left N.a).sub (h₁.mul_left N.c) using 1 <;> simp [det] <;> ring
  exact ⟨Problem3.even_of_mul_odd hx hd, Problem3.even_of_mul_odd hy hd⟩

def kernelU : State → ℤ
  | .D => 1
  | .H0 => 0
  | .H1 => 1
def kernelV : State → ℤ
  | .D => 0
  | .H0 => 1
  | .H1 => 1

theorem state_kernel_unique (s t : State)
    (h : EvenVec (stateMatrix t) (kernelU s) (kernelV s)) : t = s := by
  cases s <;> cases t <;> simp_all [EvenVec, stateMatrix, kernelU, kernelV]

/-- A period matrix congruent to the identity modulo two returns all three
Hurwitz states to their initial state. -/
theorem run_state_closed_of_parity (w : List ℤ)
    (ha : Odd (word w).a) (hb : Even (word w).b)
    (hc : Even (word w).c) (hd : Odd (word w).d) (s : State) : (run s w).2 = s := by
  have hvec : EvenVec (mul (stateMatrix s) (word w)) (kernelU s) (kernelV s) := by
    cases s
    · constructor
      · simpa [mul, stateMatrix, kernelU, kernelV] using even_two_mul (word w).a
      · simpa [mul, stateMatrix, kernelU, kernelV] using hc
    · constructor
      · simpa [mul, stateMatrix, kernelU, kernelV] using hb
      · simpa [mul, stateMatrix, kernelU, kernelV] using even_two_mul (word w).d
    · constructor
      · have he := ((ha.sub_odd hd).add hb).sub hc
        convert he using 1 <;> simp [mul, stateMatrix, kernelU, kernelV] <;> ring
      · simpa [mul, stateMatrix, kernelU, kernelV, mul_add] using
          even_two_mul ((word w).c+(word w).d)
  rw [run_matrix] at hvec
  exact state_kernel_unique s _ (evenVec_cancel_left (word_det_unit _) hvec)

theorem norm_unit_parity {A B C s v : ℤ} (hB : Odd B) (hAC : Even (A*C))
    (hn : Problem3.normForm A B C s v = 1 ∨ Problem3.normForm A B C s v = -1) :
    Even v ∧ Odd s := by
  have hodd : Odd (Problem3.normForm A B C s v) := by
    rcases hn with hn | hn
    · rw [hn]; exact odd_one
    · rw [hn]; exact odd_one.neg
  have hnot := Int.not_even_iff_odd.mpr hodd
  have hlast : Even (A*C*v^2) := hAC.mul_right _
  have hv : Even v := by
    rcases Int.even_or_odd v with hv | hv
    · exact hv
    · exfalso
      apply hnot
      rcases Int.even_or_odd s with hs | hs
      · exact ((hs.pow_of_ne_zero (by decide : (2:ℕ) ≠ 0)).sub
          ((hs.mul_left B).mul_right v)).add hlast
      · exact ((hs.pow (n := 2)).sub_odd ((hB.mul hs).mul hv)).add hlast
  refine ⟨hv, Int.not_even_iff_odd.mp ?_⟩
  intro hs
  exact hnot (((hs.pow_of_ne_zero (by decide : (2:ℕ) ≠ 0)).sub
    (hv.mul_left (B*s))).add hlast)

/-- Every unimodular stabilizer of a primitive quadratic with the admissible
Pell certificate is the identity modulo two. -/
theorem stabilizer_parity {α : ℝ} {A B C : ℤ} (M : Mat)
    (hα : Irrational α) (hA : A ≠ 0) (hp : Problem3.PrimitiveTriple A B C)
    (hroot : (A:ℝ)*α^2+B*α+C=0)
    (hpell : Problem3.SignedPellEight (Problem3.discriminant A B C))
    (hdet : det M = 1 ∨ det M = -1)
    (hfix : α*((M.c:ℝ)*α+M.d)=(M.a:ℝ)*α+M.b) :
    Odd M.a ∧ Even M.b ∧ Even M.c ∧ Odd M.d := by
  have hrel : (M.c:ℝ)*α^2+(M.d-M.a:ℤ)*α+(-M.b:ℤ)=0 := by
    push_cast
    linear_combination hfix
  obtain ⟨v, hc, hd, hb⟩ := Problem3.relation_multiple hα hA hp hroot hrel
  have hn : Problem3.normForm A B C M.d v = det M := by
    unfold Problem3.normForm det
    linear_combination M.d*hd-M.c*hb-C*v*hc
  obtain ⟨hB, hAC⟩ := Problem3.coefficient_parity_of_pell hpell
  have hnorm : Problem3.normForm A B C M.d v = 1 ∨
      Problem3.normForm A B C M.d v = -1 := by simpa only [hn] using hdet
  obtain ⟨hv, hs⟩ := norm_unit_parity hB hAC hnorm
  refine ⟨?_, ?_, ?_, hs⟩
  · have he : M.a = M.d-B*v := by omega
    rw [he]
    exact hs.sub_even (hv.mul_left B)
  · have he : M.b = -(C*v) := by omega
    rw [he]
    exact (hv.mul_left C).neg
  · rw [hc]
    exact hv.mul_left A

end VV.Hurwitz
