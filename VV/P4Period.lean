import VV.P4Trace
import VV.Problem4Real

/-! Exact least periods of genuine positive continued-fraction cycles. -/

namespace VV.Hurwitz

def DigitPeriod (x : ℝ) (p : ℕ) : Prop :=
  ∀ n : ℕ, partialQuotient x (n+p) = partialQuotient x n

theorem nat_period_mul {α : Type*} {f : ℕ → α} {p : ℕ}
    (h : ∀ n, f (n+p) = f n) (n k : ℕ) : f (n+p*k) = f n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, h, ih]

theorem nat_period_mod {α : Type*} {f : ℕ → α} {p q : ℕ}
    (hp : ∀ n, f (n+p) = f n) (hq : ∀ n, f (n+q) = f n) :
    ∀ n, f (n+q%p) = f n := by
  intro n
  have he := nat_period_mul hp (n+q%p) (q/p)
  rw [Nat.add_assoc, Nat.mod_add_div] at he
  exact he.symm.trans (hq n)

theorem DigitPeriod.eventual {x : ℝ} {p : ℕ} (h : DigitPeriod x p) :
    Problem4.EventualPeriod x p := by
  refine ⟨0, fun n _ => ?_⟩
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (n+1)

theorem DigitPeriod.of_eventual {x : ℝ} {p q : ℕ} (hp : 0 < p)
    (h : DigitPeriod x p) (hq : Problem4.EventualPeriod x q) : DigitPeriod x q := by
  obtain ⟨N,hN⟩ := hq
  intro n
  have hbig : N+2 ≤ p*(N+2) := by nlinarith
  have he := hN (n+p*(N+2)-1) (by omega)
  have h₁ : n+p*(N+2)-1+q+1 = n+q+p*(N+2) := by omega
  have h₂ : n+p*(N+2)-1+1 = n+p*(N+2) := by omega
  rw [h₁,h₂,nat_period_mul h,nat_period_mul h] at he
  exact he

theorem DigitPeriod.minimal_dvd {x : ℝ} {p ℓ : ℕ} (hp : 0 < p)
    (h : DigitPeriod x p) (hℓ : Problem4.ExactEventualPeriod x ℓ) : ℓ ∣ p := by
  have hmin := h.of_eventual hp hℓ.2.1
  have hrem : DigitPeriod x (p%ℓ) := nat_period_mod hmin h
  apply Nat.dvd_of_mod_eq_zero
  by_contra hn
  exact hℓ.2.2 (p%ℓ) (by omega) (Nat.mod_lt _ hℓ.1) hrem.eventual

theorem CycleModel.gt_one {x : ℝ} {w : List ℤ} (h : CycleModel x w)
    (hw : ∀ a ∈ w, 1 ≤ a) : 1 < x := by
  cases w with
  | nil => simpa [word, one, trace] using h.hyperbolic
  | cons a w =>
      have ha : (1:ℝ) ≤ a := by exact_mod_cast hw a (by simp)
      have ht := value_pos w h.positive (fun b hb => h.digits b (by simp [hb]))
      have hf := h.fixed
      change (a:ℝ)+(value w x)⁻¹=x at hf
      linarith [inv_pos.mpr ht]

theorem CycleModel.digitBlock {x : ℝ} {w : List ℤ} (h : CycleModel x w)
    (hw : ∀ a ∈ w, 1 ≤ a) : P5Period.digitBlock x 0 w.length = w := by
  simpa only [h.fixed] using value_digitBlock w (h.gt_one hw) hw

theorem CycleModel.digitPeriod {x : ℝ} {w : List ℤ} (h : CycleModel x w)
    (hw : ∀ a ∈ w, 1 ≤ a) : DigitPeriod x w.length := by
  have he : completeQuotient x w.length = x := by
    simpa only [h.fixed] using value_complete_length w (h.gt_one hw) hw
  intro n
  simp only [partialQuotient]
  rw [Nat.add_comm n, ← completeQuotient_add, he]

theorem digitBlock_eq_of_digits_eq {x y : ℝ} {m n : ℕ}
    (h : ∀ k, partialQuotient x (m+k) = partialQuotient y (n+k)) (p : ℕ) :
    P5Period.digitBlock x m p = P5Period.digitBlock y n p := by
  rw [P5Period.digitBlock_eq_ofFn, P5Period.digitBlock_eq_ofFn]
  exact congrArg List.ofFn (funext fun i => h i.val)

theorem trace_digitBlock_shift {x : ℝ} {p : ℕ} (hp : DigitPeriod x p) (n : ℕ) :
    trace (word (P5Period.digitBlock x (n+1) p)) =
      trace (word (P5Period.digitBlock x n p)) := by
  cases p with
  | zero => rfl
  | succ p =>
      have he : P5Period.digitBlock x (n+1) (p+1) =
          P5Period.digitBlock x (n+1) p ++ [partialQuotient x n] := by
        rw [P5Period.digitBlock_append]
        simp only [P5Period.digitBlock, List.append_nil]
        congr 2
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp n
      rw [he]
      change trace (word (P5Period.digitBlock x (n+1) p ++ [partialQuotient x n])) =
        trace (word ([partialQuotient x n] ++ P5Period.digitBlock x (n+1) p))
      exact trace_word_rotate _ _

theorem trace_digitBlock_shift_all {x : ℝ} {p : ℕ} (hp : DigitPeriod x p) (n : ℕ) :
    trace (word (P5Period.digitBlock x n p)) =
      trace (word (P5Period.digitBlock x 0 p)) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (trace_digitBlock_shift hp n).trans ih

theorem trace_digitBlock_eq_of_tailEquivalent {x y : ℝ} {p : ℕ}
    (hx : DigitPeriod x p) (hy : DigitPeriod y p) (hxy : TailEquivalent x y) :
    trace (word (P5Period.digitBlock x 0 p)) =
      trace (word (P5Period.digitBlock y 0 p)) := by
  obtain ⟨m,n,h⟩ := hxy
  have he : ∀ k, partialQuotient x (m+1+k) = partialQuotient y (n+1+k) := by
    intro k
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h k
  calc
    _ = trace (word (P5Period.digitBlock x (m+1) p)) :=
      (trace_digitBlock_shift_all hx _).symm
    _ = trace (word (P5Period.digitBlock y (n+1) p)) := by
      rw [digitBlock_eq_of_digits_eq he]
    _ = _ := trace_digitBlock_shift_all hy _

theorem digitBlock_positive_of_gt_one {x : ℝ} (hx : Irrational x) (hgt : 1 < x)
    (n p : ℕ) : ∀ a ∈ P5Period.digitBlock x n p, 1 ≤ a := by
  have hall : ∀ k, 1 ≤ partialQuotient x k := by
    intro k
    cases k with
    | zero =>
        change 1 ≤ ⌊x⌋
        exact Int.le_floor.mpr (by simpa using le_of_lt hgt)
    | succ k => exact one_le_partialQuotient_succ hx k
  rw [P5Period.digitBlock_eq_ofFn]
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact hall _

/-- A normalized Hurwitz output in the same tail class contains exactly one
least input period. The statement needs no presumed output-length bound:
trace alone excludes every nontrivial repetition. -/
theorem equal_length_of_cycle_trace {x y : ℝ} {w v : List ℤ}
    (hx : CycleModel x w) (hy : CycleModel y v)
    (hw : ∀ a ∈ w, 1 ≤ a) (hv : ∀ a ∈ v, 1 ≤ a)
    (hmin : Problem4.ExactEventualPeriod x w.length) (hlen : 2 ≤ w.length)
    (hxy : TailEquivalent x y) (htrace : trace (word v) = trace (word w)) :
    v.length = w.length := by
  have hminy := (Problem4.exactEventualPeriod_iff_of_tailEquivalent hxy w.length).mp hmin
  have hpos : 0 < v.length := by
    by_contra hn
    have he : v = [] := List.length_eq_zero_iff.mp (by omega)
    simpa [he, word, one, trace] using hy.hyperbolic
  have hyp := hy.digitPeriod hv
  have hyd := hyp.minimal_dvd hpos hminy
  obtain ⟨k,hk⟩ := hyd
  have hyl := hyp.of_eventual hpos hminy.2.1
  have he : v = (List.replicate k (P5Period.digitBlock y 0 w.length)).flatten := by
    rw [← hy.digitBlock hv, hk]
    apply P5Period.digitBlock_repeat
    intro n
    simpa only [Nat.zero_add, Nat.add_comm] using hyl n
  have hbase : trace (word (P5Period.digitBlock y 0 w.length)) = trace (word w) := by
    calc
      _ = trace (word (P5Period.digitBlock x 0 w.length)) :=
        (trace_digitBlock_eq_of_tailEquivalent (hx.digitPeriod hw) hyl hxy).symm
      _ = _ := congrArg (fun u => trace (word u)) (hx.digitBlock hw)
  have hrep : trace (word ((List.replicate k (P5Period.digitBlock y 0 w.length)).flatten)) =
      trace (word (P5Period.digitBlock y 0 w.length)) := by
    rw [← he,hbase,htrace]
  have hk1 := (trace_repeat_eq_iff _
    (digitBlock_positive_of_gt_one hy.irrational (hy.gt_one hv) 0 w.length)
    (by simpa only [P5Period.digitBlock_length] using hlen) k).mp hrep
  simpa [hk1] using hk

end VV.Hurwitz
