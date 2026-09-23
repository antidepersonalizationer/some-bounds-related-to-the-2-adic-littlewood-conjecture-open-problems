import VV.P5Coverage
import VV.P5TailAlignment
import VV.P5MachineGraph

/-! Actual real-number coverage of each iterated synchronization machine. -/

open Filter

namespace VV.P5Window
open P5Synchronize P5Coverage P5Machine P5TailAlignment

theorem digitValue_injective (C : ℕ) : Function.Injective (@digitValue C) := by
  intro a b h
  apply Fin.ext
  dsimp [digitValue] at h
  omega

/-- Lift three genuine traces after aligning their independently chosen
finite prefixes. The two actual output reals and their cofinal positions
are preserved. -/
theorem realTrace_lift {C : ℕ} {V : Type} {s : Step V (Fin C)}
    {x y z xl xr yl yr zl zr : ℝ}
    (t : RealTrace C V s x y z) (l : RealTrace C V s xl yl yr)
    (r : RealTrace C V s xr zl zr)
    (hyl : TailEquivalent y xl) (hzr : TailEquivalent z xr) :
    Nonempty (RealTrace C (V × V × V) (lift s) x y z) := by
  obtain ⟨a,b,hal⟩ := alignment_of_tailEquivalent digitValue hyl l.input l.start
    (fun n => (l.input_digits n).symm)
  obtain ⟨c,d,har⟩ := alignment_of_tailEquivalent digitValue hzr r.input r.start
    (fun n => (r.input_digits n).symm)
  have hLc : Tendsto t.L atTop atTop := tendsto_atTop.2
    (fun K => eventually_atTop.mpr (t.L_cofinal K))
  have hRc : Tendsto t.R atTop atTop := tendsto_atTop.2
    (fun K => eventually_atTop.mpr (t.R_cofinal K))
  obtain ⟨N, combined, ht⟩ := eventually_trace_lift s digitValue (digitValue_injective C)
    t.input l.input r.input t.state l.state r.state t.left t.right l.left l.right r.left r.right
    t.trace l.trace r.trace y z t.L t.R a b c d hal har t.L_succ t.R_succ hLc hRc
    t.left_digits t.right_digits
  refine ⟨{
    start := t.start + N
    start_pos := by have := t.start_pos; omega
    input := fun n => t.input (N + n)
    state := combined
    left := fun n => t.left (N + n)
    right := fun n => t.right (N + n)
    L := fun n => t.L (N + n)
    R := fun n => t.R (N + n)
    trace := ht
    input_digits := fun n => by simpa only [Nat.add_assoc] using t.input_digits (N + n)
    left_digits := fun n => t.left_digits (N + n)
    right_digits := fun n => t.right_digits (N + n)
    L_succ := fun n => by simpa only [Nat.add_assoc] using t.L_succ (N + n)
    R_succ := fun n => by simpa only [Nat.add_assoc] using t.R_succ (N + n)
    L_cofinal := ?_
    R_cofinal := ?_
  }⟩
  · intro K
    obtain ⟨M,hM⟩ := t.L_cofinal K
    exact ⟨M,fun n hn => hM (N + n) (by omega)⟩
  · intro K
    obtain ⟨M,hM⟩ := t.R_cofinal K
    exact ⟨M,fun n hn => hM (N + n) (by omega)⟩

def Coverage {C : ℕ} {V : Type} (s : Step V (Fin C)) (x : ℝ) : Prop :=
  ∃ y z : ℝ, TailEquivalent y (x / 2) ∧ TailEquivalent z (2 * x) ∧
    Nonempty (RealTrace C V s x y z)

theorem coverage_lift {C : ℕ} {V : Type} {s : Step V (Fin C)} {x : ℝ}
    (hc : Coverage s x) (hl : Coverage s (x / 2)) (hr : Coverage s (2 * x)) :
    Coverage (lift s) x := by
  obtain ⟨y,z,hy,hz,⟨t⟩⟩ := hc
  obtain ⟨yl,yr,_,_,⟨l⟩⟩ := hl
  obtain ⟨zl,zr,_,_,⟨r⟩⟩ := hr
  exact ⟨y,z,hy,hz,realTrace_lift t l r hy hz⟩

theorem coverage_zero {C : ℕ} {x : ℝ} (hx : Irrational x)
    (h : ∀ k : ℕ, k ≤ 2 → EventualBound ((2 : ℝ) ^ k * x) C) :
    Coverage (step C) ((2 : ℝ) * x) := by
  apply base_coverage (by simpa using irrational_dyadic_mul hx 1)
  · simpa using h 1 (by omega)
  · simpa using h 0 (by omega)
  · convert h 2 (by omega) using 1; ring

/-- At recursion depth `r`, the actual synchronized machine covers the
center of every bounded window of radius `r+1`. This induction removes
independent finite prefixes at each synchronization step. -/
theorem coverage_iterate (C r : ℕ) {x : ℝ} (hx : Irrational x)
    (h : ∀ k : ℕ, k ≤ 2 * (r + 1) → EventualBound ((2 : ℝ) ^ k * x) C) :
    Coverage (iterate (step C) r) ((2 : ℝ) ^ (r + 1) * x) := by
  induction r generalizing x with
  | zero => simpa only [iterate, Nat.zero_add, pow_one] using coverage_zero hx (by simpa using h)
  | succ r ih =>
    have hshift (j : ℕ) (hj : j ≤ 2) :
        ∀ k : ℕ, k ≤ 2 * (r + 1) →
          EventualBound ((2 : ℝ) ^ k * ((2 : ℝ) ^ j * x)) C := by
      intro k hk
      simpa only [pow_add, mul_assoc] using h (k + j) (by omega)
    have hc := ih (irrational_dyadic_mul hx 1) (hshift 1 (by omega))
    have hl := ih hx (fun k hk => h k (by omega))
    have hr := ih (irrational_dyadic_mul hx 2) (hshift 2 (by omega))
    have hcenter : (2 : ℝ) ^ (r + 1) * ((2 : ℝ) ^ 1 * x) =
        (2 : ℝ) ^ (r + 1 + 1) * x := by rw [pow_succ]; ring
    rw [hcenter] at hc
    change Coverage (lift (iterate (step C) r)) ((2 : ℝ) ^ (r + 1 + 1) * x)
    apply coverage_lift hc
    · convert hl using 1; rw [pow_succ]; ring
    · convert hr using 1; rw [pow_succ]; ring

instance stateAtDecidableEq (V : Type) [DecidableEq V] (n : ℕ) :
    DecidableEq (StateAt V n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq V)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (StateAt V n × StateAt V n × StateAt V n))

noncomputable def windowGraph (C r : ℕ) : P5Graph.Graph := by
  letI : DecidableEq (StateAt (Pair C) r) := stateAtDecidableEq (Pair C) r
  exact P5MachineGraph.graph C (iterate (step C) r)

/-- The concrete finite graph reads the genuine middle CF tail of the
bounded dyadic window. No graph-coverage assumption remains. -/
theorem windowGraph_realizes (C r : ℕ) {x : ℝ} (hx : Irrational x)
    (h : ∀ k : ℕ, k ≤ 2 * (r + 1) → EventualBound ((2 : ℝ) ^ k * x) C) :
    (windowGraph C r).Realizes ((2 : ℝ) ^ (r + 1) * x) := by
  letI : DecidableEq (StateAt (Pair C) r) := stateAtDecidableEq (Pair C) r
  obtain ⟨y,z,_,_,⟨t⟩⟩ := coverage_iterate C r hx h
  exact P5MachineGraph.realizes_of_trace C (iterate (step C) r) t.input t.state t.left t.right
    t.trace t.start t.start_pos (fun n => by
      simpa only [digitValue, Nat.cast_add, Nat.cast_one] using (t.input_digits n).symm)

/-- Radius 15 is exactly the original 31-layer hypothesis. The only
remaining graph premise is a finite Boolean rank check on a specified
machine, not an infinite-path or real-number classification premise. -/
theorem problem5_of_finite_window_check
    (hfinite : (windowGraph 10 14).checkEventuallyDeterministic = true) :
    Problem5Statement := by
  letI : DecidableEq (StateAt (Pair 10) 14) := stateAtDecidableEq (Pair 10) 14
  apply P5MachineGraph.problem5_of_machine (iterate (step 10) 14) hfinite
  intro x hx h
  exact windowGraph_realizes 10 14 hx h

def encodedWindowGraph (C r : ℕ) {n : ℕ}
    (code : P5MachineGraph.Vertex (V := StateAt (Pair C) r) C ≃ Fin n) : P5Graph.Graph := by
  letI : DecidableEq (StateAt (Pair C) r) := stateAtDecidableEq (Pair C) r
  exact P5MachineGraph.graphWith C code (iterate (step C) r)

theorem windowGraphWith_realizes (C r : ℕ) {n : ℕ}
    (code : P5MachineGraph.Vertex (V := StateAt (Pair C) r) C ≃ Fin n)
    {x : ℝ} (hx : Irrational x)
    (h : ∀ k : ℕ, k ≤ 2 * (r + 1) → EventualBound ((2 : ℝ) ^ k * x) C) :
    (encodedWindowGraph C r code).Realizes
      ((2 : ℝ) ^ (r + 1) * x) := by
  letI : DecidableEq (StateAt (Pair C) r) := stateAtDecidableEq (Pair C) r
  obtain ⟨y,z,_,_,⟨t⟩⟩ := coverage_iterate C r hx h
  exact P5MachineGraph.graphWith_realizes_of_trace C code (iterate (step C) r)
    t.input t.state t.left t.right t.trace t.start t.start_pos
    (fun j => by simpa only [digitValue, Nat.cast_add, Nat.cast_one] using (t.input_digits j).symm)

/-- A supplied executable numbering of the finite state space yields the
same endpoint, allowing the finite check to be exported to an evaluator. -/
theorem problem5_of_finite_encoded_check {n : ℕ}
    (code : P5MachineGraph.Vertex (V := StateAt (Pair 10) 14) 10 ≃ Fin n)
    (hfinite : (encodedWindowGraph 10 14 code).checkEventuallyDeterministic = true) :
    Problem5Statement := by
  letI : DecidableEq (StateAt (Pair 10) 14) := stateAtDecidableEq (Pair 10) 14
  apply P5Graph.problem5_of_rank_graph
    (P5MachineGraph.graphWith 10 code (iterate (step 10) 14)) hfinite
    (P5MachineGraph.graphWith_checkLabels 10 code (iterate (step 10) 14))
  intro x hx h
  exact windowGraphWith_realizes 10 14 code hx h

end VV.P5Window
