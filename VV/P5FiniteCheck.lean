import VV.P5Window

/-!
The sole admitted obligation is a completely specified finite Boolean
graph check, as requested to avoid a large computation. It has NOT been
run. It concerns the reconstructed raw synchronized machine, not a replay
of the unavailable 2603-vertex attachment. In particular, compiling this
file does not independently validate that computational assertion.

All real-CF coverage, synchronization, infinite-path, period, quadratic,
and discriminant arguments are proved in the imported modules.
-/

namespace VV.P5FiniteCheck

/-- FINITE COMPUTATION NOT EXECUTED: the depth-14 machine over digits
1,...,10 has a finite rank certificate. The assertion quantifies only
over functions between explicitly finite vertex sets. -/
theorem rank_check_10_14 :
    (P5Window.windowGraph 10 14).checkEventuallyDeterministic = true := by
  sorry

theorem window_classification : Problem5Real.WindowClassification := by
  letI : DecidableEq (P5Synchronize.StateAt (P5Machine.Pair 10) 14) :=
    P5Window.stateAtDecidableEq (P5Machine.Pair 10) 14
  obtain ⟨rank,hcert⟩ := of_decide_eq_true rank_check_10_14
  apply P5Period.windowClassification_of_bounded_period (P5Window.windowGraph 10 14).size
  intro x hx h
  apply P5Graph.Graph.boundedPeriod_of_rank_realizes (P5Window.windowGraph 10 14) 10 rank hcert
  · exact P5MachineGraph.graph_label_bound 10 (P5Synchronize.iterate (P5Machine.step 10) 14)
  · exact P5Window.windowGraph_realizes 10 14 hx h

/-- The bound 11, with precisely the one admitted finite check above. -/
theorem problem5_bound_eleven : Problem5Statement :=
  P5Window.problem5_of_finite_window_check rank_check_10_14

theorem problem5_limsup :
    ∀ x : ℝ, Irrational x → ∃ k : ℕ, (11 : ℕ∞) ≤ B ((2 : ℝ)^k*x) :=
  Problem5Real.problem5_limsup_of_window_classification window_classification

theorem eventual_every_31 (x : ℝ) (hx : Irrational x) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ k : ℕ, k ≤ 30 ∧
      DigitsFrequentlyAtLeast ((2 : ℝ)^(j+k)*x) 11 :=
  Problem5Real.eventual_every_31_real_layers window_classification x hx

end VV.P5FiniteCheck
