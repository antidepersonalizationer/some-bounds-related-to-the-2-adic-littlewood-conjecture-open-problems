import VV.P5GeneralWindow

/-!
The sole admitted obligation is a completely specified finite Boolean
graph check, as requested to avoid a large computation. It has NOT been
run. It concerns the reconstructed raw synchronized machine, not a replay
of the unavailable 2603-vertex attachment. In particular, compiling this
file does not independently validate that computational assertion.

The graph uses noncomputable finite-state numbering, and the Boolean check
expresses existence of a rank over the entire raw state space. It is not
a directly runnable, efficient verification program. Supplying a concrete
numbering and a checked certificate remains necessary for computation.

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

theorem window_classification : Problem5Real.WindowClassification :=
  P5GeneralWindow.classification_of_window_check 10 14 rank_check_10_14

/-- The bound 11, specializing the arbitrary-window reduction at C=10
and r=14, with precisely the one admitted finite check above. -/
theorem problem5_bound_eleven : Problem5Statement :=
  P5GeneralWindow.frequently_large_of_window_check 10 14 rank_check_10_14

theorem problem5_limsup :
    ∀ x : ℝ, Irrational x → ∃ k : ℕ, (11 : ℕ∞) ≤ B ((2 : ℝ)^k*x) :=
  problem5_limsup_iff.mp problem5_bound_eleven

theorem eventual_every_31 (x : ℝ) (hx : Irrational x) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ k : ℕ, k ≤ 30 ∧
      DigitsFrequentlyAtLeast ((2 : ℝ)^(j+k)*x) 11 :=
  P5GeneralWindow.eventual_every_window_of_check 10 14 rank_check_10_14 x hx

end VV.P5FiniteCheck
