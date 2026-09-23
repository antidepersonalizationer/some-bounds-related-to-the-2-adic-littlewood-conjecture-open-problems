import VV.Semantics
import Mathlib.Algebra.ContinuedFractions.Computation.Basic

namespace VV

/-- On irrational inputs our recurrence agrees term by term with mathlib's
standard continued-fraction computation. This rules out an abstract digit
function being silently substituted for the actual continued fraction. -/
theorem mathlib_stream_eq {x : ℝ} (hx : Irrational x) (n : ℕ) :
    GenContFract.IntFractPair.stream x n =
      some (GenContFract.IntFractPair.of (completeQuotient x n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [GenContFract.IntFractPair.stream, ih, Option.some_bind,
      GenContFract.IntFractPair.of]
    rw [if_neg (completeQuotient_fract_ne_zero hx n)]
    rfl

end VV
