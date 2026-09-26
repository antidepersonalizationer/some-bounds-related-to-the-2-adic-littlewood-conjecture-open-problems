import VV.P4PeriodThree
import VV.P4PeriodFour

/-!
# Symbolic tools for the exact period-four classification

State closure gives three parity patterns. The case modules separate each
positive digit into 1, 2, odd at least 3, or even at least 4. Thus only 48
symbolic type patterns remain. The digits themselves are unrestricted
integers: this is not a search with a numerical digit cutoff.
-/
noncomputable section
namespace VV.Problem4
open Hurwitz P5RealCursor

theorem digits_four {x : ℝ} {a b c d : ℤ} (hx : CycleModel x [a,b,c,d])
    (hw : ∀e∈[a,b,c,d],1≤e) :
    partialQuotient x 0=a ∧ partialQuotient x 1=b ∧ partialQuotient x 2=c ∧
      partialQuotient x 3=d ∧ partialQuotient x 4=a ∧ partialQuotient x 5=b ∧
      partialQuotient x 6=c := by
  have hd := hx.digitBlock hw
  simp only [List.length_cons,List.length_nil,P5Period.digitBlock,
    List.cons.injEq,true_and,and_true] at hd
  have hp : DigitPeriod x 4 := hx.digitPeriod hw
  exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,(hp 0).trans hd.1,
    (hp 1).trans hd.2.1,(hp 2).trans hd.2.2.1⟩

theorem same_four_cycle {x y : ℝ} {a b c d : ℤ} {v : List ℤ}
    (hx : CycleModel x [a,b,c,d]) (hy : CycleModel y v)
    (hw : ∀e∈[a,b,c,d],1≤e) (hv : ∀e∈v,1≤e)
    (hp : ExactEventualPeriod x 4) (hxy : TailEquivalent x y)
    (htr : trace (word v)=trace (word [a,b,c,d])) :
    v=[a,b,c,d] ∨ v=[b,c,d,a] ∨ v=[c,d,a,b] ∨ v=[d,a,b,c] := by
  have hl := equal_length_of_cycle_trace hx hy hw hv hp (by norm_num) hxy htr
  obtain ⟨k,hk,he⟩ := cycle_block_alignment hx hy hw hv hl (by norm_num) hxy
  rw [he]
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := digits_four hx hw
  have hk4 : k<4 := hk
  interval_cases k <;> simp [P5Period.digitBlock,h0,h1,h2,h3,h4,h5,h6]

theorem parity_four {x : ℝ} {a b c d : ℤ} (hx : CycleModel x [a,b,c,d])
    (hc : HasTripleRepresentative x) :
    (a%2=0 ∧ b%2=0 ∧ c%2=0 ∧ d%2=0) ∨
      (a%2=1 ∧ b%2=0 ∧ c%2=1 ∧ d%2=0) ∨
      (a%2=0 ∧ b%2=1 ∧ c%2=0 ∧ d%2=1) := by
  have hD := hx.all_states_closed hc State.D
  have hH := hx.all_states_closed hc State.H0
  have ha : a%2=0 ∨ a%2=1 := by omega
  have hb : b%2=0 ∨ b%2=1 := by omega
  have he : c%2=0 ∨ c%2=1 := by omega
  have hd : d%2=0 ∨ d%2=1 := by omega
  rcases ha with ha|ha <;> rcases hb with hb|hb <;>
    rcases he with he|he <;> rcases hd with hd|hd <;>
    simp [run,next,ha,hb,he,hd] at hD hH <;> omega



end VV.Problem4

