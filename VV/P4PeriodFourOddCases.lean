import VV.P4PeriodFourHelpers

/-! Sixteen symbolic digit-type cases; all arithmetic variables remain unbounded. -/

noncomputable section
namespace VV.Problem4.PeriodFourCases
open Hurwitz P5RealCursor

theorem case_0101 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : a=1)
    (hb : b=2)
    (hc : c=1)
    (hd : d=2)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  subst a
  subst b
  subst c
  subst d
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2,1,2,1] : List ℤ)=[1,2,1,2] ∨ ([2,1,2,1] : List ℤ)=[2,1,2,1] ∨ ([2,1,2,1] : List ℤ)=[1,2,1,2] ∨ ([2,1,2,1] : List ℤ)=[2,1,2,1] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2,1,2,1] := by simpa [run,next,emit] using raw
    have t0 : trace (word [2,1,2,1])=trace (word [1,2,1,2]) := by simpa [run,next,emit] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      False := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [0,1,1,0,1,1,0,4] := by simpa [run,next,emit] using raw
    have t0 : trace (word [0,1,1,0,1,1,0,4])=trace (word [1,2,1,2]) := by simpa [run,next,emit] using tr
    have m1 : CycleModel (value [4] (stateValue .H0 x)) [4,0,1,1,0,1,1,0] :=
      (show CycleModel (stateValue .H0 x) ([0,1,1,0,1,1,0]++[4]) from m0).rotate
    have t1 : trace (word [4,0,1,1,0,1,1,0])=trace (word [1,2,1,2]) :=
      (trace_word_rotate [0,1,1,0,1,1,0] [4]).symm.trans t0
    have ht1 : TailEquivalent x (value [4] (stateValue .H0 x)) := hs.trans (value_tailEquivalent [4] m0.irrational)
    have m2 : CycleModel (value [4] (stateValue .H0 x)) [(4+1),1,0,1,1,0] :=
      (show CycleModel (value [4] (stateValue .H0 x)) ([]++[4,0,1]++[1,0,1,1,0]) from m1).clean
    have t2 : trace (word [(4+1),1,0,1,1,0])=trace (word [1,2,1,2]) :=
      (congrArg trace (zero_cleanup_context [] [1,0,1,1,0] 4 1)).symm.trans t1
    have m3 : CycleModel (value [4] (stateValue .H0 x)) [(4+1),(1+1),1,0] :=
      (show CycleModel (value [4] (stateValue .H0 x)) ([(4+1)]++[1,0,1]++[1,0]) from m2).clean
    have t3 : trace (word [(4+1),(1+1),1,0])=trace (word [1,2,1,2]) :=
      (congrArg trace (zero_cleanup_context [(4+1)] [1,0] 1 1)).symm.trans t2
    have m4 : CycleModel (value [1,0] (value [4] (stateValue .H0 x))) [1,0,(4+1),(1+1)] :=
      (show CycleModel (value [4] (stateValue .H0 x)) ([(4+1),(1+1)]++[1,0]) from m3).rotate
    have t4 : trace (word [1,0,(4+1),(1+1)])=trace (word [1,2,1,2]) :=
      (trace_word_rotate [(4+1),(1+1)] [1,0]).symm.trans t3
    have ht4 : TailEquivalent x (value [1,0] (value [4] (stateValue .H0 x))) := ht1.trans (value_tailEquivalent [1,0] m3.irrational)
    have m5 : CycleModel (value [1,0] (value [4] (stateValue .H0 x))) [(1+(4+1)),(1+1)] :=
      (show CycleModel (value [1,0] (value [4] (stateValue .H0 x))) ([]++[1,0,(4+1)]++[(1+1)]) from m4).clean
    have t5 : trace (word [(1+(4+1)),(1+1)])=trace (word [1,2,1,2]) :=
      (congrArg trace (zero_cleanup_context [] [(1+1)] 1 (4+1))).symm.trans t4
    have hh := same_four_cycle hx m5 hw (by simp <;> omega) hp ht4 t5
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      False := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [0,4,0,1,1,0,1,1] := by simpa [run,next,emit] using raw
    have t0 : trace (word [0,4,0,1,1,0,1,1])=trace (word [1,2,1,2]) := by simpa [run,next,emit] using tr
    have m1 : CycleModel (value [1] (stateValue .H1 x)) [1,0,4,0,1,1,0,1] :=
      (show CycleModel (stateValue .H1 x) ([0,4,0,1,1,0,1]++[1]) from m0).rotate
    have t1 : trace (word [1,0,4,0,1,1,0,1])=trace (word [1,2,1,2]) :=
      (trace_word_rotate [0,4,0,1,1,0,1] [1]).symm.trans t0
    have ht1 : TailEquivalent x (value [1] (stateValue .H1 x)) := hs.trans (value_tailEquivalent [1] m0.irrational)
    have m2 : CycleModel (value [1] (stateValue .H1 x)) [(1+4),0,1,1,0,1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[1,0,4]++[0,1,1,0,1]) from m1).clean
    have t2 : trace (word [(1+4),0,1,1,0,1])=trace (word [1,2,1,2]) :=
      (congrArg trace (zero_cleanup_context [] [0,1,1,0,1] 1 4)).symm.trans t1
    have m3 : CycleModel (value [1] (stateValue .H1 x)) [((1+4)+1),1,0,1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[(1+4),0,1]++[1,0,1]) from m2).clean
    have t3 : trace (word [((1+4)+1),1,0,1])=trace (word [1,2,1,2]) :=
      (congrArg trace (zero_cleanup_context [] [1,0,1] (1+4) 1)).symm.trans t2
    have m4 : CycleModel (value [1] (stateValue .H1 x)) [((1+4)+1),(1+1)] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([((1+4)+1)]++[1,0,1]++[]) from m3).clean
    have t4 : trace (word [((1+4)+1),(1+1)])=trace (word [1,2,1,2]) :=
      (congrArg trace (zero_cleanup_context [((1+4)+1)] [] 1 1)).symm.trans t3
    have hh := same_four_cycle hx m4 hw (by simp <;> omega) hp ht1 t4
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_2101 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : 3≤a ∧ a%2=1)
    (hb : b=2)
    (hc : c=1)
    (hd : d=2)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  obtain ⟨ha,hpa⟩ := ha
  subst b
  subst c
  subst d
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2*a,1,2,1] : List ℤ)=[a,2,1,2] ∨ ([2*a,1,2,1] : List ℤ)=[2,1,2,a] ∨ ([2*a,1,2,1] : List ℤ)=[1,2,a,2] ∨ ([2*a,1,2,1] : List ℤ)=[2,a,2,1] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2*a,1,2,1] := by simpa [run,next,emit,hpa] using raw
    have t0 : trace (word [2*a,1,2,1])=trace (word [a,2,1,2]) := by simpa [run,next,emit,hpa] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      ([a/2,1,(1+1),(1+4)] : List ℤ)=[a,2,1,2] ∨ ([a/2,1,(1+1),(1+4)] : List ℤ)=[2,1,2,a] ∨ ([a/2,1,(1+1),(1+4)] : List ℤ)=[1,2,a,2] ∨ ([a/2,1,(1+1),(1+4)] : List ℤ)=[2,a,2,1] := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [a/2,1,1,0,1,1,0,4] := by simpa [run,next,emit,hpa] using raw
    have t0 : trace (word [a/2,1,1,0,1,1,0,4])=trace (word [a,2,1,2]) := by simpa [run,next,emit,hpa] using tr
    have m1 : CycleModel (stateValue .H0 x) [a/2,1,(1+1),1,0,4] :=
      (show CycleModel (stateValue .H0 x) ([a/2,1]++[1,0,1]++[1,0,4]) from m0).clean
    have t1 : trace (word [a/2,1,(1+1),1,0,4])=trace (word [a,2,1,2]) :=
      (congrArg trace (zero_cleanup_context [a/2,1] [1,0,4] 1 1)).symm.trans t0
    have m2 : CycleModel (stateValue .H0 x) [a/2,1,(1+1),(1+4)] :=
      (show CycleModel (stateValue .H0 x) ([a/2,1,(1+1)]++[1,0,4]++[]) from m1).clean
    have t2 : trace (word [a/2,1,(1+1),(1+4)])=trace (word [a,2,1,2]) :=
      (congrArg trace (zero_cleanup_context [a/2,1,(1+1)] [] 1 4)).symm.trans t1
    have hh := same_four_cycle hx m2 hw (by simp <;> omega) hp hs t2
    exact hh
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      ([a/2,(4+1),(1+1),1] : List ℤ)=[a,2,1,2] ∨ ([a/2,(4+1),(1+1),1] : List ℤ)=[2,1,2,a] ∨ ([a/2,(4+1),(1+1),1] : List ℤ)=[1,2,a,2] ∨ ([a/2,(4+1),(1+1),1] : List ℤ)=[2,a,2,1] := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [a/2,4,0,1,1,0,1,1] := by simpa [run,next,emit,hpa] using raw
    have t0 : trace (word [a/2,4,0,1,1,0,1,1])=trace (word [a,2,1,2]) := by simpa [run,next,emit,hpa] using tr
    have m1 : CycleModel (stateValue .H1 x) [a/2,(4+1),1,0,1,1] :=
      (show CycleModel (stateValue .H1 x) ([a/2]++[4,0,1]++[1,0,1,1]) from m0).clean
    have t1 : trace (word [a/2,(4+1),1,0,1,1])=trace (word [a,2,1,2]) :=
      (congrArg trace (zero_cleanup_context [a/2] [1,0,1,1] 4 1)).symm.trans t0
    have m2 : CycleModel (stateValue .H1 x) [a/2,(4+1),(1+1),1] :=
      (show CycleModel (stateValue .H1 x) ([a/2,(4+1)]++[1,0,1]++[1]) from m1).clean
    have t2 : trace (word [a/2,(4+1),(1+1),1])=trace (word [a,2,1,2]) :=
      (congrArg trace (zero_cleanup_context [a/2,(4+1)] [1] 1 1)).symm.trans t1
    have hh := same_four_cycle hx m2 hw (by simp <;> omega) hp hs t2
    exact hh
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_0301 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : a=1)
    (hb : 4≤b ∧ b%2=0)
    (hc : c=1)
    (hd : d=2)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  subst a
  obtain ⟨hb,hpb⟩ := hb
  subst c
  subst d
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2,b/2,2,1] : List ℤ)=[1,b,1,2] ∨ ([2,b/2,2,1] : List ℤ)=[b,1,2,1] ∨ ([2,b/2,2,1] : List ℤ)=[1,2,1,b] ∨ ([2,b/2,2,1] : List ℤ)=[2,1,b,1] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2,b/2,2,1] := by simpa [run,next,emit,hpb] using raw
    have t0 : trace (word [2,b/2,2,1])=trace (word [1,b,1,2]) := by simpa [run,next,emit,hpb] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      ([(1+(4+1)),1,(b/2-1),1] : List ℤ)=[1,b,1,2] ∨ ([(1+(4+1)),1,(b/2-1),1] : List ℤ)=[b,1,2,1] ∨ ([(1+(4+1)),1,(b/2-1),1] : List ℤ)=[1,2,1,b] ∨ ([(1+(4+1)),1,(b/2-1),1] : List ℤ)=[2,1,b,1] := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [0,1,1,(b/2-1),1,1,0,4] := by simpa [run,next,emit,hpb] using raw
    have t0 : trace (word [0,1,1,(b/2-1),1,1,0,4])=trace (word [1,b,1,2]) := by simpa [run,next,emit,hpb] using tr
    have m1 : CycleModel (value [4] (stateValue .H0 x)) [4,0,1,1,(b/2-1),1,1,0] :=
      (show CycleModel (stateValue .H0 x) ([0,1,1,(b/2-1),1,1,0]++[4]) from m0).rotate
    have t1 : trace (word [4,0,1,1,(b/2-1),1,1,0])=trace (word [1,b,1,2]) :=
      (trace_word_rotate [0,1,1,(b/2-1),1,1,0] [4]).symm.trans t0
    have ht1 : TailEquivalent x (value [4] (stateValue .H0 x)) := hs.trans (value_tailEquivalent [4] m0.irrational)
    have m2 : CycleModel (value [4] (stateValue .H0 x)) [(4+1),1,(b/2-1),1,1,0] :=
      (show CycleModel (value [4] (stateValue .H0 x)) ([]++[4,0,1]++[1,(b/2-1),1,1,0]) from m1).clean
    have t2 : trace (word [(4+1),1,(b/2-1),1,1,0])=trace (word [1,b,1,2]) :=
      (congrArg trace (zero_cleanup_context [] [1,(b/2-1),1,1,0] 4 1)).symm.trans t1
    have m3 : CycleModel (value [1,0] (value [4] (stateValue .H0 x))) [1,0,(4+1),1,(b/2-1),1] :=
      (show CycleModel (value [4] (stateValue .H0 x)) ([(4+1),1,(b/2-1),1]++[1,0]) from m2).rotate
    have t3 : trace (word [1,0,(4+1),1,(b/2-1),1])=trace (word [1,b,1,2]) :=
      (trace_word_rotate [(4+1),1,(b/2-1),1] [1,0]).symm.trans t2
    have ht3 : TailEquivalent x (value [1,0] (value [4] (stateValue .H0 x))) := ht1.trans (value_tailEquivalent [1,0] m2.irrational)
    have m4 : CycleModel (value [1,0] (value [4] (stateValue .H0 x))) [(1+(4+1)),1,(b/2-1),1] :=
      (show CycleModel (value [1,0] (value [4] (stateValue .H0 x))) ([]++[1,0,(4+1)]++[1,(b/2-1),1]) from m3).clean
    have t4 : trace (word [(1+(4+1)),1,(b/2-1),1])=trace (word [1,b,1,2]) :=
      (congrArg trace (zero_cleanup_context [] [1,(b/2-1),1] 1 (4+1))).symm.trans t3
    have hh := same_four_cycle hx m4 hw (by simp <;> omega) hp ht3 t4
    exact hh
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      False := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [0,2*b,0,1,1,0,1,1] := by simpa [run,next,emit,hpb] using raw
    have t0 : trace (word [0,2*b,0,1,1,0,1,1])=trace (word [1,b,1,2]) := by simpa [run,next,emit,hpb] using tr
    have m1 : CycleModel (value [1] (stateValue .H1 x)) [1,0,2*b,0,1,1,0,1] :=
      (show CycleModel (stateValue .H1 x) ([0,2*b,0,1,1,0,1]++[1]) from m0).rotate
    have t1 : trace (word [1,0,2*b,0,1,1,0,1])=trace (word [1,b,1,2]) :=
      (trace_word_rotate [0,2*b,0,1,1,0,1] [1]).symm.trans t0
    have ht1 : TailEquivalent x (value [1] (stateValue .H1 x)) := hs.trans (value_tailEquivalent [1] m0.irrational)
    have m2 : CycleModel (value [1] (stateValue .H1 x)) [(1+2*b),0,1,1,0,1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[1,0,2*b]++[0,1,1,0,1]) from m1).clean
    have t2 : trace (word [(1+2*b),0,1,1,0,1])=trace (word [1,b,1,2]) :=
      (congrArg trace (zero_cleanup_context [] [0,1,1,0,1] 1 (2*b))).symm.trans t1
    have m3 : CycleModel (value [1] (stateValue .H1 x)) [((1+2*b)+1),1,0,1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[(1+2*b),0,1]++[1,0,1]) from m2).clean
    have t3 : trace (word [((1+2*b)+1),1,0,1])=trace (word [1,b,1,2]) :=
      (congrArg trace (zero_cleanup_context [] [1,0,1] ((1+2*b)) 1)).symm.trans t2
    have m4 : CycleModel (value [1] (stateValue .H1 x)) [((1+2*b)+1),(1+1)] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([((1+2*b)+1)]++[1,0,1]++[]) from m3).clean
    have t4 : trace (word [((1+2*b)+1),(1+1)])=trace (word [1,b,1,2]) :=
      (congrArg trace (zero_cleanup_context [((1+2*b)+1)] [] 1 1)).symm.trans t3
    have hh := same_four_cycle hx m4 hw (by simp <;> omega) hp ht1 t4
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_2301 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : 3≤a ∧ a%2=1)
    (hb : 4≤b ∧ b%2=0)
    (hc : c=1)
    (hd : d=2)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  obtain ⟨ha,hpa⟩ := ha
  obtain ⟨hb,hpb⟩ := hb
  subst c
  subst d
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2*a,b/2,2,1] : List ℤ)=[a,b,1,2] ∨ ([2*a,b/2,2,1] : List ℤ)=[b,1,2,a] ∨ ([2*a,b/2,2,1] : List ℤ)=[1,2,a,b] ∨ ([2*a,b/2,2,1] : List ℤ)=[2,a,b,1] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2*a,b/2,2,1] := by simpa [run,next,emit,hpa,hpb] using raw
    have t0 : trace (word [2*a,b/2,2,1])=trace (word [a,b,1,2]) := by simpa [run,next,emit,hpa,hpb] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      False := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [a/2,1,1,(b/2-1),1,1,0,4] := by simpa [run,next,emit,hpa,hpb] using raw
    have t0 : trace (word [a/2,1,1,(b/2-1),1,1,0,4])=trace (word [a,b,1,2]) := by simpa [run,next,emit,hpa,hpb] using tr
    have m1 : CycleModel (stateValue .H0 x) [a/2,1,1,(b/2-1),1,(1+4)] :=
      (show CycleModel (stateValue .H0 x) ([a/2,1,1,(b/2-1),1]++[1,0,4]++[]) from m0).clean
    have t1 : trace (word [a/2,1,1,(b/2-1),1,(1+4)])=trace (word [a,b,1,2]) :=
      (congrArg trace (zero_cleanup_context [a/2,1,1,(b/2-1),1] [] 1 4)).symm.trans t0
    have hh := same_four_cycle hx m1 hw (by simp <;> omega) hp hs t1
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      ([a/2,(2*b+1),(1+1),1] : List ℤ)=[a,b,1,2] ∨ ([a/2,(2*b+1),(1+1),1] : List ℤ)=[b,1,2,a] ∨ ([a/2,(2*b+1),(1+1),1] : List ℤ)=[1,2,a,b] ∨ ([a/2,(2*b+1),(1+1),1] : List ℤ)=[2,a,b,1] := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [a/2,2*b,0,1,1,0,1,1] := by simpa [run,next,emit,hpa,hpb] using raw
    have t0 : trace (word [a/2,2*b,0,1,1,0,1,1])=trace (word [a,b,1,2]) := by simpa [run,next,emit,hpa,hpb] using tr
    have m1 : CycleModel (stateValue .H1 x) [a/2,(2*b+1),1,0,1,1] :=
      (show CycleModel (stateValue .H1 x) ([a/2]++[2*b,0,1]++[1,0,1,1]) from m0).clean
    have t1 : trace (word [a/2,(2*b+1),1,0,1,1])=trace (word [a,b,1,2]) :=
      (congrArg trace (zero_cleanup_context [a/2] [1,0,1,1] (2*b) 1)).symm.trans t0
    have m2 : CycleModel (stateValue .H1 x) [a/2,(2*b+1),(1+1),1] :=
      (show CycleModel (stateValue .H1 x) ([a/2,(2*b+1)]++[1,0,1]++[1]) from m1).clean
    have t2 : trace (word [a/2,(2*b+1),(1+1),1])=trace (word [a,b,1,2]) :=
      (congrArg trace (zero_cleanup_context [a/2,(2*b+1)] [1] 1 1)).symm.trans t1
    have hh := same_four_cycle hx m2 hw (by simp <;> omega) hp hs t2
    exact hh
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_0121 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : a=1)
    (hb : b=2)
    (hc : 3≤c ∧ c%2=1)
    (hd : d=2)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  subst a
  subst b
  obtain ⟨hc,hpc⟩ := hc
  subst d
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2,1,2*c,1] : List ℤ)=[1,2,c,2] ∨ ([2,1,2*c,1] : List ℤ)=[2,c,2,1] ∨ ([2,1,2*c,1] : List ℤ)=[c,2,1,2] ∨ ([2,1,2*c,1] : List ℤ)=[2,1,2,c] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2,1,2*c,1] := by simpa [run,next,emit,hpc] using raw
    have t0 : trace (word [2,1,2*c,1])=trace (word [1,2,c,2]) := by simpa [run,next,emit,hpc] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      ([(4+1),(1+1),1,c/2] : List ℤ)=[1,2,c,2] ∨ ([(4+1),(1+1),1,c/2] : List ℤ)=[2,c,2,1] ∨ ([(4+1),(1+1),1,c/2] : List ℤ)=[c,2,1,2] ∨ ([(4+1),(1+1),1,c/2] : List ℤ)=[2,1,2,c] := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [0,1,1,0,1,1,c/2,4] := by simpa [run,next,emit,hpc] using raw
    have t0 : trace (word [0,1,1,0,1,1,c/2,4])=trace (word [1,2,c,2]) := by simpa [run,next,emit,hpc] using tr
    have m1 : CycleModel (value [4] (stateValue .H0 x)) [4,0,1,1,0,1,1,c/2] :=
      (show CycleModel (stateValue .H0 x) ([0,1,1,0,1,1,c/2]++[4]) from m0).rotate
    have t1 : trace (word [4,0,1,1,0,1,1,c/2])=trace (word [1,2,c,2]) :=
      (trace_word_rotate [0,1,1,0,1,1,c/2] [4]).symm.trans t0
    have ht1 : TailEquivalent x (value [4] (stateValue .H0 x)) := hs.trans (value_tailEquivalent [4] m0.irrational)
    have m2 : CycleModel (value [4] (stateValue .H0 x)) [(4+1),1,0,1,1,c/2] :=
      (show CycleModel (value [4] (stateValue .H0 x)) ([]++[4,0,1]++[1,0,1,1,c/2]) from m1).clean
    have t2 : trace (word [(4+1),1,0,1,1,c/2])=trace (word [1,2,c,2]) :=
      (congrArg trace (zero_cleanup_context [] [1,0,1,1,c/2] 4 1)).symm.trans t1
    have m3 : CycleModel (value [4] (stateValue .H0 x)) [(4+1),(1+1),1,c/2] :=
      (show CycleModel (value [4] (stateValue .H0 x)) ([(4+1)]++[1,0,1]++[1,c/2]) from m2).clean
    have t3 : trace (word [(4+1),(1+1),1,c/2])=trace (word [1,2,c,2]) :=
      (congrArg trace (zero_cleanup_context [(4+1)] [1,c/2] 1 1)).symm.trans t2
    have hh := same_four_cycle hx m3 hw (by simp <;> omega) hp ht1 t3
    exact hh
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      ([(1+4),c/2,1,(1+1)] : List ℤ)=[1,2,c,2] ∨ ([(1+4),c/2,1,(1+1)] : List ℤ)=[2,c,2,1] ∨ ([(1+4),c/2,1,(1+1)] : List ℤ)=[c,2,1,2] ∨ ([(1+4),c/2,1,(1+1)] : List ℤ)=[2,1,2,c] := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [0,4,c/2,1,1,0,1,1] := by simpa [run,next,emit,hpc] using raw
    have t0 : trace (word [0,4,c/2,1,1,0,1,1])=trace (word [1,2,c,2]) := by simpa [run,next,emit,hpc] using tr
    have m1 : CycleModel (value [1] (stateValue .H1 x)) [1,0,4,c/2,1,1,0,1] :=
      (show CycleModel (stateValue .H1 x) ([0,4,c/2,1,1,0,1]++[1]) from m0).rotate
    have t1 : trace (word [1,0,4,c/2,1,1,0,1])=trace (word [1,2,c,2]) :=
      (trace_word_rotate [0,4,c/2,1,1,0,1] [1]).symm.trans t0
    have ht1 : TailEquivalent x (value [1] (stateValue .H1 x)) := hs.trans (value_tailEquivalent [1] m0.irrational)
    have m2 : CycleModel (value [1] (stateValue .H1 x)) [(1+4),c/2,1,1,0,1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[1,0,4]++[c/2,1,1,0,1]) from m1).clean
    have t2 : trace (word [(1+4),c/2,1,1,0,1])=trace (word [1,2,c,2]) :=
      (congrArg trace (zero_cleanup_context [] [c/2,1,1,0,1] 1 4)).symm.trans t1
    have m3 : CycleModel (value [1] (stateValue .H1 x)) [(1+4),c/2,1,(1+1)] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([(1+4),c/2,1]++[1,0,1]++[]) from m2).clean
    have t3 : trace (word [(1+4),c/2,1,(1+1)])=trace (word [1,2,c,2]) :=
      (congrArg trace (zero_cleanup_context [(1+4),c/2,1] [] 1 1)).symm.trans t2
    have hh := same_four_cycle hx m3 hw (by simp <;> omega) hp ht1 t3
    exact hh
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_2121 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : 3≤a ∧ a%2=1)
    (hb : b=2)
    (hc : 3≤c ∧ c%2=1)
    (hd : d=2)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  obtain ⟨ha,hpa⟩ := ha
  subst b
  obtain ⟨hc,hpc⟩ := hc
  subst d
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2*a,1,2*c,1] : List ℤ)=[a,2,c,2] ∨ ([2*a,1,2*c,1] : List ℤ)=[2,c,2,a] ∨ ([2*a,1,2*c,1] : List ℤ)=[c,2,a,2] ∨ ([2*a,1,2*c,1] : List ℤ)=[2,a,2,c] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2*a,1,2*c,1] := by simpa [run,next,emit,hpa,hpc] using raw
    have t0 : trace (word [2*a,1,2*c,1])=trace (word [a,2,c,2]) := by simpa [run,next,emit,hpa,hpc] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      False := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [a/2,1,1,0,1,1,c/2,4] := by simpa [run,next,emit,hpa,hpc] using raw
    have t0 : trace (word [a/2,1,1,0,1,1,c/2,4])=trace (word [a,2,c,2]) := by simpa [run,next,emit,hpa,hpc] using tr
    have m1 : CycleModel (stateValue .H0 x) [a/2,1,(1+1),1,c/2,4] :=
      (show CycleModel (stateValue .H0 x) ([a/2,1]++[1,0,1]++[1,c/2,4]) from m0).clean
    have t1 : trace (word [a/2,1,(1+1),1,c/2,4])=trace (word [a,2,c,2]) :=
      (congrArg trace (zero_cleanup_context [a/2,1] [1,c/2,4] 1 1)).symm.trans t0
    have hh := same_four_cycle hx m1 hw (by simp <;> omega) hp hs t1
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      False := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [a/2,4,c/2,1,1,0,1,1] := by simpa [run,next,emit,hpa,hpc] using raw
    have t0 : trace (word [a/2,4,c/2,1,1,0,1,1])=trace (word [a,2,c,2]) := by simpa [run,next,emit,hpa,hpc] using tr
    have m1 : CycleModel (stateValue .H1 x) [a/2,4,c/2,1,(1+1),1] :=
      (show CycleModel (stateValue .H1 x) ([a/2,4,c/2,1]++[1,0,1]++[1]) from m0).clean
    have t1 : trace (word [a/2,4,c/2,1,(1+1),1])=trace (word [a,2,c,2]) :=
      (congrArg trace (zero_cleanup_context [a/2,4,c/2,1] [1] 1 1)).symm.trans t0
    have hh := same_four_cycle hx m1 hw (by simp <;> omega) hp hs t1
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_0321 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : a=1)
    (hb : 4≤b ∧ b%2=0)
    (hc : 3≤c ∧ c%2=1)
    (hd : d=2)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  subst a
  obtain ⟨hb,hpb⟩ := hb
  obtain ⟨hc,hpc⟩ := hc
  subst d
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2,b/2,2*c,1] : List ℤ)=[1,b,c,2] ∨ ([2,b/2,2*c,1] : List ℤ)=[b,c,2,1] ∨ ([2,b/2,2*c,1] : List ℤ)=[c,2,1,b] ∨ ([2,b/2,2*c,1] : List ℤ)=[2,1,b,c] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2,b/2,2*c,1] := by simpa [run,next,emit,hpb,hpc] using raw
    have t0 : trace (word [2,b/2,2*c,1])=trace (word [1,b,c,2]) := by simpa [run,next,emit,hpb,hpc] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      False := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [0,1,1,(b/2-1),1,1,c/2,4] := by simpa [run,next,emit,hpb,hpc] using raw
    have t0 : trace (word [0,1,1,(b/2-1),1,1,c/2,4])=trace (word [1,b,c,2]) := by simpa [run,next,emit,hpb,hpc] using tr
    have m1 : CycleModel (value [4] (stateValue .H0 x)) [4,0,1,1,(b/2-1),1,1,c/2] :=
      (show CycleModel (stateValue .H0 x) ([0,1,1,(b/2-1),1,1,c/2]++[4]) from m0).rotate
    have t1 : trace (word [4,0,1,1,(b/2-1),1,1,c/2])=trace (word [1,b,c,2]) :=
      (trace_word_rotate [0,1,1,(b/2-1),1,1,c/2] [4]).symm.trans t0
    have ht1 : TailEquivalent x (value [4] (stateValue .H0 x)) := hs.trans (value_tailEquivalent [4] m0.irrational)
    have m2 : CycleModel (value [4] (stateValue .H0 x)) [(4+1),1,(b/2-1),1,1,c/2] :=
      (show CycleModel (value [4] (stateValue .H0 x)) ([]++[4,0,1]++[1,(b/2-1),1,1,c/2]) from m1).clean
    have t2 : trace (word [(4+1),1,(b/2-1),1,1,c/2])=trace (word [1,b,c,2]) :=
      (congrArg trace (zero_cleanup_context [] [1,(b/2-1),1,1,c/2] 4 1)).symm.trans t1
    have hh := same_four_cycle hx m2 hw (by simp <;> omega) hp ht1 t2
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      ([(1+2*b),c/2,1,(1+1)] : List ℤ)=[1,b,c,2] ∨ ([(1+2*b),c/2,1,(1+1)] : List ℤ)=[b,c,2,1] ∨ ([(1+2*b),c/2,1,(1+1)] : List ℤ)=[c,2,1,b] ∨ ([(1+2*b),c/2,1,(1+1)] : List ℤ)=[2,1,b,c] := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [0,2*b,c/2,1,1,0,1,1] := by simpa [run,next,emit,hpb,hpc] using raw
    have t0 : trace (word [0,2*b,c/2,1,1,0,1,1])=trace (word [1,b,c,2]) := by simpa [run,next,emit,hpb,hpc] using tr
    have m1 : CycleModel (value [1] (stateValue .H1 x)) [1,0,2*b,c/2,1,1,0,1] :=
      (show CycleModel (stateValue .H1 x) ([0,2*b,c/2,1,1,0,1]++[1]) from m0).rotate
    have t1 : trace (word [1,0,2*b,c/2,1,1,0,1])=trace (word [1,b,c,2]) :=
      (trace_word_rotate [0,2*b,c/2,1,1,0,1] [1]).symm.trans t0
    have ht1 : TailEquivalent x (value [1] (stateValue .H1 x)) := hs.trans (value_tailEquivalent [1] m0.irrational)
    have m2 : CycleModel (value [1] (stateValue .H1 x)) [(1+2*b),c/2,1,1,0,1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[1,0,2*b]++[c/2,1,1,0,1]) from m1).clean
    have t2 : trace (word [(1+2*b),c/2,1,1,0,1])=trace (word [1,b,c,2]) :=
      (congrArg trace (zero_cleanup_context [] [c/2,1,1,0,1] 1 (2*b))).symm.trans t1
    have m3 : CycleModel (value [1] (stateValue .H1 x)) [(1+2*b),c/2,1,(1+1)] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([(1+2*b),c/2,1]++[1,0,1]++[]) from m2).clean
    have t3 : trace (word [(1+2*b),c/2,1,(1+1)])=trace (word [1,b,c,2]) :=
      (congrArg trace (zero_cleanup_context [(1+2*b),c/2,1] [] 1 1)).symm.trans t2
    have hh := same_four_cycle hx m3 hw (by simp <;> omega) hp ht1 t3
    exact hh
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_2321 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : 3≤a ∧ a%2=1)
    (hb : 4≤b ∧ b%2=0)
    (hc : 3≤c ∧ c%2=1)
    (hd : d=2)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  obtain ⟨ha,hpa⟩ := ha
  obtain ⟨hb,hpb⟩ := hb
  obtain ⟨hc,hpc⟩ := hc
  subst d
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2*a,b/2,2*c,1] : List ℤ)=[a,b,c,2] ∨ ([2*a,b/2,2*c,1] : List ℤ)=[b,c,2,a] ∨ ([2*a,b/2,2*c,1] : List ℤ)=[c,2,a,b] ∨ ([2*a,b/2,2*c,1] : List ℤ)=[2,a,b,c] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2*a,b/2,2*c,1] := by simpa [run,next,emit,hpa,hpb,hpc] using raw
    have t0 : trace (word [2*a,b/2,2*c,1])=trace (word [a,b,c,2]) := by simpa [run,next,emit,hpa,hpb,hpc] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      False := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [a/2,1,1,(b/2-1),1,1,c/2,4] := by simpa [run,next,emit,hpa,hpb,hpc] using raw
    have t0 : trace (word [a/2,1,1,(b/2-1),1,1,c/2,4])=trace (word [a,b,c,2]) := by simpa [run,next,emit,hpa,hpb,hpc] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      False := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [a/2,2*b,c/2,1,1,0,1,1] := by simpa [run,next,emit,hpa,hpb,hpc] using raw
    have t0 : trace (word [a/2,2*b,c/2,1,1,0,1,1])=trace (word [a,b,c,2]) := by simpa [run,next,emit,hpa,hpb,hpc] using tr
    have m1 : CycleModel (stateValue .H1 x) [a/2,2*b,c/2,1,(1+1),1] :=
      (show CycleModel (stateValue .H1 x) ([a/2,2*b,c/2,1]++[1,0,1]++[1]) from m0).clean
    have t1 : trace (word [a/2,2*b,c/2,1,(1+1),1])=trace (word [a,b,c,2]) :=
      (congrArg trace (zero_cleanup_context [a/2,2*b,c/2,1] [1] 1 1)).symm.trans t0
    have hh := same_four_cycle hx m1 hw (by simp <;> omega) hp hs t1
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_0103 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : a=1)
    (hb : b=2)
    (hc : c=1)
    (hd : 4≤d ∧ d%2=0)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  subst a
  subst b
  subst c
  obtain ⟨hd,hpd⟩ := hd
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2,1,2,d/2] : List ℤ)=[1,2,1,d] ∨ ([2,1,2,d/2] : List ℤ)=[2,1,d,1] ∨ ([2,1,2,d/2] : List ℤ)=[1,d,1,2] ∨ ([2,1,2,d/2] : List ℤ)=[d,1,2,1] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2,1,2,d/2] := by simpa [run,next,emit,hpd] using raw
    have t0 : trace (word [2,1,2,d/2])=trace (word [1,2,1,d]) := by simpa [run,next,emit,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      False := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [0,1,1,0,1,1,0,2*d] := by simpa [run,next,emit,hpd] using raw
    have t0 : trace (word [0,1,1,0,1,1,0,2*d])=trace (word [1,2,1,d]) := by simpa [run,next,emit,hpd] using tr
    have m1 : CycleModel (value [2*d] (stateValue .H0 x)) [2*d,0,1,1,0,1,1,0] :=
      (show CycleModel (stateValue .H0 x) ([0,1,1,0,1,1,0]++[2*d]) from m0).rotate
    have t1 : trace (word [2*d,0,1,1,0,1,1,0])=trace (word [1,2,1,d]) :=
      (trace_word_rotate [0,1,1,0,1,1,0] [2*d]).symm.trans t0
    have ht1 : TailEquivalent x (value [2*d] (stateValue .H0 x)) := hs.trans (value_tailEquivalent [2*d] m0.irrational)
    have m2 : CycleModel (value [2*d] (stateValue .H0 x)) [(2*d+1),1,0,1,1,0] :=
      (show CycleModel (value [2*d] (stateValue .H0 x)) ([]++[2*d,0,1]++[1,0,1,1,0]) from m1).clean
    have t2 : trace (word [(2*d+1),1,0,1,1,0])=trace (word [1,2,1,d]) :=
      (congrArg trace (zero_cleanup_context [] [1,0,1,1,0] (2*d) 1)).symm.trans t1
    have m3 : CycleModel (value [2*d] (stateValue .H0 x)) [(2*d+1),(1+1),1,0] :=
      (show CycleModel (value [2*d] (stateValue .H0 x)) ([(2*d+1)]++[1,0,1]++[1,0]) from m2).clean
    have t3 : trace (word [(2*d+1),(1+1),1,0])=trace (word [1,2,1,d]) :=
      (congrArg trace (zero_cleanup_context [(2*d+1)] [1,0] 1 1)).symm.trans t2
    have m4 : CycleModel (value [1,0] (value [2*d] (stateValue .H0 x))) [1,0,(2*d+1),(1+1)] :=
      (show CycleModel (value [2*d] (stateValue .H0 x)) ([(2*d+1),(1+1)]++[1,0]) from m3).rotate
    have t4 : trace (word [1,0,(2*d+1),(1+1)])=trace (word [1,2,1,d]) :=
      (trace_word_rotate [(2*d+1),(1+1)] [1,0]).symm.trans t3
    have ht4 : TailEquivalent x (value [1,0] (value [2*d] (stateValue .H0 x))) := ht1.trans (value_tailEquivalent [1,0] m3.irrational)
    have m5 : CycleModel (value [1,0] (value [2*d] (stateValue .H0 x))) [(1+(2*d+1)),(1+1)] :=
      (show CycleModel (value [1,0] (value [2*d] (stateValue .H0 x))) ([]++[1,0,(2*d+1)]++[(1+1)]) from m4).clean
    have t5 : trace (word [(1+(2*d+1)),(1+1)])=trace (word [1,2,1,d]) :=
      (congrArg trace (zero_cleanup_context [] [(1+1)] 1 ((2*d+1)))).symm.trans t4
    have hh := same_four_cycle hx m5 hw (by simp <;> omega) hp ht4 t5
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      ([((1+4)+1),1,(d/2-1),1] : List ℤ)=[1,2,1,d] ∨ ([((1+4)+1),1,(d/2-1),1] : List ℤ)=[2,1,d,1] ∨ ([((1+4)+1),1,(d/2-1),1] : List ℤ)=[1,d,1,2] ∨ ([((1+4)+1),1,(d/2-1),1] : List ℤ)=[d,1,2,1] := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [0,4,0,1,1,(d/2-1),1,1] := by simpa [run,next,emit,hpd] using raw
    have t0 : trace (word [0,4,0,1,1,(d/2-1),1,1])=trace (word [1,2,1,d]) := by simpa [run,next,emit,hpd] using tr
    have m1 : CycleModel (value [1] (stateValue .H1 x)) [1,0,4,0,1,1,(d/2-1),1] :=
      (show CycleModel (stateValue .H1 x) ([0,4,0,1,1,(d/2-1),1]++[1]) from m0).rotate
    have t1 : trace (word [1,0,4,0,1,1,(d/2-1),1])=trace (word [1,2,1,d]) :=
      (trace_word_rotate [0,4,0,1,1,(d/2-1),1] [1]).symm.trans t0
    have ht1 : TailEquivalent x (value [1] (stateValue .H1 x)) := hs.trans (value_tailEquivalent [1] m0.irrational)
    have m2 : CycleModel (value [1] (stateValue .H1 x)) [(1+4),0,1,1,(d/2-1),1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[1,0,4]++[0,1,1,(d/2-1),1]) from m1).clean
    have t2 : trace (word [(1+4),0,1,1,(d/2-1),1])=trace (word [1,2,1,d]) :=
      (congrArg trace (zero_cleanup_context [] [0,1,1,(d/2-1),1] 1 4)).symm.trans t1
    have m3 : CycleModel (value [1] (stateValue .H1 x)) [((1+4)+1),1,(d/2-1),1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[(1+4),0,1]++[1,(d/2-1),1]) from m2).clean
    have t3 : trace (word [((1+4)+1),1,(d/2-1),1])=trace (word [1,2,1,d]) :=
      (congrArg trace (zero_cleanup_context [] [1,(d/2-1),1] (1+4) 1)).symm.trans t2
    have hh := same_four_cycle hx m3 hw (by simp <;> omega) hp ht1 t3
    exact hh
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_2103 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : 3≤a ∧ a%2=1)
    (hb : b=2)
    (hc : c=1)
    (hd : 4≤d ∧ d%2=0)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  obtain ⟨ha,hpa⟩ := ha
  subst b
  subst c
  obtain ⟨hd,hpd⟩ := hd
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2*a,1,2,d/2] : List ℤ)=[a,2,1,d] ∨ ([2*a,1,2,d/2] : List ℤ)=[2,1,d,a] ∨ ([2*a,1,2,d/2] : List ℤ)=[1,d,a,2] ∨ ([2*a,1,2,d/2] : List ℤ)=[d,a,2,1] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2*a,1,2,d/2] := by simpa [run,next,emit,hpa,hpd] using raw
    have t0 : trace (word [2*a,1,2,d/2])=trace (word [a,2,1,d]) := by simpa [run,next,emit,hpa,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      ([a/2,1,(1+1),(1+2*d)] : List ℤ)=[a,2,1,d] ∨ ([a/2,1,(1+1),(1+2*d)] : List ℤ)=[2,1,d,a] ∨ ([a/2,1,(1+1),(1+2*d)] : List ℤ)=[1,d,a,2] ∨ ([a/2,1,(1+1),(1+2*d)] : List ℤ)=[d,a,2,1] := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [a/2,1,1,0,1,1,0,2*d] := by simpa [run,next,emit,hpa,hpd] using raw
    have t0 : trace (word [a/2,1,1,0,1,1,0,2*d])=trace (word [a,2,1,d]) := by simpa [run,next,emit,hpa,hpd] using tr
    have m1 : CycleModel (stateValue .H0 x) [a/2,1,(1+1),1,0,2*d] :=
      (show CycleModel (stateValue .H0 x) ([a/2,1]++[1,0,1]++[1,0,2*d]) from m0).clean
    have t1 : trace (word [a/2,1,(1+1),1,0,2*d])=trace (word [a,2,1,d]) :=
      (congrArg trace (zero_cleanup_context [a/2,1] [1,0,2*d] 1 1)).symm.trans t0
    have m2 : CycleModel (stateValue .H0 x) [a/2,1,(1+1),(1+2*d)] :=
      (show CycleModel (stateValue .H0 x) ([a/2,1,(1+1)]++[1,0,2*d]++[]) from m1).clean
    have t2 : trace (word [a/2,1,(1+1),(1+2*d)])=trace (word [a,2,1,d]) :=
      (congrArg trace (zero_cleanup_context [a/2,1,(1+1)] [] 1 (2*d))).symm.trans t1
    have hh := same_four_cycle hx m2 hw (by simp <;> omega) hp hs t2
    exact hh
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      False := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [a/2,4,0,1,1,(d/2-1),1,1] := by simpa [run,next,emit,hpa,hpd] using raw
    have t0 : trace (word [a/2,4,0,1,1,(d/2-1),1,1])=trace (word [a,2,1,d]) := by simpa [run,next,emit,hpa,hpd] using tr
    have m1 : CycleModel (stateValue .H1 x) [a/2,(4+1),1,(d/2-1),1,1] :=
      (show CycleModel (stateValue .H1 x) ([a/2]++[4,0,1]++[1,(d/2-1),1,1]) from m0).clean
    have t1 : trace (word [a/2,(4+1),1,(d/2-1),1,1])=trace (word [a,2,1,d]) :=
      (congrArg trace (zero_cleanup_context [a/2] [1,(d/2-1),1,1] 4 1)).symm.trans t0
    have hh := same_four_cycle hx m1 hw (by simp <;> omega) hp hs t1
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_0303 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : a=1)
    (hb : 4≤b ∧ b%2=0)
    (hc : c=1)
    (hd : 4≤d ∧ d%2=0)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  subst a
  obtain ⟨hb,hpb⟩ := hb
  subst c
  obtain ⟨hd,hpd⟩ := hd
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2,b/2,2,d/2] : List ℤ)=[1,b,1,d] ∨ ([2,b/2,2,d/2] : List ℤ)=[b,1,d,1] ∨ ([2,b/2,2,d/2] : List ℤ)=[1,d,1,b] ∨ ([2,b/2,2,d/2] : List ℤ)=[d,1,b,1] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2,b/2,2,d/2] := by simpa [run,next,emit,hpb,hpd] using raw
    have t0 : trace (word [2,b/2,2,d/2])=trace (word [1,b,1,d]) := by simpa [run,next,emit,hpb,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      ([(1+(2*d+1)),1,(b/2-1),1] : List ℤ)=[1,b,1,d] ∨ ([(1+(2*d+1)),1,(b/2-1),1] : List ℤ)=[b,1,d,1] ∨ ([(1+(2*d+1)),1,(b/2-1),1] : List ℤ)=[1,d,1,b] ∨ ([(1+(2*d+1)),1,(b/2-1),1] : List ℤ)=[d,1,b,1] := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [0,1,1,(b/2-1),1,1,0,2*d] := by simpa [run,next,emit,hpb,hpd] using raw
    have t0 : trace (word [0,1,1,(b/2-1),1,1,0,2*d])=trace (word [1,b,1,d]) := by simpa [run,next,emit,hpb,hpd] using tr
    have m1 : CycleModel (value [2*d] (stateValue .H0 x)) [2*d,0,1,1,(b/2-1),1,1,0] :=
      (show CycleModel (stateValue .H0 x) ([0,1,1,(b/2-1),1,1,0]++[2*d]) from m0).rotate
    have t1 : trace (word [2*d,0,1,1,(b/2-1),1,1,0])=trace (word [1,b,1,d]) :=
      (trace_word_rotate [0,1,1,(b/2-1),1,1,0] [2*d]).symm.trans t0
    have ht1 : TailEquivalent x (value [2*d] (stateValue .H0 x)) := hs.trans (value_tailEquivalent [2*d] m0.irrational)
    have m2 : CycleModel (value [2*d] (stateValue .H0 x)) [(2*d+1),1,(b/2-1),1,1,0] :=
      (show CycleModel (value [2*d] (stateValue .H0 x)) ([]++[2*d,0,1]++[1,(b/2-1),1,1,0]) from m1).clean
    have t2 : trace (word [(2*d+1),1,(b/2-1),1,1,0])=trace (word [1,b,1,d]) :=
      (congrArg trace (zero_cleanup_context [] [1,(b/2-1),1,1,0] (2*d) 1)).symm.trans t1
    have m3 : CycleModel (value [1,0] (value [2*d] (stateValue .H0 x))) [1,0,(2*d+1),1,(b/2-1),1] :=
      (show CycleModel (value [2*d] (stateValue .H0 x)) ([(2*d+1),1,(b/2-1),1]++[1,0]) from m2).rotate
    have t3 : trace (word [1,0,(2*d+1),1,(b/2-1),1])=trace (word [1,b,1,d]) :=
      (trace_word_rotate [(2*d+1),1,(b/2-1),1] [1,0]).symm.trans t2
    have ht3 : TailEquivalent x (value [1,0] (value [2*d] (stateValue .H0 x))) := ht1.trans (value_tailEquivalent [1,0] m2.irrational)
    have m4 : CycleModel (value [1,0] (value [2*d] (stateValue .H0 x))) [(1+(2*d+1)),1,(b/2-1),1] :=
      (show CycleModel (value [1,0] (value [2*d] (stateValue .H0 x))) ([]++[1,0,(2*d+1)]++[1,(b/2-1),1]) from m3).clean
    have t4 : trace (word [(1+(2*d+1)),1,(b/2-1),1])=trace (word [1,b,1,d]) :=
      (congrArg trace (zero_cleanup_context [] [1,(b/2-1),1] 1 ((2*d+1)))).symm.trans t3
    have hh := same_four_cycle hx m4 hw (by simp <;> omega) hp ht3 t4
    exact hh
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      ([((1+2*b)+1),1,(d/2-1),1] : List ℤ)=[1,b,1,d] ∨ ([((1+2*b)+1),1,(d/2-1),1] : List ℤ)=[b,1,d,1] ∨ ([((1+2*b)+1),1,(d/2-1),1] : List ℤ)=[1,d,1,b] ∨ ([((1+2*b)+1),1,(d/2-1),1] : List ℤ)=[d,1,b,1] := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [0,2*b,0,1,1,(d/2-1),1,1] := by simpa [run,next,emit,hpb,hpd] using raw
    have t0 : trace (word [0,2*b,0,1,1,(d/2-1),1,1])=trace (word [1,b,1,d]) := by simpa [run,next,emit,hpb,hpd] using tr
    have m1 : CycleModel (value [1] (stateValue .H1 x)) [1,0,2*b,0,1,1,(d/2-1),1] :=
      (show CycleModel (stateValue .H1 x) ([0,2*b,0,1,1,(d/2-1),1]++[1]) from m0).rotate
    have t1 : trace (word [1,0,2*b,0,1,1,(d/2-1),1])=trace (word [1,b,1,d]) :=
      (trace_word_rotate [0,2*b,0,1,1,(d/2-1),1] [1]).symm.trans t0
    have ht1 : TailEquivalent x (value [1] (stateValue .H1 x)) := hs.trans (value_tailEquivalent [1] m0.irrational)
    have m2 : CycleModel (value [1] (stateValue .H1 x)) [(1+2*b),0,1,1,(d/2-1),1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[1,0,2*b]++[0,1,1,(d/2-1),1]) from m1).clean
    have t2 : trace (word [(1+2*b),0,1,1,(d/2-1),1])=trace (word [1,b,1,d]) :=
      (congrArg trace (zero_cleanup_context [] [0,1,1,(d/2-1),1] 1 (2*b))).symm.trans t1
    have m3 : CycleModel (value [1] (stateValue .H1 x)) [((1+2*b)+1),1,(d/2-1),1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[(1+2*b),0,1]++[1,(d/2-1),1]) from m2).clean
    have t3 : trace (word [((1+2*b)+1),1,(d/2-1),1])=trace (word [1,b,1,d]) :=
      (congrArg trace (zero_cleanup_context [] [1,(d/2-1),1] ((1+2*b)) 1)).symm.trans t2
    have hh := same_four_cycle hx m3 hw (by simp <;> omega) hp ht1 t3
    exact hh
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_2303 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : 3≤a ∧ a%2=1)
    (hb : 4≤b ∧ b%2=0)
    (hc : c=1)
    (hd : 4≤d ∧ d%2=0)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  obtain ⟨ha,hpa⟩ := ha
  obtain ⟨hb,hpb⟩ := hb
  subst c
  obtain ⟨hd,hpd⟩ := hd
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2*a,b/2,2,d/2] : List ℤ)=[a,b,1,d] ∨ ([2*a,b/2,2,d/2] : List ℤ)=[b,1,d,a] ∨ ([2*a,b/2,2,d/2] : List ℤ)=[1,d,a,b] ∨ ([2*a,b/2,2,d/2] : List ℤ)=[d,a,b,1] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2*a,b/2,2,d/2] := by simpa [run,next,emit,hpa,hpb,hpd] using raw
    have t0 : trace (word [2*a,b/2,2,d/2])=trace (word [a,b,1,d]) := by simpa [run,next,emit,hpa,hpb,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      False := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [a/2,1,1,(b/2-1),1,1,0,2*d] := by simpa [run,next,emit,hpa,hpb,hpd] using raw
    have t0 : trace (word [a/2,1,1,(b/2-1),1,1,0,2*d])=trace (word [a,b,1,d]) := by simpa [run,next,emit,hpa,hpb,hpd] using tr
    have m1 : CycleModel (stateValue .H0 x) [a/2,1,1,(b/2-1),1,(1+2*d)] :=
      (show CycleModel (stateValue .H0 x) ([a/2,1,1,(b/2-1),1]++[1,0,2*d]++[]) from m0).clean
    have t1 : trace (word [a/2,1,1,(b/2-1),1,(1+2*d)])=trace (word [a,b,1,d]) :=
      (congrArg trace (zero_cleanup_context [a/2,1,1,(b/2-1),1] [] 1 (2*d))).symm.trans t0
    have hh := same_four_cycle hx m1 hw (by simp <;> omega) hp hs t1
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      False := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [a/2,2*b,0,1,1,(d/2-1),1,1] := by simpa [run,next,emit,hpa,hpb,hpd] using raw
    have t0 : trace (word [a/2,2*b,0,1,1,(d/2-1),1,1])=trace (word [a,b,1,d]) := by simpa [run,next,emit,hpa,hpb,hpd] using tr
    have m1 : CycleModel (stateValue .H1 x) [a/2,(2*b+1),1,(d/2-1),1,1] :=
      (show CycleModel (stateValue .H1 x) ([a/2]++[2*b,0,1]++[1,(d/2-1),1,1]) from m0).clean
    have t1 : trace (word [a/2,(2*b+1),1,(d/2-1),1,1])=trace (word [a,b,1,d]) :=
      (congrArg trace (zero_cleanup_context [a/2] [1,(d/2-1),1,1] (2*b) 1)).symm.trans t0
    have hh := same_four_cycle hx m1 hw (by simp <;> omega) hp hs t1
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_0123 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : a=1)
    (hb : b=2)
    (hc : 3≤c ∧ c%2=1)
    (hd : 4≤d ∧ d%2=0)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  subst a
  subst b
  obtain ⟨hc,hpc⟩ := hc
  obtain ⟨hd,hpd⟩ := hd
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2,1,2*c,d/2] : List ℤ)=[1,2,c,d] ∨ ([2,1,2*c,d/2] : List ℤ)=[2,c,d,1] ∨ ([2,1,2*c,d/2] : List ℤ)=[c,d,1,2] ∨ ([2,1,2*c,d/2] : List ℤ)=[d,1,2,c] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2,1,2*c,d/2] := by simpa [run,next,emit,hpc,hpd] using raw
    have t0 : trace (word [2,1,2*c,d/2])=trace (word [1,2,c,d]) := by simpa [run,next,emit,hpc,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      ([(2*d+1),(1+1),1,c/2] : List ℤ)=[1,2,c,d] ∨ ([(2*d+1),(1+1),1,c/2] : List ℤ)=[2,c,d,1] ∨ ([(2*d+1),(1+1),1,c/2] : List ℤ)=[c,d,1,2] ∨ ([(2*d+1),(1+1),1,c/2] : List ℤ)=[d,1,2,c] := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [0,1,1,0,1,1,c/2,2*d] := by simpa [run,next,emit,hpc,hpd] using raw
    have t0 : trace (word [0,1,1,0,1,1,c/2,2*d])=trace (word [1,2,c,d]) := by simpa [run,next,emit,hpc,hpd] using tr
    have m1 : CycleModel (value [2*d] (stateValue .H0 x)) [2*d,0,1,1,0,1,1,c/2] :=
      (show CycleModel (stateValue .H0 x) ([0,1,1,0,1,1,c/2]++[2*d]) from m0).rotate
    have t1 : trace (word [2*d,0,1,1,0,1,1,c/2])=trace (word [1,2,c,d]) :=
      (trace_word_rotate [0,1,1,0,1,1,c/2] [2*d]).symm.trans t0
    have ht1 : TailEquivalent x (value [2*d] (stateValue .H0 x)) := hs.trans (value_tailEquivalent [2*d] m0.irrational)
    have m2 : CycleModel (value [2*d] (stateValue .H0 x)) [(2*d+1),1,0,1,1,c/2] :=
      (show CycleModel (value [2*d] (stateValue .H0 x)) ([]++[2*d,0,1]++[1,0,1,1,c/2]) from m1).clean
    have t2 : trace (word [(2*d+1),1,0,1,1,c/2])=trace (word [1,2,c,d]) :=
      (congrArg trace (zero_cleanup_context [] [1,0,1,1,c/2] (2*d) 1)).symm.trans t1
    have m3 : CycleModel (value [2*d] (stateValue .H0 x)) [(2*d+1),(1+1),1,c/2] :=
      (show CycleModel (value [2*d] (stateValue .H0 x)) ([(2*d+1)]++[1,0,1]++[1,c/2]) from m2).clean
    have t3 : trace (word [(2*d+1),(1+1),1,c/2])=trace (word [1,2,c,d]) :=
      (congrArg trace (zero_cleanup_context [(2*d+1)] [1,c/2] 1 1)).symm.trans t2
    have hh := same_four_cycle hx m3 hw (by simp <;> omega) hp ht1 t3
    exact hh
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      False := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [0,4,c/2,1,1,(d/2-1),1,1] := by simpa [run,next,emit,hpc,hpd] using raw
    have t0 : trace (word [0,4,c/2,1,1,(d/2-1),1,1])=trace (word [1,2,c,d]) := by simpa [run,next,emit,hpc,hpd] using tr
    have m1 : CycleModel (value [1] (stateValue .H1 x)) [1,0,4,c/2,1,1,(d/2-1),1] :=
      (show CycleModel (stateValue .H1 x) ([0,4,c/2,1,1,(d/2-1),1]++[1]) from m0).rotate
    have t1 : trace (word [1,0,4,c/2,1,1,(d/2-1),1])=trace (word [1,2,c,d]) :=
      (trace_word_rotate [0,4,c/2,1,1,(d/2-1),1] [1]).symm.trans t0
    have ht1 : TailEquivalent x (value [1] (stateValue .H1 x)) := hs.trans (value_tailEquivalent [1] m0.irrational)
    have m2 : CycleModel (value [1] (stateValue .H1 x)) [(1+4),c/2,1,1,(d/2-1),1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[1,0,4]++[c/2,1,1,(d/2-1),1]) from m1).clean
    have t2 : trace (word [(1+4),c/2,1,1,(d/2-1),1])=trace (word [1,2,c,d]) :=
      (congrArg trace (zero_cleanup_context [] [c/2,1,1,(d/2-1),1] 1 4)).symm.trans t1
    have hh := same_four_cycle hx m2 hw (by simp <;> omega) hp ht1 t2
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_2123 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : 3≤a ∧ a%2=1)
    (hb : b=2)
    (hc : 3≤c ∧ c%2=1)
    (hd : 4≤d ∧ d%2=0)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  obtain ⟨ha,hpa⟩ := ha
  subst b
  obtain ⟨hc,hpc⟩ := hc
  obtain ⟨hd,hpd⟩ := hd
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2*a,1,2*c,d/2] : List ℤ)=[a,2,c,d] ∨ ([2*a,1,2*c,d/2] : List ℤ)=[2,c,d,a] ∨ ([2*a,1,2*c,d/2] : List ℤ)=[c,d,a,2] ∨ ([2*a,1,2*c,d/2] : List ℤ)=[d,a,2,c] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2*a,1,2*c,d/2] := by simpa [run,next,emit,hpa,hpc,hpd] using raw
    have t0 : trace (word [2*a,1,2*c,d/2])=trace (word [a,2,c,d]) := by simpa [run,next,emit,hpa,hpc,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      False := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [a/2,1,1,0,1,1,c/2,2*d] := by simpa [run,next,emit,hpa,hpc,hpd] using raw
    have t0 : trace (word [a/2,1,1,0,1,1,c/2,2*d])=trace (word [a,2,c,d]) := by simpa [run,next,emit,hpa,hpc,hpd] using tr
    have m1 : CycleModel (stateValue .H0 x) [a/2,1,(1+1),1,c/2,2*d] :=
      (show CycleModel (stateValue .H0 x) ([a/2,1]++[1,0,1]++[1,c/2,2*d]) from m0).clean
    have t1 : trace (word [a/2,1,(1+1),1,c/2,2*d])=trace (word [a,2,c,d]) :=
      (congrArg trace (zero_cleanup_context [a/2,1] [1,c/2,2*d] 1 1)).symm.trans t0
    have hh := same_four_cycle hx m1 hw (by simp <;> omega) hp hs t1
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      False := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [a/2,4,c/2,1,1,(d/2-1),1,1] := by simpa [run,next,emit,hpa,hpc,hpd] using raw
    have t0 : trace (word [a/2,4,c/2,1,1,(d/2-1),1,1])=trace (word [a,2,c,d]) := by simpa [run,next,emit,hpa,hpc,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_0323 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : a=1)
    (hb : 4≤b ∧ b%2=0)
    (hc : 3≤c ∧ c%2=1)
    (hd : 4≤d ∧ d%2=0)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  subst a
  obtain ⟨hb,hpb⟩ := hb
  obtain ⟨hc,hpc⟩ := hc
  obtain ⟨hd,hpd⟩ := hd
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2,b/2,2*c,d/2] : List ℤ)=[1,b,c,d] ∨ ([2,b/2,2*c,d/2] : List ℤ)=[b,c,d,1] ∨ ([2,b/2,2*c,d/2] : List ℤ)=[c,d,1,b] ∨ ([2,b/2,2*c,d/2] : List ℤ)=[d,1,b,c] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2,b/2,2*c,d/2] := by simpa [run,next,emit,hpb,hpc,hpd] using raw
    have t0 : trace (word [2,b/2,2*c,d/2])=trace (word [1,b,c,d]) := by simpa [run,next,emit,hpb,hpc,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      False := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [0,1,1,(b/2-1),1,1,c/2,2*d] := by simpa [run,next,emit,hpb,hpc,hpd] using raw
    have t0 : trace (word [0,1,1,(b/2-1),1,1,c/2,2*d])=trace (word [1,b,c,d]) := by simpa [run,next,emit,hpb,hpc,hpd] using tr
    have m1 : CycleModel (value [2*d] (stateValue .H0 x)) [2*d,0,1,1,(b/2-1),1,1,c/2] :=
      (show CycleModel (stateValue .H0 x) ([0,1,1,(b/2-1),1,1,c/2]++[2*d]) from m0).rotate
    have t1 : trace (word [2*d,0,1,1,(b/2-1),1,1,c/2])=trace (word [1,b,c,d]) :=
      (trace_word_rotate [0,1,1,(b/2-1),1,1,c/2] [2*d]).symm.trans t0
    have ht1 : TailEquivalent x (value [2*d] (stateValue .H0 x)) := hs.trans (value_tailEquivalent [2*d] m0.irrational)
    have m2 : CycleModel (value [2*d] (stateValue .H0 x)) [(2*d+1),1,(b/2-1),1,1,c/2] :=
      (show CycleModel (value [2*d] (stateValue .H0 x)) ([]++[2*d,0,1]++[1,(b/2-1),1,1,c/2]) from m1).clean
    have t2 : trace (word [(2*d+1),1,(b/2-1),1,1,c/2])=trace (word [1,b,c,d]) :=
      (congrArg trace (zero_cleanup_context [] [1,(b/2-1),1,1,c/2] (2*d) 1)).symm.trans t1
    have hh := same_four_cycle hx m2 hw (by simp <;> omega) hp ht1 t2
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      False := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [0,2*b,c/2,1,1,(d/2-1),1,1] := by simpa [run,next,emit,hpb,hpc,hpd] using raw
    have t0 : trace (word [0,2*b,c/2,1,1,(d/2-1),1,1])=trace (word [1,b,c,d]) := by simpa [run,next,emit,hpb,hpc,hpd] using tr
    have m1 : CycleModel (value [1] (stateValue .H1 x)) [1,0,2*b,c/2,1,1,(d/2-1),1] :=
      (show CycleModel (stateValue .H1 x) ([0,2*b,c/2,1,1,(d/2-1),1]++[1]) from m0).rotate
    have t1 : trace (word [1,0,2*b,c/2,1,1,(d/2-1),1])=trace (word [1,b,c,d]) :=
      (trace_word_rotate [0,2*b,c/2,1,1,(d/2-1),1] [1]).symm.trans t0
    have ht1 : TailEquivalent x (value [1] (stateValue .H1 x)) := hs.trans (value_tailEquivalent [1] m0.irrational)
    have m2 : CycleModel (value [1] (stateValue .H1 x)) [(1+2*b),c/2,1,1,(d/2-1),1] :=
      (show CycleModel (value [1] (stateValue .H1 x)) ([]++[1,0,2*b]++[c/2,1,1,(d/2-1),1]) from m1).clean
    have t2 : trace (word [(1+2*b),c/2,1,1,(d/2-1),1])=trace (word [1,b,c,d]) :=
      (congrArg trace (zero_cleanup_context [] [c/2,1,1,(d/2-1),1] 1 (2*b))).symm.trans t1
    have hh := same_four_cycle hx m2 hw (by simp <;> omega) hp ht1 t2
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



theorem case_2323 {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a)
    (ha : 3≤a ∧ a%2=1)
    (hb : 4≤b ∧ b%2=0)
    (hc : 3≤c ∧ c%2=1)
    (hd : 4≤d ∧ d%2=0)
    : a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  obtain ⟨ha,hpa⟩ := ha
  obtain ⟨hb,hpb⟩ := hb
  obtain ⟨hc,hpc⟩ := hc
  obtain ⟨hd,hpd⟩ := hd
  have hD (hs : TailEquivalent x (stateValue .D x)) :
      ([2*a,b/2,2*c,d/2] : List ℤ)=[a,b,c,d] ∨ ([2*a,b/2,2*c,d/2] : List ℤ)=[b,c,d,a] ∨ ([2*a,b/2,2*c,d/2] : List ℤ)=[c,d,a,b] ∨ ([2*a,b/2,2*c,d/2] : List ℤ)=[d,a,b,c] := by
    have raw := hx.outputModel hw .D (hx.all_states_closed hclass .D)
    have tr := output_trace hx hclass .D
    have m0 : CycleModel (stateValue .D x) [2*a,b/2,2*c,d/2] := by simpa [run,next,emit,hpa,hpb,hpc,hpd] using raw
    have t0 : trace (word [2*a,b/2,2*c,d/2])=trace (word [a,b,c,d]) := by simpa [run,next,emit,hpa,hpb,hpc,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    exact hh
  have hH0 (hs : TailEquivalent x (stateValue .H0 x)) :
      False := by
    have raw := hx.outputModel hw .H0 (hx.all_states_closed hclass .H0)
    have tr := output_trace hx hclass .H0
    have m0 : CycleModel (stateValue .H0 x) [a/2,1,1,(b/2-1),1,1,c/2,2*d] := by simpa [run,next,emit,hpa,hpb,hpc,hpd] using raw
    have t0 : trace (word [a/2,1,1,(b/2-1),1,1,c/2,2*d])=trace (word [a,b,c,d]) := by simpa [run,next,emit,hpa,hpb,hpc,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  have hH1 (hs : TailEquivalent x (stateValue .H1 x)) :
      False := by
    have raw := hx.outputModel hw .H1 (hx.all_states_closed hclass .H1)
    have tr := output_trace hx hclass .H1
    have m0 : CycleModel (stateValue .H1 x) [a/2,2*b,c/2,1,1,(d/2-1),1,1] := by simpa [run,next,emit,hpa,hpb,hpc,hpd] using raw
    have t0 : trace (word [a/2,2*b,c/2,1,1,(d/2-1),1,1])=trace (word [a,b,c,d]) := by simpa [run,next,emit,hpa,hpb,hpc,hpd] using tr
    have hh := same_four_cycle hx m0 hw (by simp <;> omega) hp hs t0
    rcases hh with hh|hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · have hi := hD hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hD hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH0 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)
  · have hi := hH0 hs
    have hj := hH1 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hD ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · have hi := hH1 hs
    have hj := hH0 ht
    simp only [List.cons.injEq,and_true] at hi hj <;> omega
  · exact False.elim (hst rfl)



end VV.Problem4.PeriodFourCases

