import VV.P4UniformDigits

/-!
# Exact classification at least period three

The three-state return condition forces all three digits to be odd. Root the
cycle at a largest digit. The doubling branch cannot have the same tail:
zero cleanup either changes the period length or leaves a digit larger than
that maximum. Both halving branches must therefore succeed. Their lengths
force the other two digits to be 1, and the remaining alignment forces 3.

All divisions, cleanup identities, and parity cases below are symbolic.
The representative (3 + sqrt 17) / 2 supplies existence, so the quotient
has cardinality exactly one, and its eventual digit alphabet is {1, 3}.
-/

noncomputable section
namespace VV.Problem4
open Hurwitz P5RealCursor

theorem digits_three {x : ℝ} {a b c : ℤ} (hx : CycleModel x [a,b,c])
    (hw : ∀d∈[a,b,c],1≤d) :
    partialQuotient x 0=a ∧ partialQuotient x 1=b ∧ partialQuotient x 2=c ∧
      partialQuotient x 3=a ∧ partialQuotient x 4=b := by
  have hd := hx.digitBlock hw
  simp only [List.length_cons,List.length_nil,P5Period.digitBlock,
    List.cons.injEq,true_and,and_true] at hd
  have hp : DigitPeriod x 3 := hx.digitPeriod hw
  exact ⟨hd.1,hd.2.1,hd.2.2,(hp 0).trans hd.1,(hp 1).trans hd.2.1⟩

theorem blocks_three {x : ℝ} {a b c : ℤ} (hx : CycleModel x [a,b,c])
    (hw : ∀d∈[a,b,c],1≤d) {k : ℕ} (hk : k<3) :
    P5Period.digitBlock x k 3=[a,b,c] ∨
      P5Period.digitBlock x k 3=[b,c,a] ∨
      P5Period.digitBlock x k 3=[c,a,b] := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := digits_three hx hw
  interval_cases k <;> simp [P5Period.digitBlock,h0,h1,h2,h3,h4]

theorem same_three_cycle {x y : ℝ} {a b c : ℤ} {v : List ℤ}
    (hx : CycleModel x [a,b,c]) (hy : CycleModel y v)
    (hw : ∀d∈[a,b,c],1≤d) (hv : ∀d∈v,1≤d)
    (hp : ExactEventualPeriod x 3) (hxy : TailEquivalent x y)
    (htr : trace (word v)=trace (word [a,b,c])) :
    v=[a,b,c] ∨ v=[b,c,a] ∨ v=[c,a,b] := by
  have hl := equal_length_of_cycle_trace hx hy hw hv hp (by norm_num) hxy htr
  obtain ⟨k,hk,he⟩ := cycle_block_alignment hx hy hw hv hl (by norm_num) hxy
  rw [he]
  exact blocks_three hx hw hk

theorem odd_three {x : ℝ} {a b c : ℤ} (hx : CycleModel x [a,b,c])
    (hc : HasTripleRepresentative x) : a%2=1 ∧ b%2=1 ∧ c%2=1 := by
  have hd := hx.all_states_closed hc State.D
  have hh := hx.all_states_closed hc State.H0
  have ha : a%2=0 ∨ a%2=1 := by omega
  have hb : b%2=0 ∨ b%2=1 := by omega
  have he : c%2=0 ∨ c%2=1 := by omega
  rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases he with he|he <;>
    simp [run,next,ha,hb,he] at hd hh <;> omega

def periodThreeValue : ℝ := (3+Real.sqrt 17)/2

theorem periodThreeValue_irrational : Irrational periodThreeValue := by
  have hi : Irrational (Real.sqrt 17) := by
    simpa using (show Nat.Prime 17 by norm_num).irrational_sqrt
  simpa [periodThreeValue] using (hi.intCast_add 3).div_natCast (by decide : (2:ℕ)≠0)

theorem periodThreeValue_positive : 0<periodThreeValue := by
  dsimp [periodThreeValue]
  positivity

theorem periodThreeValue_quadratic : periodThreeValue^2-3*periodThreeValue-2=0 := by
  have h := Real.sq_sqrt (show (0:ℝ)≤17 by norm_num)
  dsimp [periodThreeValue]
  nlinarith

theorem periodThreeValue_model : CycleModel periodThreeValue [3,1,1] := by
  have hp := periodThreeValue_positive
  have hq := periodThreeValue_quadratic
  refine ⟨periodThreeValue_irrational,hp,by simp,?_,by norm_num [trace,word,mul,digit,one]⟩
  simp only [value,Int.cast_ofNat,Int.cast_one]
  have h0 : periodThreeValue≠0 := ne_of_gt hp
  have h1 : periodThreeValue+1≠0 := by linarith
  have h2 : 2*periodThreeValue+1≠0 := by linarith
  field_simp
  nlinarith

theorem periodThreeValue_triple : Problem3Triple periodThreeValue := by
  apply (problem3_fixed_representative periodThreeValue_irrational
    (by decide : (1:ℤ)≠0)
    (show Problem3.PrimitiveTriple 1 (-3) (-2) from ⟨1,0,0,by norm_num⟩)
    (show ((1:ℤ):ℝ)*periodThreeValue^2+(-3:ℤ)*periodThreeValue+(-2:ℤ)=0 by
      convert periodThreeValue_quadratic using 1 <;> norm_num <;> ring)).mpr
  refine ⟨by decide,3,1,by decide,by decide,Or.inr ?_⟩
  norm_num [Problem3.discriminant]

theorem periodThreeValue_least : ExactEventualPeriod periodThreeValue 3 := by
  refine ⟨by decide,(periodThreeValue_model.digitPeriod (by simp)).eventual,?_⟩
  intro k hk hk3 hperiod
  have hh := period_at_least_three_of_triple periodThreeValue_triple hk hperiod
  omega

def periodThreeRepresentative : Representative 3 :=
  ⟨periodThreeValue,periodThreeValue_triple,periodThreeValue_least⟩

theorem class_three_nonempty : Nonempty (Class 3) := ⟨toClass periodThreeRepresentative⟩



theorem output_trace {x : ℝ} {w : List ℤ} (hx : CycleModel x w)
    (hc : HasTripleRepresentative x) (s : State) :
    trace (word (run s w).1)=trace (word w) := by
  have hm := run_matrix s w
  rw [hx.all_states_closed hc s] at hm
  exact (trace_similar (by rw [stateMatrix_det]; decide) hm).symm

theorem same_three_head_le {x y : ℝ} {a b c : ℤ} {v : List ℤ}
    (hx : CycleModel x [a,b,c]) (hy : CycleModel y v)
    (hw : ∀d∈[a,b,c],1≤d) (hv : ∀d∈v,1≤d)
    (hp : ExactEventualPeriod x 3) (hxy : TailEquivalent x y)
    (htr : trace (word v)=trace (word [a,b,c])) (hab : b≤a) (hac : c≤a) :
    v.headD 0≤a := by
  rcases same_three_cycle hx hy hw hv hp hxy htr with he|he|he
  · simp [he]
  · simpa [he] using hab
  · simpa [he] using hac

theorem no_good_D_of_max_three {x : ℝ} {a b c : ℤ}
    (hx : CycleModel x [a,b,c]) (hw : ∀d∈[a,b,c],1≤d)
    (hp : ExactEventualPeriod x 3) (hc : HasTripleRepresentative x)
    (hab : b≤a) (hac : c≤a) :
    ¬TailEquivalent x (stateValue .D x) := by
  intro hg
  obtain ⟨haodd,hbodd,hcodd⟩ := odd_three hx hc
  have ha : 1≤a := hw a (by simp)
  have hb : 1≤b := hw b (by simp)
  have hcc : 1≤c := hw c (by simp)
  have hy := hx.outputModel hw State.D (hx.all_states_closed hc .D)
  have ht := output_trace hx hc State.D
  simp [run,next,emit,haodd,hbodd,hcodd] at hy ht
  by_cases hb1 : b=1
  · subst b
    by_cases hc1 : c=1
    · subst c
      norm_num at hy ht
      have hy' : CycleModel (stateValue .D x) [2*a+1,1,0] :=
        (show CycleModel (stateValue .D x) ([]++[2*a,0,1]++[1,0]) from hy).clean
      have hy'' : CycleModel (value [1,0] (stateValue .D x)) [1,0,2*a+1] :=
        (show CycleModel (stateValue .D x) ([2*a+1]++[1,0]) from hy').rotate
      have hy''' : CycleModel (value [1,0] (stateValue .D x)) [2*a+2] := by
        convert (show CycleModel _ ([]++[1,0,2*a+1]++[]) from hy'').clean using 1 <;>
          simp <;> ring
      have htt : trace (word [2*a+2])=trace (word [a,1,1]) := by
        simp [trace,word,mul,digit,one]; ring
      have hh := same_three_cycle hx hy''' hw (by simp; omega) hp
        (hg.trans (value_tailEquivalent [1,0] hy.irrational)) htt
      rcases hh with hh|hh|hh <;> have := congrArg List.length hh <;> norm_num at this
    · have hc3 : 3≤c := by omega
      have hcd : 1≤c/2 := by omega
      norm_num at hy ht
      have hy' : CycleModel (stateValue .D x) [2*a+1,1,c/2] :=
        (show CycleModel (stateValue .D x) ([]++[2*a,0,1]++[1,c/2]) from hy).clean
      have htt : trace (word [2*a+1,1,c/2])=trace (word [a,1,c]) := by
        convert ht using 1 <;> simp [trace,word,mul,digit,one] <;> ring
      have hh := same_three_head_le hx hy' hw (by simp; omega) hp hg htt hab hac
      simp only [List.headD_cons] at hh
      omega
  · have hb3 : 3≤b := by omega
    have hbd : 1≤b/2 := by omega
    by_cases hc1 : c=1
    · subst c
      norm_num at hy ht
      have hy' : CycleModel (value [1,0] (stateValue .D x)) [1,0,2*a,b/2,1] :=
        (show CycleModel (stateValue .D x) ([2*a,b/2,1]++[1,0]) from hy).rotate
      have hy'' : CycleModel (value [1,0] (stateValue .D x)) [2*a+1,b/2,1] := by
        convert (show CycleModel _ ([]++[1,0,2*a]++[b/2,1]) from hy').clean using 1 <;>
          simp <;> ring
      have htt : trace (word [2*a+1,b/2,1])=trace (word [a,b,1]) := by
        convert ht using 1 <;> simp [trace,word,mul,digit,one] <;> ring
      have hh := same_three_head_le hx hy'' hw (by simp; omega) hp
        (hg.trans (value_tailEquivalent [1,0] hy.irrational)) htt hab hac
      simp only [List.headD_cons] at hh
      omega
    · have hc3 : 3≤c := by omega
      have hcd : 1≤c/2 := by omega
      have hlen := equal_length_of_cycle_trace hx hy hw (by simp; omega) hp
        (by norm_num) hg ht
      norm_num at hlen

theorem good_halves_of_max_three {x : ℝ} {a b c : ℤ}
    (hx : CycleModel x [a,b,c]) (hw : ∀d∈[a,b,c],1≤d)
    (hp : ExactEventualPeriod x 3) (hc : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hab : b≤a) (hac : c≤a) :
    TailEquivalent x (stateValue .H0 x) ∧ TailEquivalent x (stateValue .H1 x) := by
  have hn := no_good_D_of_max_three hx hw hp hc hab hac
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  cases s <;> cases t <;> simp_all







theorem period_one_of_three_ones {x : ℝ} (hx : CycleModel x [1,1,1]) :
    EventualPeriod x 1 := by
  have hw : ∀d∈([1,1,1] : List ℤ),1≤d := by simp
  obtain ⟨h0,h1,h2,_,_⟩ := digits_three hx hw
  have hp : DigitPeriod x 3 := hx.digitPeriod hw
  have hall (n : ℕ) : partialQuotient x n=1 := by
    rw [period_digit_mod hp n]
    have hn : n%3<3 := Nat.mod_lt _ (by decide)
    interval_cases n%3 <;> assumption
  have hp1 : DigitPeriod x 1 := by intro n; rw [hall,hall]
  exact hp1.eventual

theorem canonical_max_three {x : ℝ} {a b c : ℤ}
    (hx : CycleModel x [a,b,c]) (hw : ∀d∈[a,b,c],1≤d)
    (hp : ExactEventualPeriod x 3) (hc : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hab : b≤a) (hac : c≤a) :
    a=3 ∧ b=1 ∧ c=1 := by
  obtain ⟨haodd,hbodd,hcodd⟩ := odd_three hx hc
  have ha : 1≤a := hw a (by simp)
  have hb : 1≤b := hw b (by simp)
  have hcc : 1≤c := hw c (by simp)
  have ha3 : 3≤a := by
    by_contra hlt
    have hea : a=1 := by omega
    have heb : b=1 := by omega
    have hec : c=1 := by omega
    subst a b c
    exact hp.2.2 1 (by decide) (by decide) (period_one_of_three_ones hx)
  have had : 1≤a/2 := by omega
  obtain ⟨hH0,hH1⟩ := good_halves_of_max_three hx hw hp hc hg hab hac
  have hy0 := hx.outputModel hw State.H0 (hx.all_states_closed hc .H0)
  have hy1 := hx.outputModel hw State.H1 (hx.all_states_closed hc .H1)
  have ht0 := output_trace hx hc State.H0
  have ht1 := output_trace hx hc State.H1
  simp [run,next,emit,haodd,hbodd,hcodd] at hy0 hy1 ht0 ht1
  have hb1 : b=1 := by
    by_contra h
    have hb3 : 3≤b := by omega
    have hbd : 1≤b/2 := by omega
    have hlen := equal_length_of_cycle_trace hx hy0 hw (by simp; omega) hp
      (by norm_num) hH0 ht0
    norm_num at hlen
  have hc1 : c=1 := by
    by_contra h
    have hc3 : 3≤c := by omega
    have hcd : 1≤c/2 := by omega
    have hlen := equal_length_of_cycle_trace hx hy1 hw (by simp; omega) hp
      (by norm_num) hH1 ht1
    norm_num at hlen
  subst b c
  norm_num at hy0 ht0
  have hy' : CycleModel (stateValue .H0 x) [a/2,1,3] := by
    convert (show CycleModel _ ([a/2,1]++[1,0,2]++[]) from hy0).clean using 1
  have htt : trace (word [a/2,1,3])=trace (word [a,1,1]) := by
    convert ht0 using 1
  have hh := same_three_cycle hx hy' hw (by simp; omega) hp hH0 htt
  rcases hh with hh|hh|hh <;>
    simp only [List.cons.injEq,and_true] at hh <;> omega

theorem rootedWord_three_form (w : RootedWord 3) :
    w.val=[3,1,1] ∨ w.val=[1,3,1] ∨ w.val=[1,1,3] := by
  obtain ⟨x,hx,hw,hlen,hmin,hclass,hgood⟩ := w.property
  obtain ⟨a,b,c,hword⟩ := List.length_eq_three.mp hlen
  rw [hword] at hx hw
  let r : RootedCycle 3 := ⟨x,[a,b,c],hx,hw,rfl,hmin,hclass,hgood⟩
  have hrot1 : (r.rotate 1).w=[b,c,a] := by
    obtain ⟨h0,h1,h2,h3,h4⟩ := digits_three hx hw
    change P5Period.digitBlock x 1 3=_
    simp [P5Period.digitBlock,h1,h2,h3]
  have hrot2 : (r.rotate 2).w=[c,a,b] := by
    obtain ⟨h0,h1,h2,h3,h4⟩ := digits_three hx hw
    change P5Period.digitBlock x 2 3=_
    simp [P5Period.digitBlock,h2,h3,h4]
  have hmax : (b≤a ∧ c≤a) ∨ (a≤b ∧ c≤b) ∨ (a≤c ∧ b≤c) := by omega
  rcases hmax with hm|hm|hm
  · obtain ⟨rfl,rfl,rfl⟩ := canonical_max_three hx hw hmin hclass hgood hm.1 hm.2
    exact Or.inl hword
  · have hm' := (r.rotate 1).model
    have hp' := (r.rotate 1).positive
    rw [hrot1] at hm' hp'
    obtain ⟨rfl,rfl,rfl⟩ := canonical_max_three hm' hp' (r.rotate 1).least
      (r.rotate 1).triple (r.rotate 1).good hm.2 hm.1
    exact Or.inr (Or.inl hword)
  · have hm' := (r.rotate 2).model
    have hp' := (r.rotate 2).positive
    rw [hrot2] at hm' hp'
    obtain ⟨rfl,rfl,rfl⟩ := canonical_max_three hm' hp' (r.rotate 2).least
      (r.rotate 2).triple (r.rotate 2).good hm.1 hm.2
    exact Or.inr (Or.inr hword)

theorem card_rootedWord_three_le : Nat.card (RootedWord 3)≤3 := by
  let S : Finset (List ℤ) := {[3,1,1],[1,3,1],[1,1,3]}
  let f : RootedWord 3 → {w // w∈S} := fun w =>
    ⟨w.val,by simpa [S] using rootedWord_three_form w⟩
  have hf : Function.Injective f := by
    intro w v he
    apply Subtype.ext
    exact congrArg (fun z : {w : List ℤ // w∈S} => z.val) he
  have hh := Nat.card_le_card_of_injective f hf
  have hS : Nat.card {w : List ℤ // w∈S}=3 := by
    change Nat.card ↥S=3
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    norm_num [S]
  simpa only [hS] using hh

theorem card_class_three : Nat.card (Class 3)=1 := by
  have hupper := card_rootedWord_three_le
  rw [card_rootedWord] at hupper
  letI : Finite (Class 3) := (problem4_all_periods 3).1
  letI : Nonempty (Class 3) := class_three_nonempty
  have hpos : 0<Nat.card (Class 3) := Nat.card_pos
  omega




/-- The period-three stratum is exactly the tail class of `[3,1,1]`. -/
theorem period_three_iff {x : ℝ} :
    HasTripleRepresentative x ∧ ExactEventualPeriod x 3 ↔
      TailEquivalent x periodThreeValue := by
  constructor
  · rintro ⟨⟨y,hxy,hy⟩,hp⟩
    let r : Representative 3 :=
      ⟨y,hy,(exactEventualPeriod_iff_of_tailEquivalent hxy 3).mp hp⟩
    have hs : Subsingleton (Class 3) := (Nat.card_eq_one_iff_unique.mp card_class_three).1
    have he := hs.elim (toClass r) (toClass periodThreeRepresentative)
    exact hxy.trans ((toClass_eq_iff r periodThreeRepresentative).mp he)
  · intro h
    exact ⟨⟨periodThreeValue,h,periodThreeValue_triple⟩,
      (exactEventualPeriod_iff_of_tailEquivalent h 3).mpr periodThreeValue_least⟩

def periodThreeCycle : RootedCycle 3 :=
  ⟨periodThreeValue,[3,1,1],periodThreeValue_model,by simp,rfl,
    periodThreeValue_least,⟨periodThreeValue,TailEquivalent.refl _,periodThreeValue_triple⟩,
    goodPair_of_triple periodThreeValue_triple⟩

/-- This alphabet is evaluated symbolically; no template enumeration is used. -/
theorem uniformAlphabet_three : uniformAlphabet 3={1,3} := by
  ext a
  constructor
  · intro ha
    obtain ⟨w,hw⟩ := (mem_uniformAlphabet_iff 3 a).mp ha
    rcases rootedWord_three_form w with he|he|he <;>
      simp [he] at hw <;> simp [← hw]
  · intro ha
    have h1 : (1:ℤ)∈uniformAlphabet 3 := by
      have hh := periodThreeCycle.digit_mem_uniformAlphabet 1
      have hd := digits_three periodThreeValue_model (by simp)
      simpa only [periodThreeCycle,hd.2.1] using hh
    have h3 : (3:ℤ)∈uniformAlphabet 3 := by
      have hh := periodThreeCycle.digit_mem_uniformAlphabet 0
      have hd := digits_three periodThreeValue_model (by simp)
      simpa only [periodThreeCycle,hd.1] using hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl
    · exact h1
    · exact h3

theorem uniformDigitBound_three : uniformDigitBound 3=3 := by
  norm_num [uniformDigitBound,uniformAlphabet_three,Int.toNat]

theorem periodThreeValue_B : B periodThreeValue=3 := by
  apply le_antisymm
  · have hh := B_le_uniformDigitBound periodThreeCycle.triple periodThreeValue_least
    simpa only [uniformDigitBound_three] using hh
  · apply (B_atLeast_succ_iff periodThreeValue 2).mpr
    intro N
    refine ⟨3*N+2,by omega,?_⟩
    have hp : DigitPeriod periodThreeValue 3 := periodThreeCycle.period
    rw [period_digit_mod hp]
    have he : (3*N+2+1)%3=0 := by omega
    rw [he,(digits_three periodThreeValue_model (by simp)).1]
    norm_num

/-- Every successful least-period-three representative has limsup digit 3. -/
theorem B_eq_three_of_period_three {x : ℝ} (hc : HasTripleRepresentative x)
    (hp : ExactEventualPeriod x 3) : B x=3 :=
  (period_three_iff.mp ⟨hc,hp⟩).B_eq.trans periodThreeValue_B

end VV.Problem4


