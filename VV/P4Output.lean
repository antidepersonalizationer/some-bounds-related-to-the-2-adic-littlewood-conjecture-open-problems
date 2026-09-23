import VV.P4Period
import VV.P5RealCursor
import VV.P4SmallPeriods

/-! Closed Hurwitz runs give actual, normalized output periods. -/

namespace VV.Hurwitz
open P5RealCursor

theorem stateMatrix_det (s : State) : det (stateMatrix s) = 2 := by cases s <;> rfl

theorem run_realizes (s : State) (w : List ℤ) {x : ℝ} (hx : Irrational x) :
    stateValue s (value w x) = value (run s w).1 (stateValue (run s w).2 x) := by
  have hleft := (show Rel (word w) x (value w x) from value_matrix w hx).comp
    (stateValue_rel s (value w x))
  have hright := (stateValue_rel (run s w).2 x).comp
    (show Rel (word (run s w).1) (stateValue (run s w).2 x)
      (value (run s w).1 (stateValue (run s w).2 x)) from
        value_matrix _ (stateValue_irrational _ hx))
  rw [run_matrix] at hleft
  apply hleft.unique ?_ hright
  rw [det_mul, stateMatrix_det]
  apply mul_ne_zero _ (by decide)
  rcases word_det_unit (run s w).1 with h | h <;> rw [h] <;> norm_num

theorem CycleModel.outputModel {x : ℝ} {w : List ℤ} (h : CycleModel x w)
    (hw : ∀ a ∈ w, 1 ≤ a) (s : State) (hclosed : (run s w).2 = s) :
    CycleModel (stateValue s x) (run s w).1 := by
  have hmat := run_matrix s w
  rw [hclosed] at hmat
  refine ⟨stateValue_irrational s h.irrational, stateValue_pos s (h.gt_one hw),
    run_nonnegative s w hw, ?_, ?_⟩
  · have he := run_realizes s w h.irrational
    rw [h.fixed,hclosed] at he
    exact he.symm
  · rw [← trace_similar (by rw [stateMatrix_det]; decide) hmat]
    exact h.hyperbolic

theorem CycleModel.all_states_closed {x : ℝ} {w : List ℤ} (h : CycleModel x w)
    (hclass : HasTripleRepresentative x) (s : State) : (run s w).2 = s := by
  obtain ⟨A,B,C,hA,hp,hr,hpell⟩ := (problem3_classification h.irrational).mp hclass
  have hfix := value_matrix w h.irrational
  rw [h.fixed] at hfix
  obtain ⟨ha,hb,hc,hd⟩ := stabilizer_parity (word w) h.irrational hA hp hr hpell
    (word_det_unit w) hfix
  exact run_state_closed_of_parity w ha hb hc hd s

/-- The real output of every good closed branch has exactly the input's
least period, after the explicitly proved cyclic zero normalization. -/
theorem normalized_output_exact_length {x : ℝ} {w : List ℤ}
    (hx : CycleModel x w) (hw : ∀ a ∈ w, 1 ≤ a)
    (hmin : Problem4.ExactEventualPeriod x w.length) (hlen : 2 ≤ w.length)
    (hclass : HasTripleRepresentative x) (s : State)
    (hgood : TailEquivalent x (stateValue s x)) :
    ∃ y v, CycleModel y v ∧ (∀ a ∈ v, 1 ≤ a) ∧ v.length = w.length ∧
      TailEquivalent x y ∧ trace (word v) = trace (word w) := by
  have hc := hx.all_states_closed hclass s
  have hr := hx.outputModel hw s hc
  obtain ⟨y,v,hy,hv,_,ht,he⟩ := hr.normalize
  have hxy := hgood.trans ht
  have htr : trace (word v) = trace (word w) := by
    have hm := run_matrix s w
    rw [hc] at hm
    exact he.trans (trace_similar (by rw [stateMatrix_det]; decide) hm).symm
  exact ⟨y,v,hy,hv,equal_length_of_cycle_trace hx hy hw hv hmin hlen hxy htr,hxy,htr⟩

theorem value_actual_digitBlock {x : ℝ} (hx : Irrational x) (n p : ℕ) :
    value (P5Period.digitBlock x n p) (completeQuotient x (n+p)) = completeQuotient x n := by
  have hr := digitBlock_relation hx n p
  have hv : Rel (word (P5Period.digitBlock x n p)) (completeQuotient x (n+p))
      (value (P5Period.digitBlock x n p) (completeQuotient x (n+p))) :=
    value_matrix _ (completeQuotient_irrational hx _)
  apply hv.unique ?_ hr
  rcases word_det_unit (P5Period.digitBlock x n p) with h | h <;> rw [h] <;> norm_num

theorem stateValue_completeQuotient_tail {x : ℝ} (hx : Irrational x) (n : ℕ) (s : State) :
    TailEquivalent (stateValue s x)
      (stateValue (run s (P5Period.digitBlock x 0 n)).2 (completeQuotient x n)) := by
  have hr := run_realizes s (P5Period.digitBlock x 0 n) (completeQuotient_irrational hx n)
  have he := value_actual_digitBlock hx 0 n
  simp only [Nat.zero_add] at he
  rw [he] at hr
  change stateValue s x = _ at hr
  rw [hr]
  exact (value_tailEquivalent _ (stateValue_irrational _ (completeQuotient_irrational hx n))).symm

def HasGoodPair (x : ℝ) : Prop :=
  ∃ s t : State, s ≠ t ∧ TailEquivalent x (stateValue s x) ∧ TailEquivalent x (stateValue t x)

theorem goodPair_of_triple {x : ℝ} (hx : Problem3Triple x) : HasGoodPair x := by
  refine ⟨.H0,.H1,by decide,hx.2.1,?_⟩
  have ht := tailEquivalent_add_int ((x+1)/2) (-1)
  have he : (x+1)/2+(-1:ℤ) = stateValue .H1 x := by simp [stateValue]; ring
  exact hx.2.2.trans (he ▸ ht)

theorem goodPair_completeQuotient {x : ℝ} (hx : Irrational x) (hg : HasGoodPair x) (n : ℕ) :
    HasGoodPair (completeQuotient x n) := by
  obtain ⟨s,t,hst,hs,ht⟩ := hg
  refine ⟨(run s (P5Period.digitBlock x 0 n)).2,(run t (P5Period.digitBlock x 0 n)).2,
    fun he => hst (run_state_injective _ he), ?_, ?_⟩
  · exact (tailEquivalent_completeQuotient x n).symm.trans
      (hs.trans (stateValue_completeQuotient_tail hx n s))
  · exact (tailEquivalent_completeQuotient x n).symm.trans
      (ht.trans (stateValue_completeQuotient_tail hx n t))

/-- Every actual successful least-period class admits a positive pure cycle
with a pair of distinct good Hurwitz branches. No Lagrange theorem or
transducer encoding is assumed. -/
theorem positive_cycle_of_representative {ℓ : ℕ} (r : Problem4.Representative ℓ) :
    ∃ x w, CycleModel x w ∧ (∀ a ∈ w, 1 ≤ a) ∧ w.length = ℓ ∧
      Problem4.ExactEventualPeriod x ℓ ∧ TailEquivalent r.val x ∧ HasGoodPair x := by
  have hx := r.property.1.1
  obtain ⟨N,hN⟩ := r.property.2.2.1
  let x := completeQuotient r.val (N+1)
  let w := P5Period.digitBlock r.val (N+1) ℓ
  have hp : ∀ k : ℕ, partialQuotient r.val (N+1+ℓ+k) = partialQuotient r.val (N+1+k) := by
    intro k
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hN (N+k) (by omega)
  have hc := P5Period.completeQuotient_eq_of_periodic hx (N+1) ℓ hp
  have hw : ∀ a ∈ w, 1 ≤ a := P5Period.digitBlock_positive hx _ _ (by omega)
  have hlen : w.length = ℓ := P5Period.digitBlock_length _ _ _
  have hl3 := Problem4.period_at_least_three_of_triple r.property.1 r.property.2.1
    r.property.2.2.1
  have hxy : TailEquivalent r.val x := tailEquivalent_completeQuotient _ _
  refine ⟨x,w,?_,hw,hlen,
    (Problem4.exactEventualPeriod_iff_of_tailEquivalent hxy ℓ).mp r.property.2,
    hxy,goodPair_completeQuotient hx (goodPair_of_triple r.property.1) _⟩
  refine ⟨completeQuotient_irrational hx _, lt_trans zero_lt_one
    (one_lt_completeQuotient_succ hx N), fun a ha => le_trans (by omega : (0:ℤ) ≤ 1)
      (hw a ha), ?_, ?_⟩
  · have he := value_actual_digitBlock hx (N+1) ℓ
    rw [hc] at he
    exact he
  · obtain ⟨ha,_,_,hd⟩ := positive_long_word_bounds w hw (by omega)
    unfold trace
    omega

end VV.Hurwitz
