import VV.P4Output
import VV.P4Alignment

/-! Rooting a genuine least-period tail class gives exactly its period many
distinct positive continued-fraction words. This step uses no enumeration. -/

namespace VV.Problem4
open Hurwitz

def RootedWord (ℓ : ℕ) :=
  {w : List ℤ // ∃ x, CycleModel x w ∧ (∀ a ∈ w, 1 ≤ a) ∧ w.length = ℓ ∧
    ExactEventualPeriod x ℓ ∧ HasTripleRepresentative x ∧ HasGoodPair x}

structure RootedCycle (ℓ : ℕ) where
  x : ℝ
  w : List ℤ
  model : CycleModel x w
  positive : ∀ a ∈ w, 1 ≤ a
  length : w.length = ℓ
  least : ExactEventualPeriod x ℓ
  triple : HasTripleRepresentative x
  good : HasGoodPair x

def RootedCycle.toWord {ℓ : ℕ} (r : RootedCycle ℓ) : RootedWord ℓ :=
  ⟨r.w,r.x,r.model,r.positive,r.length,r.least,r.triple,r.good⟩

theorem RootedCycle.period {ℓ : ℕ} (r : RootedCycle ℓ) : DigitPeriod r.x ℓ := by
  simpa only [r.length] using r.model.digitPeriod r.positive

theorem RootedCycle.block {ℓ : ℕ} (r : RootedCycle ℓ) :
    P5Period.digitBlock r.x 0 ℓ = r.w := by
  simpa only [r.length] using r.model.digitBlock r.positive

theorem period_digit_mod {x : ℝ} {p : ℕ} (h : DigitPeriod x p) (n : ℕ) :
    partialQuotient x n = partialQuotient x (n%p) := by
  have he := nat_period_mul h (n%p) (n/p)
  simpa only [Nat.mod_add_div] using he

theorem RootedCycle.real_eq_of_word_eq {ℓ : ℕ} (r s : RootedCycle ℓ)
    (h : r.w = s.w) : r.x = s.x := by
  have he : P5Period.digitBlock r.x 0 ℓ = P5Period.digitBlock s.x 0 ℓ := by
    exact r.block.trans (h.trans s.block.symm)
  rw [P5Period.digitBlock_eq_ofFn,P5Period.digitBlock_eq_ofFn] at he
  have hf := List.ofFn_injective he
  apply CylinderGeometry.eq_of_all_partialQuotients_eq r.model.irrational s.model.irrational
  intro n
  rw [period_digit_mod r.period n,period_digit_mod s.period n]
  simpa only [Nat.zero_add] using congrFun hf ⟨n%ℓ,Nat.mod_lt _ r.least.1⟩

noncomputable def RootedCycle.rotate {ℓ : ℕ} (r : RootedCycle ℓ) (k : ℕ) : RootedCycle ℓ where
  x := completeQuotient r.x k
  w := P5Period.digitBlock r.x k ℓ
  model := by
    have hc : completeQuotient r.x (k+ℓ) = completeQuotient r.x k := by
      apply P5Period.completeQuotient_eq_of_periodic r.model.irrational
      intro n
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using r.period (k+n)
    refine ⟨completeQuotient_irrational r.model.irrational _, ?_, ?_, ?_, ?_⟩
    · cases k with
      | zero => exact r.model.positive
      | succ k => exact lt_trans zero_lt_one (one_lt_completeQuotient_succ r.model.irrational k)
    · intro a ha
      exact le_trans (by omega : (0:ℤ)≤1)
        (digitBlock_positive_of_gt_one r.model.irrational (r.model.gt_one r.positive) k ℓ a ha)
    · have he := value_actual_digitBlock r.model.irrational k ℓ
      rw [hc] at he
      exact he
    · rw [trace_digitBlock_shift_all r.period k,r.block]
      exact r.model.hyperbolic
  positive := digitBlock_positive_of_gt_one r.model.irrational (r.model.gt_one r.positive) k ℓ
  length := P5Period.digitBlock_length _ _ _
  least := (exactEventualPeriod_iff_of_tailEquivalent
    (tailEquivalent_completeQuotient r.x k) ℓ).mp r.least
  triple := by
    obtain ⟨y,hy,htr⟩ := r.triple
    exact ⟨y,(tailEquivalent_completeQuotient r.x k).symm.trans hy,htr⟩
  good := goodPair_completeQuotient r.model.irrational r.good k

theorem eventualPeriod_of_completeQuotient_eq {x : ℝ} {i j : ℕ} (hij : i < j)
    (h : completeQuotient x i = completeQuotient x j) : EventualPeriod x (j-i) := by
  refine ⟨i,fun n hn => ?_⟩
  have he := congrArg (fun y => partialQuotient y (n+1-i)) h
  simp only [partialQuotient,completeQuotient_add] at he
  have h₁ : i+(n+1-i)=n+1 := by omega
  have h₂ : j+(n+1-i)=n+(j-i)+1 := by omega
  rw [h₁,h₂] at he
  exact he.symm

theorem RootedCycle.rotate_injective {ℓ : ℕ} (r : RootedCycle ℓ) :
    Function.Injective (fun k : Fin ℓ => (r.rotate k).toWord) := by
  intro i j he
  have hword := congrArg Subtype.val he
  have hreal := (r.rotate i).real_eq_of_word_eq (r.rotate j) hword
  have hnot (i j : Fin ℓ) (hij : i.val < j.val)
      (he : completeQuotient r.x i = completeQuotient r.x j) : False := by
    exact r.least.2.2 (j.val-i.val) (by omega) (by omega)
      (eventualPeriod_of_completeQuotient_eq hij he)
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact False.elim (hnot i j h hreal)
  · exact h
  · exact False.elim (hnot j i h hreal.symm)

theorem exists_class_cycle {ℓ : ℕ} (q : Class ℓ) :
    ∃ r : RootedCycle ℓ, TailEquivalent q.out.val r.x := by
  obtain ⟨x,w,hx,hw,hl,hm,ht,hg⟩ := positive_cycle_of_representative q.out
  exact ⟨⟨x,w,hx,hw,hl,hm,⟨q.out.val,ht.symm,q.out.property.1⟩,hg⟩,ht⟩

noncomputable def classCycle {ℓ : ℕ} (q : Class ℓ) : RootedCycle ℓ :=
  Classical.choose (exists_class_cycle q)

theorem classCycle_tail {ℓ : ℕ} (q : Class ℓ) :
    TailEquivalent q.out.val (classCycle q).x := Classical.choose_spec (exists_class_cycle q)

noncomputable def rootedClassWord {ℓ : ℕ} (a : Class ℓ × Fin ℓ) : RootedWord ℓ :=
  ((classCycle a.1).rotate a.2).toWord

theorem rootedClassWord_injective (ℓ : ℕ) :
    Function.Injective (@rootedClassWord ℓ) := by
  rintro ⟨q,i⟩ ⟨p,j⟩ he
  have hw := congrArg Subtype.val he
  have hr := ((classCycle q).rotate i).real_eq_of_word_eq ((classCycle p).rotate j) hw
  change completeQuotient (classCycle q).x i = completeQuotient (classCycle p).x j at hr
  have ht : TailEquivalent q.out.val p.out.val :=
    (classCycle_tail q).trans ((tailEquivalent_completeQuotient _ i).trans
      (hr.symm ▸ (tailEquivalent_completeQuotient _ j).symm.trans (classCycle_tail p).symm))
  have hqp : q=p := by
    have hh := (toClass_eq_iff q.out p.out).mpr ht
    simpa only [toClass,Quotient.out_eq] using hh
  subst p
  have hij := (classCycle q).rotate_injective he
  change i=j at hij
  subst j
  rfl

theorem rootedEncoding_of_word_encoding {ℓ : ℕ}
    (h : ∃ encode : RootedWord ℓ → Template ℓ, Function.Injective encode) :
    HasRootedEncoding ℓ := by
  obtain ⟨encode,hinj⟩ := h
  exact ⟨encode ∘ rootedClassWord,hinj.comp (rootedClassWord_injective ℓ)⟩

end VV.Problem4
