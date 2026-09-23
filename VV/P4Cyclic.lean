import VV.HurwitzValue
import VV.Classification

/-!
# Cyclic removal of zeros

A nonnegative matrix word of trace greater than two, with a positive irrational
fixed value, admits a positive cyclic representative. The construction strictly
shortens the word whenever a zero is removed. Its real continued-fraction tail
class and matrix trace are preserved, so it applies to Hurwitz output cycles.
-/

namespace VV.Hurwitz

def trace (M : Mat) : ℤ := M.a+M.d

theorem trace_mul_comm (M N : Mat) : trace (mul M N) = trace (mul N M) := by
  simp [trace, mul]; ring

theorem trace_word_rotate (u v : List ℤ) : trace (word (u++v)) = trace (word (v++u)) := by
  simp only [word_append, trace_mul_comm]

theorem trace_similar {R U V : Mat} (hR : det R ≠ 0) (h : mul R U = mul V R) :
    trace U = trace V := by
  have ha := congrArg Mat.a h
  have hb := congrArg Mat.b h
  have hc := congrArg Mat.c h
  have hd := congrArg Mat.d h
  have he : det R * (trace U-trace V) = 0 := by
    simp only [mul] at ha hb hc hd
    unfold trace det
    linear_combination R.d*ha-R.b*hc-R.c*hb+R.a*hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hR)

theorem value_eq_of_word_eq {u v : List ℤ} (h : word u = word v) {x : ℝ}
    (hx : Irrational x) : value u x = value v x := by
  have hu := value_matrix u hx
  have hv := value_matrix v hx
  have hden := Problem3.mobius_denominator_ne_zero (word_det_unit v) hv
  rw [h] at hu
  exact mul_right_cancel₀ hden (hu.trans hv.symm)

structure CycleModel (x : ℝ) (w : List ℤ) : Prop where
  irrational : Irrational x
  positive : 0 < x
  digits : ∀ a ∈ w, 0 ≤ a
  fixed : value w x = x
  hyperbolic : 2 < trace (word w)

theorem CycleModel.rotate {x : ℝ} {u v : List ℤ} (h : CycleModel x (u++v)) :
    CycleModel (value v x) (v++u) := by
  refine ⟨value_irrational v h.irrational,
    value_pos v h.positive (fun a ha => h.digits a (by simp [ha])), ?_, ?_, ?_⟩
  · intro a ha
    apply h.digits
    simpa only [List.mem_append, or_comm] using ha
  · rw [value_append]
    have hf := h.fixed
    rw [value_append] at hf
    rw [hf]
  · rw [← trace_word_rotate]
    exact h.hyperbolic

theorem CycleModel.clean {x : ℝ} {u v : List ℤ} {a b : ℤ}
    (h : CycleModel x (u++[a,0,b]++v)) : CycleModel x (u++[a+b]++v) := by
  refine ⟨h.irrational, h.positive, ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with (hc | rfl) | hc
    · exact h.digits c (by simp [hc])
    · exact add_nonneg (h.digits a (by simp)) (h.digits b (by simp))
    · exact h.digits c (by simp [hc])
  · rw [← value_eq_of_word_eq (zero_cleanup_context u v a b) h.irrational]
    exact h.fixed
  · rw [← zero_cleanup_context]
    exact h.hyperbolic

theorem exists_append_singleton {α : Type*} (w : List α) (hw : w ≠ []) :
    ∃ u a, w = u ++ [a] := by
  induction w with
  | nil => exact False.elim (hw rfl)
  | cons a w ih =>
      cases w with
      | nil => exact ⟨[], a, rfl⟩
      | cons b w =>
          obtain ⟨u,c,hc⟩ := ih (by simp)
          exact ⟨a::u,c,by simp [hc]⟩

/-- Any zero in a cyclic list of length at least three can be placed between
two digits by one cyclic cut. -/
theorem cyclic_zero_split (w : List ℤ) (hzero : 0 ∈ w) (hlen : 3 ≤ w.length) :
    ∃ u v p q a b,
      w = u++v ∧ v++u = p++[a,0,b]++q := by
  obtain ⟨l,r,hw⟩ := List.mem_iff_append.mp hzero
  subst w
  cases l with
  | nil =>
      cases r with
      | nil => simp at hlen
      | cons b r =>
          have hr : r ≠ [] := by intro he; simp [he] at hlen
          obtain ⟨p,a,hp⟩ := exists_append_singleton r hr
          refine ⟨[0,b],r,p,[],a,b,?_,?_⟩
          · simp
          · simp [hp, List.append_assoc]
  | cons z l =>
      cases r with
      | nil =>
          have hl : l ≠ [] := by intro he; simp [he] at hlen
          obtain ⟨p,a,hp⟩ := exists_append_singleton l hl
          refine ⟨[z],l++[0],p,[],a,z,?_,?_⟩
          · simp
          · simp [hp, List.append_assoc]
      | cons b r =>
          obtain ⟨p,a,hp⟩ := exists_append_singleton (z::l) (by simp)
          refine ⟨[],(z::l)++0::b::r,p,r,a,b,by simp,?_⟩
          simp [hp, List.append_assoc]

theorem CycleModel.length_three_of_zero {x : ℝ} {w : List ℤ}
    (h : CycleModel x w) (hz : 0 ∈ w) : 3 ≤ w.length := by
  by_contra hn
  cases w with
  | nil => simp at hz
  | cons a w =>
      cases w with
      | nil =>
          simp only [List.mem_singleton] at hz
          subst a
          simpa [word, mul, digit, one, trace] using h.hyperbolic
      | cons b w =>
          cases w with
          | cons c w => simp at hn
          | nil =>
              have hh := h.hyperbolic
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
              rcases hz with hz | hz <;> subst_vars <;>
                simp [word, mul, digit, one, trace] at hh

/-- A genuine normalization theorem for cyclic nonnegative continued-fraction
words. The resulting positive word is no longer than the input. -/
theorem CycleModel.normalize {x : ℝ} {w : List ℤ} (h : CycleModel x w) :
    ∃ y v, CycleModel y v ∧ (∀ a ∈ v, 1 ≤ a) ∧ v.length ≤ w.length ∧
      TailEquivalent x y ∧ trace (word v) = trace (word w) := by
  suffices aux : ∀ n : ℕ, ∀ {x : ℝ} {w : List ℤ}, w.length = n → CycleModel x w →
      ∃ y v, CycleModel y v ∧ (∀ a ∈ v, 1 ≤ a) ∧ v.length ≤ w.length ∧
        TailEquivalent x y ∧ trace (word v) = trace (word w) from aux w.length rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x w hn h
      by_cases hz : 0 ∈ w
      · obtain ⟨u,v,p,q,a,b,huv,hpq⟩ := cyclic_zero_split w hz (h.length_three_of_zero hz)
        have hrot : CycleModel (value v x) (v++u) := (huv ▸ h).rotate
        have hclean : CycleModel (value v x) (p++[a+b]++q) := (hpq ▸ hrot).clean
        have hlen : (p++[a+b]++q).length < n := by
          have := congrArg List.length hpq
          have := congrArg List.length huv
          simp only [List.length_append, List.length_cons, List.length_nil] at *
          omega
        obtain ⟨y,z,hy,hzpos,hzlen,hzy,htr⟩ := ih _ hlen rfl hclean
        refine ⟨y,z,hy,hzpos,?_,(value_tailEquivalent v h.irrational).trans hzy,?_⟩
        · have := congrArg List.length hpq
          have := congrArg List.length huv
          simp only [List.length_append, List.length_cons, List.length_nil] at *
          omega
        · calc
            trace (word z) = trace (word (p++[a+b]++q)) := htr
            _ = trace (word (p++[a,0,b]++q)) := by rw [zero_cleanup_context]
            _ = trace (word (v++u)) := by rw [hpq]
            _ = trace (word w) := by rw [huv, trace_word_rotate]
      · refine ⟨x,w,h,?_,le_rfl,TailEquivalent.refl x,rfl⟩
        intro a ha
        have hnonneg := h.digits a ha
        have hne : a ≠ 0 := by intro he; subst a; exact hz ha
        omega

end VV.Hurwitz
