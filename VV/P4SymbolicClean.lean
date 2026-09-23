import VV.P4Symbolic

namespace VV.P4Symbolic
open Hurwitz

theorem cyclic_split {α : Type*} (w : List α) (z : α) (hz : z ∈ w) (hlen : 3 ≤ w.length) :
    ∃ u v p q a b, w=u++v ∧ v++u=p++[a,z,b]++q := by
  obtain ⟨l,r,hw⟩ := List.mem_iff_append.mp hz
  subst w
  cases l with
  | nil =>
      cases r with
      | nil => simp at hlen
      | cons b r =>
          have hr : r ≠ [] := by intro he; simp [he] at hlen
          obtain ⟨p,a,hp⟩ := exists_append_singleton r hr
          exact ⟨[z,b],r,p,[],a,b,by simp,by simp [hp,List.append_assoc]⟩
  | cons z' l =>
      cases r with
      | nil =>
          have hl : l ≠ [] := by intro he; simp [he] at hlen
          obtain ⟨p,a,hp⟩ := exists_append_singleton l hl
          exact ⟨[z'],l++[z],p,[],a,z',by simp,by simp [hp,List.append_assoc]⟩
      | cons b r =>
          obtain ⟨p,a,hp⟩ := exists_append_singleton (z'::l) (by simp)
          exact ⟨[],(z'::l)++z::b::r,p,r,a,b,by simp,by simp [hp,List.append_assoc]⟩

inductive Reduction {n : ℕ} : List (Expr n) → List (Expr n) → Prop where
  | refl (w) : Reduction w w
  | step (u v p q : List (Expr n)) (a z b : Expr n)
      (he : v++u=p++[a,z,b]++q) (hz : z.base=0) (hv : Valid z) :
      Reduction (u++v) (p++[add a b]++q)
  | trans {u v w} : Reduction u v → Reduction v w → Reduction u w

theorem Reduction.valid {n : ℕ} {w v : List (Expr n)} (h : Reduction w v)
    (hw : ∀ e ∈ w, Valid e) : ∀ e ∈ v, Valid e := by
  induction h with
  | refl => exact hw
  | step u v p q a z b he hz hv =>
      have hr : ∀ e ∈ p++[a,z,b]++q, Valid e := by
        intro e hh
        rw [← he] at hh
        apply hw
        simpa only [List.mem_append,or_comm] using hh
      intro e hh
      simp only [List.mem_append,List.mem_singleton] at hh
      rcases hh with (hh|rfl)|hh
      · exact hr e (by simp [hh])
      · exact (hr a (by simp)).add (hr b (by simp))
      · exact hr e (by simp [hh])
  | trans h₁ h₂ ih₁ ih₂ => exact ih₂ (ih₁ hw)

theorem Reduction.length_le {n : ℕ} {w v : List (Expr n)} (h : Reduction w v) :
    v.length ≤ w.length := by
  induction h with
  | refl => exact le_rfl
  | step u v p q a z b he hz hv =>
      have hh := congrArg List.length he
      simp only [List.length_append,List.length_cons,List.length_nil] at *
      omega
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

theorem exists_reduction {n : ℕ} (w : List (Expr n)) (hw : ∀ e ∈ w, Valid e) :
    ∃ v, Reduction w v ∧ ((∀ e ∈ v, e.base ≠ 0) ∨ v.length<3) := by
  suffices aux : ∀ k, ∀ w : List (Expr n), w.length=k → (∀ e ∈ w, Valid e) →
      ∃ v, Reduction w v ∧ ((∀ e ∈ v,e.base≠0) ∨ v.length<3) from aux w.length w rfl hw
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro w hk hw
      by_cases hz : ∃ z ∈ w, z.base=0
      · by_cases hlen : 3 ≤ w.length
        · obtain ⟨z,hzw,hz⟩ := hz
          obtain ⟨u,v,p,q,a,b,huv,hpq⟩ := cyclic_split w z hzw hlen
          have hs : Reduction w (p++[add a b]++q) := by
            rw [huv]
            exact Reduction.step u v p q a z b hpq hz (hw z hzw)
          have hshort : (p++[add a b]++q).length < k := by
            have hh := congrArg List.length hpq
            have hh' := congrArg List.length huv
            simp only [List.length_append,List.length_cons,List.length_nil] at *
            omega
          obtain ⟨r,hr,hstop⟩ := ih _ hshort _ rfl (hs.valid hw)
          exact ⟨r,hs.trans hr,hstop⟩
        · exact ⟨w,Reduction.refl w,Or.inr (by omega)⟩
      · exact ⟨w,Reduction.refl w,Or.inl (by simpa using hz)⟩

noncomputable def normalize {n : ℕ} (w : List (Expr n)) (hw : ∀ e ∈ w, Valid e) : List (Expr n) :=
  Classical.choose (exists_reduction w hw)

theorem normalize_spec {n : ℕ} (w : List (Expr n)) (hw : ∀ e ∈ w, Valid e) :
    Reduction w (normalize w hw) ∧
      ((∀ e ∈ normalize w hw,e.base≠0) ∨ (normalize w hw).length<3) :=
  Classical.choose_spec (exists_reduction w hw)

theorem Reduction.model {n : ℕ} {w v : List (Expr n)} (h : Reduction w v)
    (hw : ∀ e ∈ w, Valid e) {u : Fin n → ℤ} (hu : ∀ i, 0 ≤ u i)
    {x : ℝ} (hx : CycleModel x (w.map (fun e => eval e u))) :
    ∃ y, CycleModel y (v.map (fun e => eval e u)) ∧ TailEquivalent x y ∧
      trace (word (v.map (fun e => eval e u))) = trace (word (w.map (fun e => eval e u))) := by
  induction h generalizing x with
  | refl => exact ⟨x,hx,TailEquivalent.refl x,rfl⟩
  | step p q a b e z f he hz hv =>
      have hz0 : eval z u=0 := (hv.eval_zero_iff hu).mpr hz
      have hrot : CycleModel (value (q.map (fun e => eval e u)) x)
          ((q++p).map (fun e => eval e u)) := by
        simpa only [List.map_append] using
          (show CycleModel x (p.map (fun e => eval e u) ++ q.map (fun e => eval e u)) from
            by simpa only [List.map_append] using hx).rotate
      have heval : (q++p).map (fun e => eval e u) =
          a.map (fun e => eval e u) ++ [eval e u,0,eval f u] ++ b.map (fun e => eval e u) := by
        rw [he]
        simp only [List.map_append,List.map_cons,List.map_nil,hz0]
      rw [heval] at hrot
      have hclean := hrot.clean
      refine ⟨value (q.map (fun e => eval e u)) x, ?_,
        value_tailEquivalent _ hx.irrational, ?_⟩
      · simpa only [List.map_append,List.map_cons,List.map_nil,eval_add] using hclean
      · simp only [List.map_append,List.map_cons,List.map_nil,eval_add]
        rw [← zero_cleanup_context]
        rw [← heval,List.map_append]
        exact trace_word_rotate _ _
  | trans h₁ h₂ ih₁ ih₂ =>
      obtain ⟨y,hy,hxy,htr₁⟩ := ih₁ hw hx
      obtain ⟨z,hz,hyz,htr₂⟩ := ih₂ (h₁.valid hw) hy
      exact ⟨z,hz,hxy.trans hyz,htr₂.trans htr₁⟩

theorem normalize_model {n : ℕ} (w : List (Expr n)) (hw : ∀ e ∈ w, Valid e)
    {u : Fin n → ℤ} (hu : ∀ i, 0 ≤ u i) {x : ℝ}
    (hx : CycleModel x (w.map (fun e => eval e u))) :
    ∃ y, CycleModel y ((normalize w hw).map (fun e => eval e u)) ∧
      (∀ a ∈ (normalize w hw).map (fun e => eval e u), 1 ≤ a) ∧ TailEquivalent x y ∧
      trace (word ((normalize w hw).map (fun e => eval e u))) =
        trace (word (w.map (fun e => eval e u))) := by
  obtain ⟨hr,hstop⟩ := normalize_spec w hw
  obtain ⟨y,hy,hxy,htr⟩ := hr.model hw hu hx
  refine ⟨y,hy,?_,hxy,htr⟩
  intro a ha
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
  have hevalid := hr.valid hw e he
  have he0 := hevalid.eval_nonnegative hu
  have hne : eval e u ≠ 0 := by
    intro heq
    rcases hstop with hstop|hstop
    · exact hstop e he ((hevalid.eval_zero_iff hu).mp heq)
    · have hzero : (0:ℤ) ∈ (normalize w hw).map (fun e => eval e u) := by
        exact List.mem_map.mpr ⟨e,he,heq⟩
      have hh := hy.length_three_of_zero hzero
      simp only [List.length_map] at hh
      omega
  omega

end VV.P4Symbolic
