import VV.P4SymbolicClean

namespace VV.P4Symbolic
open Hurwitz

def column {n : ℕ} (w : List (Expr n)) (i : Fin n) : ℤ := (w.map (fun e => e.coeff i)).sum
def sourceScale (s : State) : ℤ := if s=.D then 4 else 1

@[simp] theorem column_append {n : ℕ} (w v : List (Expr n)) (i : Fin n) :
    column (w++v) i=column w i+column v i := by simp [column]

theorem emitExpr_column {n : ℕ} (s : State) (t : Fin 4) (j i : Fin n) :
    column (emitExpr s t j) i = if i=j ∧ large t then sourceScale s else 0 := by
  cases s <;> by_cases he : typeBase t % 2=0 <;>
    by_cases hl : large t=true <;> by_cases hi : i=j <;>
    simp [emitExpr,he,sourceExpr,hl,column,atom,const,hi,sourceScale]

theorem emitExpr_coeff {n : ℕ} (s : State) (t : Fin 4) (j i : Fin n)
    (e : Expr n) (he : e ∈ emitExpr s t j) :
    e.coeff i=0 ∨ e.coeff i=(if i=j ∧ large t then sourceScale s else 0) := by
  cases s <;> by_cases ht : typeBase t % 2=0 <;>
    simp only [emitExpr,ht,if_true,if_false,List.mem_cons,List.not_mem_nil,or_false] at he <;>
    rcases he with rfl | rfl | rfl <;>
    by_cases hl : large t=true <;> by_cases hi : i=j <;>
    simp [sourceExpr,hl,atom,const,hi,sourceScale]

theorem runExpr_coeff_zero_of_not_mem {n : ℕ} (types : Fin n → Fin 4)
    (s : State) (is : List (Fin n)) (i : Fin n) (hi : i ∉ is) :
    ∀ e ∈ runExpr types s is, e.coeff i=0 := by
  induction is generalizing s with
  | nil => simp [runExpr]
  | cons j is ih =>
      intro e he
      simp only [runExpr,List.mem_append] at he
      rcases he with he|he
      · have hij : i≠j := by intro h; subst j; exact hi (by simp)
        rcases emitExpr_coeff s (types j) j i e he with h|h
        · exact h
        · simpa [hij] using h
      · exact ih _ (by intro hh; exact hi (by simp [hh])) e he

theorem runExpr_column_zero_of_not_mem {n : ℕ} (types : Fin n → Fin 4)
    (s : State) (is : List (Fin n)) (i : Fin n) (hi : i ∉ is) :
    column (runExpr types s is) i=0 := by
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
  exact runExpr_coeff_zero_of_not_mem types s is i hi e he

theorem runExpr_column_small {n : ℕ} (types : Fin n → Fin 4)
    (s : State) (is : List (Fin n)) (i : Fin n) (hi : large (types i)=false) :
    column (runExpr types s is) i=0 := by
  induction is generalizing s with
  | nil => rfl
  | cons j is ih =>
      rw [runExpr,column_append,ih,add_zero,emitExpr_column]
      by_cases hij : i=j
      · subst j; simp [hi]
      · simp [hij]

theorem runExpr_column_large {n : ℕ} (types : Fin n → Fin 4)
    (s : State) (is : List (Fin n)) (hn : is.Nodup) (i : Fin n)
    (hi : i ∈ is) (hl : large (types i)=true) :
    column (runExpr types s is) i=1 ∨ column (runExpr types s is) i=4 := by
  induction is generalizing s with
  | nil => simp at hi
  | cons j is ih =>
      have hnot := (List.nodup_cons.mp hn).1
      have hnod := (List.nodup_cons.mp hn).2
      rw [runExpr,column_append,emitExpr_column]
      by_cases hij : i=j
      · subst j
        rw [runExpr_column_zero_of_not_mem types _ is i hnot]
        simp only [hl, and_self,if_true,add_zero]
        cases s <;> simp [sourceScale]
      · simp only [hij,false_and,if_false,zero_add]
        exact ih _ hnod (List.mem_of_ne_of_mem hij hi)

theorem runExpr_column_divides {n : ℕ} (types : Fin n → Fin 4)
    (s : State) (is : List (Fin n)) (hn : is.Nodup) (i : Fin n) :
    ∀ e ∈ runExpr types s is, column (runExpr types s is) i ∣ e.coeff i := by
  induction is generalizing s with
  | nil => simp [runExpr]
  | cons j is ih =>
      have hnot := (List.nodup_cons.mp hn).1
      have hnod := (List.nodup_cons.mp hn).2
      intro e he
      rw [runExpr,column_append,emitExpr_column]
      simp only [runExpr,List.mem_append] at he
      by_cases hij : i=j
      · subst j
        rw [runExpr_column_zero_of_not_mem types _ is i hnot,add_zero]
        rcases he with he|he
        · rcases emitExpr_coeff s (types i) i i e he with h|h
          · rw [h]; exact dvd_zero _
          · rw [h]
        · rw [runExpr_coeff_zero_of_not_mem types _ is i hnot e he]
          exact dvd_zero _
      · simp only [hij,false_and,if_false,zero_add]
        rcases he with he|he
        · rcases emitExpr_coeff s (types j) j i e he with h|h
          · rw [h]; exact dvd_zero _
          · simp only [hij,false_and,if_false] at h
            rw [h]; exact dvd_zero _
        · exact ih _ hnod e he

theorem runExpr_not_both_four {n : ℕ} (types : Fin n → Fin 4)
    (s t : State) (hst : s≠t) (is : List (Fin n)) (hn : is.Nodup) (i : Fin n) :
    ¬(column (runExpr types s is) i=4 ∧ column (runExpr types t is) i=4) := by
  induction is generalizing s t with
  | nil => simp [runExpr,column]
  | cons j is ih =>
      have hnot := (List.nodup_cons.mp hn).1
      have hnod := (List.nodup_cons.mp hn).2
      simp only [runExpr,column_append,emitExpr_column]
      by_cases hij : i=j
      · subst j
        rw [runExpr_column_zero_of_not_mem types _ is i hnot,
          runExpr_column_zero_of_not_mem types _ is i hnot]
        by_cases hl : large (types i)=true
        · simp only [hl,and_self,if_true,add_zero]
          cases s <;> cases t <;> simp_all [sourceScale]
        · simp [hl]
      · simp only [hij,false_and,if_false,zero_add]
        exact ih _ _ (fun h => hst (next_injective _ h)) hnod

theorem Reduction.column_eq {n : ℕ} {w v : List (Expr n)} (h : Reduction w v) (i : Fin n) :
    column v i=column w i := by
  induction h with
  | refl => rfl
  | step u v p q a z b he hz hv =>
      have hh := congrArg (fun w => column w i) he
      have hz0 := hv.2.2 hz i
      simp only [column_append,column,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        add,hz0,List.map_append,List.sum_append] at *
      omega
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

theorem Reduction.divides {n : ℕ} {w v : List (Expr n)} (h : Reduction w v)
    (i : Fin n) (c : ℤ) (hw : ∀ e ∈ w,c ∣ e.coeff i) : ∀ e ∈ v,c ∣ e.coeff i := by
  induction h with
  | refl => exact hw
  | step u v p q a z b he hz hv =>
      have hr : ∀ e ∈ p++[a,z,b]++q,c ∣ e.coeff i := by
        intro e hh
        rw [← he] at hh
        apply hw
        simpa only [List.mem_append,or_comm] using hh
      intro e hh
      simp only [List.mem_append,List.mem_singleton] at hh
      rcases hh with (hh|rfl)|hh
      · exact hr e (by simp [hh])
      · exact dvd_add (hr a (by simp)) (hr b (by simp))
      · exact hr e (by simp [hh])
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hw)

end VV.P4Symbolic
