import VV.P4ColumnOwner
import VV.P4Alignment
import Mathlib.Data.List.FinRange

namespace VV.P4Symbolic
open Hurwitz
open scoped BigOperators

noncomputable def output {n : ℕ} (types : Fin n → Fin 4) (s : State) : List (Expr n) :=
  normalize (runExpr types s (List.finRange n)) (runExpr_valid types s (List.finRange n))

theorem output_reduction {n : ℕ} (types : Fin n → Fin 4) (s : State) :
    Reduction (runExpr types s (List.finRange n)) (output types s) :=
  (normalize_spec _ _).1

theorem output_valid {n : ℕ} (types : Fin n → Fin 4) (s : State) :
    ∀ e ∈ output types s,Valid e :=
  (output_reduction types s).valid (runExpr_valid types s (List.finRange n))

def branchColumn {n : ℕ} (types : Fin n → Fin 4) (s : State) (i : Fin n) : ℤ :=
  column (runExpr types s (List.finRange n)) i

def branchDouble {n : ℕ} (types : Fin n → Fin 4) (s : State) (i : Fin n) : Bool :=
  decide (branchColumn types s i=4)

theorem branchColumn_nonnegative {n : ℕ} (types : Fin n → Fin 4) (s : State) (i : Fin n) :
    0≤branchColumn types s i := by
  by_cases h : large (types i)=true
  · rcases runExpr_column_large types s (List.finRange n) (List.nodup_finRange n) i
      (List.mem_finRange i) h with h|h <;> dsimp [branchColumn] <;> omega
  · have he : large (types i)=false := Bool.eq_false_iff.mpr h
    rw [branchColumn,runExpr_column_small types s (List.finRange n) i he]

theorem output_owners {n : ℕ} (hn : 0<n) (types : Fin n → Fin 4) (s : State)
    (E : Fin n → Expr n) (hE : List.ofFn E=output types s) :
    ∃ owner : Fin n → Fin n, ∀ j i,(E j).coeff i =
      if j=owner i then branchColumn types s i else 0 := by
  have hevalid : ∀ j,Valid (E j) := by
    intro j
    apply output_valid types s (E j)
    rw [← hE]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  have hsum (i : Fin n) : ∑ j,(E j).coeff i=branchColumn types s i := by
    rw [← column_ofFn,hE]
    exact (output_reduction types s).column_eq i
  have hdiv (i j : Fin n) : branchColumn types s i ∣ (E j).coeff i := by
    apply (output_reduction types s).divides i (branchColumn types s i)
      (runExpr_column_divides types s (List.finRange n) (List.nodup_finRange n) i) (E j)
    rw [← hE]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  have hh (i : Fin n) := owner_of_column hn E hevalid i (branchColumn types s i)
    (branchColumn_nonnegative types s i) (hdiv i) (hsum i)
  choose owner howner using hh
  exact ⟨owner,fun j i => howner i j⟩

theorem branchColumn_scale {n : ℕ} (types : Fin n → Fin 4) (s : State)
    (u v : Fin n → ℤ) (i : Fin n) :
    (branchColumn types s i:ℝ)*((u i:ℝ)-v i) =
      Problem4.scale (branchDouble types s i)*
        (if large (types i) then 2*((u i:ℝ)-v i) else 0) := by
  by_cases hl : large (types i)=true
  · rcases runExpr_column_large types s (List.finRange n) (List.nodup_finRange n) i
      (List.mem_finRange i) hl with h|h <;>
      change branchColumn types s i=_ at h <;>
      simp [branchDouble,h,Problem4.scale,hl] <;> ring
  · have he : large (types i)=false := Bool.eq_false_iff.mpr hl
    have h := runExpr_column_small types s (List.finRange n) i he
    change branchColumn types s i=0 at h
    simp [h,hl]

/-- Each fixed four-type template, pair of states, and pair of alignments
has at most one actual input digit vector. All coefficient hypotheses have
been derived from the literal Hurwitz machine and its symbolic zero removal. -/
theorem normalized_pair_unique {n : ℕ} (hn : 0<n) (types : Fin n → Fin 4)
    (s t : State) (hst : s≠t) (u v : Fin n → ℤ)
    (E F : Fin n → Expr n) (hE : List.ofFn E=output types s) (hF : List.ofFn F=output types t)
    (σ τ : Equiv.Perm (Fin n))
    (huE : ∀ j,eval (E j) u=inputDigit (types (σ j)) (u (σ j)))
    (hvE : ∀ j,eval (E j) v=inputDigit (types (σ j)) (v (σ j)))
    (huF : ∀ j,eval (F j) u=inputDigit (types (τ j)) (u (τ j)))
    (hvF : ∀ j,eval (F j) v=inputDigit (types (τ j)) (v (τ j))) :
    ∀ i,inputDigit (types i) (u i)=inputDigit (types i) (v i) := by
  obtain ⟨ownerE,hoE⟩ := output_owners hn types s E hE
  obtain ⟨ownerF,hoF⟩ := output_owners hn types t F hF
  apply affine_pair_unique types u v E F σ τ ownerE ownerF
    (branchColumn types s) (branchColumn types t) (branchDouble types s) (branchDouble types t)
    hoE hoF (branchColumn_scale types s u v) (branchColumn_scale types t u v)
    _ huE hvE huF hvF
  intro i
  simpa only [branchDouble,decide_eq_true_eq,branchColumn] using
    runExpr_not_both_four types s t hst (List.finRange n) (List.nodup_finRange n) i

theorem output_model {n : ℕ} (types : Fin n → Fin 4) (s : State) (u : Fin n → ℤ)
    (hu : ∀ i,0≤u i) {x : ℝ}
    (hx : CycleModel x (inputWord types u (List.finRange n)))
    (hmin : Problem4.ExactEventualPeriod x n) (hn : 2≤n)
    (hclass : HasTripleRepresentative x) (hgood : TailEquivalent x (P5RealCursor.stateValue s x)) :
    ∃ y, CycleModel y ((output types s).map (fun e => eval e u)) ∧
      (∀ a ∈ (output types s).map (fun e => eval e u),1≤a) ∧
      (output types s).length=n ∧ TailEquivalent x y ∧
      trace (word ((output types s).map (fun e => eval e u))) =
        trace (word (inputWord types u (List.finRange n))) := by
  have hw : ∀ a ∈ inputWord types u (List.finRange n),1≤a := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    exact inputDigit_positive (types i) (hu i)
  have hc := hx.all_states_closed hclass s
  have hr := hx.outputModel hw s hc
  rw [← runExpr_eval types u s (List.finRange n)] at hr
  obtain ⟨y,hy,hv,hxy,htr⟩ := normalize_model (runExpr types s (List.finRange n))
    (runExpr_valid types s (List.finRange n)) hu hr
  change CycleModel y ((output types s).map (fun e => eval e u)) at hy
  have hxy' := hgood.trans hxy
  have htr' : trace (word ((output types s).map (fun e => eval e u))) =
      trace (word (inputWord types u (List.finRange n))) := by
    change trace (word ((output types s).map (fun e => eval e u))) = _ at htr
    rw [runExpr_eval] at htr
    have hm := run_matrix s (inputWord types u (List.finRange n))
    rw [hc] at hm
    exact htr.trans (trace_similar (by rw [stateMatrix_det]; decide) hm).symm
  have hlen : (inputWord types u (List.finRange n)).length=n := by simp [inputWord]
  have hl := equal_length_of_cycle_trace hx hy hw hv (hlen.symm ▸ hmin)
    (by omega) hxy' htr'
  simp only [List.length_map] at hl
  exact ⟨y,hy,hv,by omega,hxy',htr'⟩

end VV.P4Symbolic
