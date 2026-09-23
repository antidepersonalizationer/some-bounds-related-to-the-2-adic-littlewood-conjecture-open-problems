import VV.P4Output
import VV.P4Kernel
import Mathlib.Data.List.OfFn

/-! Four-type symbolic Hurwitz words. Coefficients are retained throughout
zero removal, so that the uniqueness argument concerns the actual machine. -/

namespace VV.P4Symbolic
open Hurwitz
open scoped BigOperators

structure Expr (n : ℕ) where
  base : ℤ
  coeff : Fin n → ℤ

def const {n : ℕ} (a : ℤ) : Expr n := ⟨a, fun _ => 0⟩
def atom {n : ℕ} (a c : ℤ) (i : Fin n) : Expr n :=
  ⟨a, fun j => if j=i then c else 0⟩
def add {n : ℕ} (a b : Expr n) : Expr n :=
  ⟨a.base+b.base, fun i => a.coeff i+b.coeff i⟩
def eval {n : ℕ} (e : Expr n) (u : Fin n → ℤ) : ℤ :=
  e.base + ∑ i, e.coeff i * u i

@[simp] theorem eval_const {n : ℕ} (a : ℤ) (u : Fin n → ℤ) : eval (const a) u = a := by
  simp [eval,const]
@[simp] theorem eval_atom {n : ℕ} (a c : ℤ) (i : Fin n) (u : Fin n → ℤ) :
    eval (atom a c i) u = a+c*u i := by
  simp [eval,atom,ite_mul]
@[simp] theorem eval_add {n : ℕ} (a b : Expr n) (u : Fin n → ℤ) :
    eval (add a b) u = eval a u+eval b u := by
  simp only [eval,add,add_mul,Finset.sum_add_distrib]
  ring

def Valid {n : ℕ} (e : Expr n) : Prop :=
  0 ≤ e.base ∧ (∀ i, 0 ≤ e.coeff i) ∧ (e.base=0 → ∀ i,e.coeff i=0)

theorem Valid.add {n : ℕ} {a b : Expr n} (ha : Valid a) (hb : Valid b) : Valid (add a b) := by
  refine ⟨add_nonneg ha.1 hb.1, fun i => add_nonneg (ha.2.1 i) (hb.2.1 i), ?_⟩
  intro he i
  have ha0 := ha.1
  have hb0 := hb.1
  have hae : a.base=0 := by change a.base+b.base=0 at he; omega
  have hbe : b.base=0 := by change a.base+b.base=0 at he; omega
  change a.coeff i+b.coeff i=0
  rw [ha.2.2 hae i,hb.2.2 hbe i,add_zero]

theorem Valid.eval_nonnegative {n : ℕ} {e : Expr n} (h : Valid e)
    {u : Fin n → ℤ} (hu : ∀ i, 0 ≤ u i) : 0 ≤ eval e u :=
  add_nonneg h.1 (Finset.sum_nonneg fun i _ => mul_nonneg (h.2.1 i) (hu i))

theorem Valid.eval_zero_iff {n : ℕ} {e : Expr n} (h : Valid e)
    {u : Fin n → ℤ} (hu : ∀ i, 0 ≤ u i) : eval e u = 0 ↔ e.base=0 := by
  constructor
  · intro he
    have he0 := h.1
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_nonneg (h.2.1 i) (hu i))
    dsimp [eval] at he
    omega
  · intro he
    simp [eval,he,h.2.2 he]

def typeBase (t : Fin 4) : ℤ := t.val+1
def large (t : Fin 4) : Bool := decide (2 ≤ t.val)
def inputDigit (t : Fin 4) (u : ℤ) : ℤ := typeBase t + if large t then 2*u else 0

theorem inputDigit_positive (t : Fin 4) {u : ℤ} (hu : 0 ≤ u) : 1 ≤ inputDigit t u := by
  have ht := t.isLt
  dsimp [inputDigit,typeBase,large]
  split_ifs <;> omega

theorem inputDigit_mod_two (t : Fin 4) (u : ℤ) : inputDigit t u % 2 = typeBase t % 2 := by
  dsimp [inputDigit]
  split_ifs <;> omega

def sourceExpr {n : ℕ} (t : Fin 4) (i : Fin n) (a c : ℤ) : Expr n :=
  if large t then atom a c i else const a

def emitExpr {n : ℕ} (s : State) (t : Fin 4) (i : Fin n) : List (Expr n) :=
  match s with
  | .D => [sourceExpr t i (2*typeBase t) 4]
  | .H0 => if typeBase t % 2=0 then [sourceExpr t i (typeBase t/2) 1]
      else [sourceExpr t i (typeBase t/2) 1,const 1,const 1]
  | .H1 => if typeBase t % 2=0 then [sourceExpr t i (typeBase t/2-1) 1,const 1,const 1]
      else [sourceExpr t i (typeBase t/2) 1]

theorem sourceExpr_eval {n : ℕ} (t : Fin 4) (i : Fin n) (a c : ℤ) (u : Fin n → ℤ) :
    eval (sourceExpr t i a c) u = a + if large t then c*u i else 0 := by
  simp only [sourceExpr]
  split <;> simp_all

theorem emitExpr_eval {n : ℕ} (s : State) (t : Fin 4) (i : Fin n) (u : Fin n → ℤ) :
    (emitExpr s t i).map (fun e => eval e u) = emit s (inputDigit t (u i)) := by
  have hm := inputDigit_mod_two t (u i)
  have he : inputDigit t (u i) / 2 = typeBase t/2 + if large t then u i else 0 := by
    dsimp [inputDigit]
    split_ifs <;> omega
  cases s <;> simp only [emitExpr,emit,hm,List.map_cons,List.map_nil,sourceExpr_eval,eval_const]
  · simp only [inputDigit]
    split_ifs <;> simp <;> ring
  · split_ifs <;> simp [he,sourceExpr_eval]
  · split_ifs <;> simp [he,sourceExpr_eval] <;> ring

theorem emitExpr_valid {n : ℕ} (s : State) (t : Fin 4) (i : Fin n) :
    ∀ e ∈ emitExpr s t i, Valid e := by
  fin_cases t <;> cases s <;>
    simp [emitExpr,sourceExpr,typeBase,large,Valid,atom,const] <;>
    intro j <;> split_ifs <;> norm_num

def runExpr {n : ℕ} (types : Fin n → Fin 4) (s : State) : List (Fin n) → List (Expr n)
  | [] => []
  | i::is => emitExpr s (types i) i ++ runExpr types (next s (typeBase (types i))) is

def inputWord {n : ℕ} (types : Fin n → Fin 4) (u : Fin n → ℤ) (is : List (Fin n)) : List ℤ :=
  is.map (fun i => inputDigit (types i) (u i))

theorem runExpr_eval {n : ℕ} (types : Fin n → Fin 4) (u : Fin n → ℤ)
    (s : State) (is : List (Fin n)) :
    (runExpr types s is).map (fun e => eval e u) = (run s (inputWord types u is)).1 := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
      have hn : next s (inputDigit (types i) (u i)) = next s (typeBase (types i)) := by
        cases s <;> simp only [next,inputDigit_mod_two]
      simp only [runExpr,List.map_append,emitExpr_eval,ih,inputWord,List.map_cons,run,hn]

theorem runExpr_valid {n : ℕ} (types : Fin n → Fin 4) (s : State) (is : List (Fin n)) :
    ∀ e ∈ runExpr types s is, Valid e := by
  induction is generalizing s with
  | nil => simp [runExpr]
  | cons i is ih =>
      intro e he
      simp only [runExpr,List.mem_append] at he
      exact he.elim (emitExpr_valid s (types i) i e) (ih _ e)

end VV.P4Symbolic
