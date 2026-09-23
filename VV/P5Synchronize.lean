import Mathlib.Tactic

/-!
Finite synchronization of a deterministic transducer with the two automata
reading its output words. All state spaces remain finite when the initial
state space is finite; the semantic lemmas do not perform any enumeration.
-/

namespace VV.P5Synchronize

abbrev Step (V A : Type) := V → A → Option (V × List A × List A)

def advance {V A : Type} (s : Step V A) (v : V) : List A → Option V
  | [] => some v
  | a :: w => (s v a).bind fun r => advance s r.1 w

def run {V A : Type} (s : Step V A) (v : V) : List A → Option (V × List A × List A)
  | [] => some (v, [], [])
  | a :: w => (s v a).bind fun r => (run s r.1 w).map fun t =>
      (t.1, r.2.1 ++ t.2.1, r.2.2 ++ t.2.2)

theorem advance_append {V A : Type} (s : Step V A) (v : V) (u w : List A) :
    advance s v (u ++ w) = (advance s v u).bind (fun t => advance s t w) := by
  induction u generalizing v with
  | nil => simp [advance]
  | cons a u ih => simp [advance, ih, Option.bind_assoc]

theorem run_append {V A : Type} (s : Step V A) (v : V) (u w : List A) :
    run s v (u ++ w) = (run s v u).bind (fun r =>
      (run s r.1 w).map fun t => (t.1, r.2.1 ++ t.2.1, r.2.2 ++ t.2.2)) := by
  induction u generalizing v with
  | nil => simp [run]
  | cons a u ih =>
    cases hs : s v a with
    | none => simp [run, hs]
    | some z =>
      rcases z with ⟨v', l, r⟩
      cases ht : run s v' u with
      | none => simp [run, hs, ih, ht]
      | some z =>
        rcases z with ⟨v'', l', r'⟩
        cases hh : run s v'' w <;> simp [run, hs, ih, ht, hh, List.append_assoc]

theorem advance_eq_run {V A : Type} (s : Step V A) (v : V) (w : List A) :
    advance s v w = (run s v w).map Prod.fst := by
  induction w generalizing v with
  | nil => rfl
  | cons a w ih =>
    cases hs : s v a with
    | none => simp [run, advance, hs]
    | some z =>
      cases ht : run s z.1 w <;> simp [run, advance, hs, ih, ht]

def lift {V A : Type} (s : Step V A) : Step (V × V × V) A := fun v a => do
  let r ← s v.1 a
  let left ← advance s v.2.1 r.2.1
  let right ← advance s v.2.2 r.2.2
  return ((r.1, left, right), r.2.1, r.2.2)

/-- Exact finite-word synchronization: the lifted machine succeeds precisely
when the original machine and both machines reading its accumulated outputs
succeed. This theorem includes every output-length alignment. -/
theorem run_lift {V A : Type} (s : Step V A) (v l r : V) (w : List A) :
    run (lift s) (v,l,r) w = (run s v w).bind (fun t => do
      let left ← advance s l t.2.1
      let right ← advance s r t.2.2
      return ((t.1, left, right), t.2.1, t.2.2)) := by
  induction w generalizing v l r with
  | nil => simp [run, advance]
  | cons a w ih =>
    cases hs : s v a with
    | none => simp [run, lift, hs]
    | some z =>
      rcases z with ⟨v', ls, rs⟩
      cases hl : advance s l ls <;> cases hr : advance s r rs <;>
        cases ht : run s v' w <;>
        simp [run, lift, hs, hl, hr, ih, ht, advance_append]

theorem advance_lift_of_runs {V A : Type} (s : Step V A)
    (v l r v' l' r' : V) (w ls rs : List A)
    (hin : run s v w = some (v',ls,rs))
    (hl : advance s l ls = some l') (hr : advance s r rs = some r') :
    advance (lift s) (v,l,r) w = some (v',l',r') := by
  rw [advance_eq_run, run_lift, hin]
  simp [hl, hr]

def StateAt (V : Type) : ℕ → Type _
  | 0 => V
  | n + 1 => StateAt V n × StateAt V n × StateAt V n

def iterate {V A : Type} (s : Step V A) : (n : ℕ) → Step (StateAt V n) A
  | 0 => s
  | n + 1 => lift (iterate s n)

instance stateAtFintype (V : Type) [Fintype V] (n : ℕ) : Fintype (StateAt V n) := by
  induction n with
  | zero => exact ‹Fintype V›
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (StateAt V n × StateAt V n × StateAt V n))

def inputBlock {A : Type} (input : ℕ → A) (start : ℕ) : ℕ → List A
  | 0 => []
  | n + 1 => input start :: inputBlock input (start + 1) n

/-- A trace records actual states at every input position. -/
def Trace {V A : Type} (s : Step V A) (input : ℕ → A)
    (state : ℕ → V) (left right : ℕ → List A) : Prop :=
  ∀ n, s (state n) (input n) = some (state (n + 1), left n, right n)

theorem advance_inputBlock_of_trace {V A : Type} (s : Step V A)
    (input : ℕ → A) (state : ℕ → V) (left right : ℕ → List A)
    (h : Trace s input state left right) (start n : ℕ) :
    advance s (state start) (inputBlock input start n) = some (state (start + n)) := by
  induction n generalizing start with
  | zero => simp [inputBlock, advance]
  | succ n ih =>
    simp only [inputBlock, advance, h start, Option.bind_some]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (start + 1)

/-- Infinite synchronization samples each output machine at the cumulative
length of the corresponding output. The cumulative lengths need not coincide,
and individual steps may emit no letters. -/
theorem trace_lift {V A : Type} (s : Step V A)
    (input leftInput rightInput : ℕ → A)
    (state leftState rightState : ℕ → V)
    (left right ll lr rl rr : ℕ → List A)
    (h : Trace s input state left right)
    (hl : Trace s leftInput leftState ll lr)
    (hr : Trace s rightInput rightState rl rr)
    (L R : ℕ → ℕ)
    (hL : ∀ n, L (n + 1) = L n + (left n).length)
    (hR : ∀ n, R (n + 1) = R n + (right n).length)
    (hleft : ∀ n, left n = inputBlock leftInput (L n) (left n).length)
    (hright : ∀ n, right n = inputBlock rightInput (R n) (right n).length) :
    Trace (lift s) input (fun n => (state n,leftState (L n),rightState (R n)))
      left right := by
  intro n
  have hlrun : advance s (leftState (L n)) (left n) = some (leftState (L (n + 1))) := by
    conv_lhs => rw [hleft n]
    rw [advance_inputBlock_of_trace s leftInput leftState ll lr hl, ← hL n]
  have hrrun : advance s (rightState (R n)) (right n) = some (rightState (R (n + 1))) := by
    conv_lhs => rw [hright n]
    rw [advance_inputBlock_of_trace s rightInput rightState rl rr hr, ← hR n]
  simp [lift, h n, hlrun, hrrun]

end VV.P5Synchronize

