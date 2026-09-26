import VV.P5SparseCertificate
import VV.P5StateSize
import VV.P5GeneralWindow

/-!
A fully kernel-checked SMALL certificate: C=2, depth zero.
The 144-entry table includes the 48 unused equal-state pairs. The 96
admissible states have height at most 3. Each successful transition
strictly lowers height. Only 192 state/input combinations are checked
with 'decide', never 'native_decide'. No depth-14 computation is used.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace VV.P5SmallCertificate
open Hurwitz P5Machine P5Synchronize P5MachineGraph P5Graph P5Window

def stateCode : State → ℕ
  | .D => 0
  | .H0 => 1
  | .H1 => 2

def cursorCode (c : BCursor 2) : ℕ :=
  (stateCode c.1 * 2 + c.2.1.val) * 2 + if c.2.2 then 1 else 0

def heightTable : List ℕ :=
  [0,0,0,0,3,3,0,3,1,1,1,1,
   0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,3,3,0,3,1,1,1,1,
   0,0,0,0,0,0,0,0,0,0,0,0,
   3,0,3,0,0,0,0,0,2,2,1,2,
   3,0,3,0,0,0,0,0,2,2,1,2,
   0,0,0,0,0,0,0,0,2,2,0,2,
   3,0,3,0,0,0,0,0,1,2,1,2,
   1,0,1,0,2,2,2,1,0,0,0,0,
   1,0,1,0,2,2,2,2,0,0,0,0,
   1,0,1,0,1,1,0,1,0,0,0,0,
   1,0,1,0,2,2,2,2,0,0,0,0]

def height (v : Pair 2) : ℕ :=
  heightTable.getD (cursorCode v.val.1 * 12 + cursorCode v.val.2) 0

def transitionCheck (v : Pair 2) (a : Fin 2) : Bool :=
  match step 2 v a with
  | none => true
  | some t => decide (height t.1 < height v)

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
theorem transition_check : ∀ (v : Pair 2) (a : Fin 2), transitionCheck v a = true := by
  decide

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000 in
theorem height_le_three : ∀ v : Pair 2, height v ≤ 3 := by decide

theorem transition_decreases (v : Pair 2) (a : Fin 2)
    (t : Pair 2 × List (Fin 2) × List (Fin 2)) (h : step 2 v a = some t) :
    height t.1 < height v := by
  have hc := transition_check v a
  simpa only [transitionCheck, h, decide_eq_true_eq] using hc

noncomputable def graphHeight (i : Fin (windowGraph 2 0).size) : ℕ :=
  height ((vertexEquiv (V := Pair 2) 2).symm i).1

theorem graphHeight_decreases (i j : Fin (windowGraph 2 0).size)
    (h : (windowGraph 2 0).edge i j = true) : graphHeight j < graphHeight i := by
  change decide (((step 2) ((vertexEquiv (V := Pair 2) 2).symm i).1 ((vertexEquiv (V := Pair 2) 2).symm i).2).map
    Prod.fst = some ((vertexEquiv (V := Pair 2) 2).symm j).1) = true at h
  have hm := of_decide_eq_true h
  cases hs : step 2 ((vertexEquiv (V := Pair 2) 2).symm i).1 ((vertexEquiv (V := Pair 2) 2).symm i).2 with
  | none => simp [hs] at hm
  | some t =>
    have heq : t.1 = ((vertexEquiv (V := Pair 2) 2).symm j).1 := by simpa [hs] using hm
    have hd := transition_decreases _ _ t hs
    simpa only [graphHeight, heq] using hd

theorem graph_size : (windowGraph 2 0).size = 192 := by
  rw [P5StateSize.windowGraph_size]
  norm_num

noncomputable def graphRank (i : Fin (windowGraph 2 0).size) :
    Fin ((windowGraph 2 0).size + 1) :=
  ⟨graphHeight i, by
    have h := height_le_three ((vertexEquiv (V := Pair 2) 2).symm i).1
    change graphHeight i ≤ 3 at h
    rw [graph_size]
    omega⟩

theorem graphRank_certificate : (windowGraph 2 0).RankCertificate graphRank := by
  refine ⟨?_, ?_⟩
  · intro v w hw
    exact Nat.le_of_lt (graphHeight_decreases v w hw)
  · intro v w z hw hz hrw hrz
    have hlt := graphHeight_decreases v w hw
    have heq := congrArg Fin.val hrw
    change graphHeight w = graphHeight v at heq
    omega

/-- This certifies the existing graph, including its original numbering. -/
theorem rank_check_two_zero :
    (windowGraph 2 0).checkEventuallyDeterministic = true :=
  decide_eq_true ⟨graphRank, graphRank_certificate⟩

/-- The actual sparse checker also accepts the certificate. -/
theorem sparse_check_two_zero :
    P5SparseCertificate.check (windowGraph 2 0)
      (P5SparseCertificate.machineSuccessors (vertexEquiv (V := Pair 2) 2) (step 2))
      graphRank
      (P5SparseCertificate.sameRankNext (windowGraph 2 0)
        (P5SparseCertificate.machineSuccessors (vertexEquiv (V := Pair 2) 2) (step 2))
        graphRank) = true :=
  P5SparseCertificate.check_complete _ _
    (P5SparseCertificate.machineSuccessors_exact (vertexEquiv (V := Pair 2) 2) (step 2)) _ graphRank_certificate

theorem not_all_three_eventualBound_two (x : ℝ) (hx : Irrational x) :
    ¬ (∀ k : ℕ, k ≤ 2 → EventualBound ((2 : ℝ) ^ k * x) 2) := by
  intro h
  obtain ⟨N,hN,path,hpath,_⟩ := windowGraph_realizes 2 0 hx (by simpa using h)
  have hd (n : ℕ) : graphHeight (path (n+1)) < graphHeight (path n) :=
    graphHeight_decreases _ _ (hpath n)
  obtain ⟨J,hJ⟩ := antitone_nat_eventually_constant
    (fun n => graphHeight (path n)) (fun n => (hd n).le)
  have hlt := hd J
  have heq := hJ 1
  omega

/-- A complete result with no admitted computation: at least one of
x, 2x, 4x has partial quotients at least 3 infinitely often. -/
theorem frequently_three_within_two (x : ℝ) (hx : Irrational x) :
    ∃ k : ℕ, k ≤ 2 ∧ DigitsFrequentlyAtLeast ((2 : ℝ) ^ k * x) 3 := by
  by_contra h
  apply not_all_three_eventualBound_two x hx
  intro k hk
  by_contra hn
  exact h ⟨k,hk,(not_eventualBound_iff _ 2).mp hn⟩

/-- Independent integration test of the general certificate-to-orbit theorem. -/
theorem frequently_three_via_general_window (x : ℝ) (hx : Irrational x) :
    ∃ k : ℕ, DigitsFrequentlyAtLeast ((2 : ℝ) ^ k * x) 3 :=
  P5GeneralWindow.frequently_large_of_window_check 2 0 rank_check_two_zero x hx

end VV.P5SmallCertificate
