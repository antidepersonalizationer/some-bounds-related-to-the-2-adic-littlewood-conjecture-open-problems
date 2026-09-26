import VV.P5SCCCertificate
import VV.P5Window

/-! A seven-vertex/eight-edge obstruction in the literal C=3, r=0 graph.
All eight machine transitions are kernel-checked with ordinary decide.
This is unrelated to the unverified C=10, r=14 obligation. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace VV.P5SmallObstruction
open Hurwitz P5Machine P5MachineGraph P5Graph P5Window P5SCCCertificate

def pair (s t : State) (a b : Fin 3) (z w : Bool) (h : s ≠ t) : Pair 3 :=
  ⟨((s,a,z),(t,b,w)),h⟩

def data (i : Fin 7) : Pair 3 × Fin 3 :=
  match i.val with
  | 0 => (pair .D .H1 0 0 false false (by decide),0)
  | 1 => (pair .D .H0 0 1 true false (by decide),0)
  | 2 => (pair .H0 .D 1 0 false true (by decide),0)
  | 3 => (pair .H0 .H1 2 0 false false (by decide),1)
  | 4 => (pair .H0 .H1 2 0 false false (by decide),2)
  | 5 => (pair .H1 .D 0 0 false false (by decide),0)
  | _ => (pair .H1 .H0 0 2 false false (by decide),1)

def edges : List (Fin 7 × Fin 7) :=
  [(1,3),(1,4),(3,0),(0,2),(2,6),(6,5),(5,1),(4,5)]

def transitionCheck (i j : Fin 7) : Bool :=
  decide ((step 3 (data i).1 (data i).2).map Prod.fst = some (data j).1)

theorem edges_checked : edges.all (fun e => transitionCheck e.1 e.2) = true := by decide

noncomputable def vertex (i : Fin 7) : Fin (windowGraph 3 0).size :=
  (vertexEquiv (V := Pair 3) 3) (data i)

theorem actual_edge (i j : Fin 7) (hmem : (i,j) ∈ edges) :
    (windowGraph 3 0).edge (vertex i) (vertex j) = true := by
  have h := List.all_eq_true.mp edges_checked (i,j) hmem
  change decide ((step 3
    ((vertexEquiv (V := Pair 3) 3).symm ((vertexEquiv (V := Pair 3) 3) (data i))).1
    ((vertexEquiv (V := Pair 3) 3).symm ((vertexEquiv (V := Pair 3) 3) (data i))).2).map
    Prod.fst =
    some ((vertexEquiv (V := Pair 3) 3).symm ((vertexEquiv (V := Pair 3) 3) (data j))).1) = true
  simpa only [Equiv.symm_apply_apply] using h

theorem edge_reach (i j : Fin 7) (hmem : (i,j) ∈ edges) :
    Reach (windowGraph 3 0) (vertex i) (vertex j) :=
  Relation.ReflTransGen.single (actual_edge i j hmem)

theorem return_three : Reach (windowGraph 3 0) (vertex 3) (vertex 1) :=
  (edge_reach 3 0 (by decide)).trans
    ((edge_reach 0 2 (by decide)).trans
      ((edge_reach 2 6 (by decide)).trans
        ((edge_reach 6 5 (by decide)).trans
          (edge_reach 5 1 (by decide)))))

theorem return_four : Reach (windowGraph 3 0) (vertex 4) (vertex 1) :=
  (edge_reach 4 5 (by decide)).trans
    (edge_reach 5 1 (by decide))

theorem distinct_successors : vertex 3 ≠ vertex 4 := by
  intro h
  have hd := (vertexEquiv (V := Pair 3) 3).injective h
  have hlabel := congrArg Prod.snd hd
  change (1 : Fin 3) = 2 at hlabel
  exact (by decide : (1 : Fin 3) ≠ 2) hlabel

theorem not_rank_check_three_zero :
    ¬ (windowGraph 3 0).checkEventuallyDeterministic = true :=
  not_check_of_cyclic_branch (windowGraph 3 0) (vertex 1) (vertex 3) (vertex 4)
    (actual_edge 1 3 (by decide)) (actual_edge 1 4 (by decide))
    return_three return_four distinct_successors

theorem rank_check_three_zero_eq_false :
    (windowGraph 3 0).checkEventuallyDeterministic = false := by
  cases h : (windowGraph 3 0).checkEventuallyDeterministic with
  | false => rfl
  | true => exact False.elim (not_rank_check_three_zero h)

end VV.P5SmallObstruction
