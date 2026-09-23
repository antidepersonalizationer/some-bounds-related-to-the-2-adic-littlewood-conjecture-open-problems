import VV.P5Synchronize
import VV.P5Graph
import Mathlib.Data.Fintype.EquivFin

/-! A concrete finite graph associated with a finite synchronized machine. -/

namespace VV.P5MachineGraph
open P5Synchronize P5Graph

variable {V : Type} [Fintype V] [DecidableEq V] (C : ℕ)

abbrev Vertex := V × Fin C

noncomputable def vertexEquiv : Vertex (V := V) C ≃ Fin (Fintype.card (Vertex (V := V) C)) :=
  Fintype.equivFin _

def graphWith {n : ℕ} (code : Vertex (V := V) C ≃ Fin n) (s : Step V (Fin C)) : Graph where
  size := n
  edge i j :=
    let u := code.symm i
    let v := code.symm j
    decide ((s u.1 u.2).map Prod.fst = some v.1)
  label i := (code.symm i).2.val + 1

noncomputable def graph (s : Step V (Fin C)) : Graph :=
  graphWith C (vertexEquiv C) s

theorem graphWith_checkLabels {n : ℕ} (code : Vertex (V := V) C ≃ Fin n)
    (s : Step V (Fin C)) : (graphWith C code s).checkLabels C = true := by
  apply decide_eq_true
  intro i
  exact Nat.succ_le_of_lt ((code.symm i).2.isLt)

theorem graph_label_bound (s : Step V (Fin C)) :
    ∀ i, (graph C s).label i ≤ C := by
  intro i
  exact Nat.succ_le_of_lt (((vertexEquiv (V := V) C).symm i).2.isLt)

theorem graph_checkLabels (s : Step V (Fin C)) : (graph C s).checkLabels C = true := by
  exact decide_eq_true (graph_label_bound C s)

/-- The graph's vertices remember the input digit as well as the machine
state, so an infinite trace gives the original real number's actual CF path. -/
theorem realizes_of_trace (s : Step V (Fin C))
    (input : ℕ → Fin C) (state : ℕ → V) (left right : ℕ → List (Fin C))
    (htrace : Trace s input state left right) {x : ℝ} (N : ℕ) (hN : 0 < N)
    (hdigits : ∀ n, partialQuotient x (N + n) = ((input n).val + 1 : ℕ)) :
    (graph C s).Realizes x := by
  let path := fun n => vertexEquiv C (state n,input n)
  refine ⟨N,hN,path,?_,?_⟩
  · intro n
    change decide ((s ((vertexEquiv C).symm (path n)).1
      ((vertexEquiv C).symm (path n)).2).map Prod.fst =
        some ((vertexEquiv C).symm (path (n + 1))).1) = true
    simp only [path, Equiv.symm_apply_apply, htrace n, Option.map_some]
    rfl
  · intro n
    simpa only [graph, graphWith, path, Equiv.symm_apply_apply] using hdigits n

theorem graphWith_realizes_of_trace {n : ℕ} (code : Vertex (V := V) C ≃ Fin n)
    (s : Step V (Fin C))
    (input : ℕ → Fin C) (state : ℕ → V) (left right : ℕ → List (Fin C))
    (htrace : Trace s input state left right) {x : ℝ} (N : ℕ) (hN : 0 < N)
    (hdigits : ∀ j, partialQuotient x (N + j) = ((input j).val + 1 : ℕ)) :
    (graphWith C code s).Realizes x := by
  refine ⟨N,hN,fun j => code (state j,input j),?_,?_⟩
  · intro j
    change decide ((s (code.symm (code (state j,input j))).1
      (code.symm (code (state j,input j))).2).map Prod.fst =
        some (code.symm (code (state (j+1),input (j+1)))).1) = true
    simp only [Equiv.symm_apply_apply,htrace j,Option.map_some]
    rfl
  · intro j
    simpa only [graphWith,Equiv.symm_apply_apply] using hdigits j

/-- A finite quotient or pruning certificate may be checked independently
of the real-number theory. Label and edge preservation transfer every
actual infinite CF path. -/
theorem realizes_of_graph_map (G H : Graph) (f : Fin G.size → Fin H.size)
    (hlabel : ∀ v, H.label (f v) = G.label v)
    (hedge : ∀ v w, G.edge v w = true → H.edge (f v) (f w) = true)
    {x : ℝ} (h : G.Realizes x) : H.Realizes x := by
  obtain ⟨N,hN,s,hpath,hdigits⟩ := h
  exact ⟨N,hN,fun n => f (s n),fun n => hedge _ _ (hpath n),
    fun n => by rw [hlabel]; exact hdigits n⟩

/-- Once the 31-layer coverage theorem has been supplied, this endpoint
leaves only an explicitly finite Boolean graph check. -/
theorem problem5_of_machine
    (s : Step V (Fin 10))
    (hfinite : (graph 10 s).checkEventuallyDeterministic = true)
    (coverage : ∀ x : ℝ, Irrational x →
      (∀ k : ℕ, k ≤ 30 → EventualBound ((2 : ℝ) ^ k * x) 10) →
      (graph 10 s).Realizes ((2 : ℝ) ^ 15 * x)) : Problem5Statement :=
  problem5_of_rank_graph (graph 10 s) hfinite (graph_checkLabels 10 s) coverage

end VV.P5MachineGraph
