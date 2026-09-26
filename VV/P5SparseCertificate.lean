import VV.P5Window

/-! Sparse validation of a supplied rank: no search over rank functions.
The machine successor lists are exactly those of the existing graph.
No concrete depth-14 certificate is asserted. -/

namespace VV.P5SparseCertificate
open P5Graph P5Synchronize P5MachineGraph

def check (G : Graph) (successors : Fin G.size → List (Fin G.size))
    (rank : Fin G.size → Fin (G.size + 1))
    (next : Fin G.size → Option (Fin G.size)) : Bool :=
  (List.finRange G.size).all fun v => (successors v).all fun w =>
    decide ((rank w).val ≤ (rank v).val ∧ (rank w = rank v → next v = some w))

def ExactSuccessors (G : Graph) (successors : Fin G.size → List (Fin G.size)) : Prop :=
  ∀ v w, G.edge v w = true ↔ w ∈ successors v

theorem check_sound (G : Graph) (successors : Fin G.size → List (Fin G.size))
    (hexact : ExactSuccessors G successors)
    (rank : Fin G.size → Fin (G.size + 1))
    (next : Fin G.size → Option (Fin G.size))
    (h : check G successors rank next = true) : G.RankCertificate rank := by
  have localCheck (v w : Fin G.size) (hw : G.edge v w = true) :
      (rank w).val ≤ (rank v).val ∧ (rank w = rank v → next v = some w) := by
    have hv := List.all_eq_true.mp h v (by simp)
    exact of_decide_eq_true (List.all_eq_true.mp hv w ((hexact v w).mp hw))
  refine ⟨fun v w hw => (localCheck v w hw).1, ?_⟩
  intro v w z hw hz hrw hrz
  exact Option.some.inj (((localCheck v w hw).2 hrw).symm.trans
    ((localCheck v z hz).2 hrz))

def sameRankNext (G : Graph) (successors : Fin G.size → List (Fin G.size))
    (rank : Fin G.size → Fin (G.size + 1)) (v : Fin G.size) : Option (Fin G.size) :=
  (successors v).find? fun w => decide (rank w = rank v)

theorem check_complete (G : Graph) (successors : Fin G.size → List (Fin G.size))
    (hexact : ExactSuccessors G successors)
    (rank : Fin G.size → Fin (G.size + 1)) (h : G.RankCertificate rank) :
    check G successors rank (sameRankNext G successors rank) = true := by
  apply List.all_eq_true.mpr
  intro v _
  apply List.all_eq_true.mpr
  intro w hw
  apply decide_eq_true
  refine ⟨h.1 v w ((hexact v w).mpr hw), ?_⟩
  intro hrw
  cases he : sameRankNext G successors rank v with
  | none =>
    have hn := List.find?_eq_none.mp he w hw
    exact False.elim (hn (by simpa using hrw))
  | some z =>
    have hz : z ∈ successors v := List.mem_of_find?_eq_some he
    have hrz : rank z = rank v := of_decide_eq_true (List.find?_some (p := fun w => decide (rank w = rank v)) he)
    have hzw := h.2 v z w ((hexact v z).mpr hz) ((hexact v w).mpr hw) hrz hrw
    simpa [hzw] using he

theorem check_iff_rankCertificate (G : Graph)
    (successors : Fin G.size → List (Fin G.size)) (hexact : ExactSuccessors G successors)
    (rank : Fin G.size → Fin (G.size + 1)) :
    check G successors rank (sameRankNext G successors rank) = true ↔
      G.RankCertificate rank :=
  ⟨check_sound G successors hexact rank _, check_complete G successors hexact rank⟩

theorem eventuallyDeterministic_of_check (G : Graph)
    (successors : Fin G.size → List (Fin G.size)) (hexact : ExactSuccessors G successors)
    (rank : Fin G.size → Fin (G.size + 1))
    (next : Fin G.size → Option (Fin G.size)) (h : check G successors rank next = true) :
    G.checkEventuallyDeterministic = true :=
  decide_eq_true ⟨rank, check_sound G successors hexact rank next h⟩

variable {V : Type} [Fintype V] [DecidableEq V] {C n : ℕ}

def machineSuccessors (code : (V × Fin C) ≃ Fin n) (s : Step V (Fin C))
    (i : Fin n) : List (Fin n) :=
  match s (code.symm i).1 (code.symm i).2 with
  | none => []
  | some t => (List.finRange C).map fun a => code (t.1, a)

theorem machineSuccessors_exact (code : (V × Fin C) ≃ Fin n) (s : Step V (Fin C)) :
    ExactSuccessors (graphWith C code s) (machineSuccessors code s) := by
  intro i j
  change decide ((s (code.symm i).1 (code.symm i).2).map Prod.fst =
    some (code.symm j).1) = true ↔ j ∈ machineSuccessors code s i
  rw [decide_eq_true_eq]
  cases hs : s (code.symm i).1 (code.symm i).2 with
  | none => simp [machineSuccessors, hs]
  | some t =>
    simp only [Option.map_some, Option.some.injEq, machineSuccessors, hs]
    constructor
    · intro ht
      apply List.mem_map.mpr
      exact ⟨(code.symm j).2, by simp, by rw [ht]; exact code.apply_symm_apply j⟩
    · intro hj
      change j ∈ (List.finRange C).map (fun a => code (t.1,a)) at hj
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hj
      have := congrArg (fun k => (code.symm k).1) ha
      simpa using this

theorem machineSuccessors_length_le (code : (V × Fin C) ≃ Fin n)
    (s : Step V (Fin C)) (i : Fin n) : (machineSuccessors code s i).length ≤ C := by
  unfold machineSuccessors
  split <;> simp

/-- Finite renumbering preserves the original rank-check proposition. -/
theorem original_check_of_encoded_check (code : (V × Fin C) ≃ Fin n)
    (s : Step V (Fin C))
    (h : (graphWith C code s).checkEventuallyDeterministic = true) :
    (graph C s).checkEventuallyDeterministic = true := by
  have hn : n = Fintype.card (V × Fin C) := by
    simpa using (Fintype.card_congr code).symm
  subst n
  obtain ⟨rank, hr⟩ := of_decide_eq_true h
  let e : Fin (Fintype.card (V × Fin C)) ≃ Fin (Fintype.card (V × Fin C)) :=
    (vertexEquiv C).symm.trans code
  have hedge (v w) : (graphWith C code s).edge (e v) (e w) = (graph C s).edge v w := by
    simp [graphWith, graph, e]
  apply decide_eq_true
  refine ⟨fun v => rank (e v), ?_, ?_⟩
  · intro v w hw
    exact hr.1 (e v) (e w) (by rw [hedge]; exact hw)
  · intro v w z hw hz hrw hrz
    apply e.injective
    exact hr.2 (e v) (e w) (e z) (by rw [hedge]; exact hw)
      (by rw [hedge]; exact hz) hrw hrz

theorem original_check_of_sparse_check (code : (V × Fin C) ≃ Fin n)
    (s : Step V (Fin C)) (rank : Fin n → Fin (n + 1))
    (next : Fin n → Option (Fin n))
    (h : check (graphWith C code s) (machineSuccessors code s) rank next = true) :
    (graph C s).checkEventuallyDeterministic = true :=
  original_check_of_encoded_check code s
    (eventuallyDeterministic_of_check _ _ (machineSuccessors_exact code s) rank next h)

end VV.P5SparseCertificate
