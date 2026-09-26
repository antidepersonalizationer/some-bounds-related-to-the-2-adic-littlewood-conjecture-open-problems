import VV.P5SparseCertificate

/-!
Compression certificates for the ORIGINAL synchronized graph.

An arbitrary graph homomorphism need not preserve rank certificates.
Here the source graph additionally has uniquely labeled successors,
which is proved for the actual machine graph. Consequently a
label-preserving map into a smaller rank-certified graph pulls the
certificate back, even when the map is not injective. This supplies a
sound compression boundary without changing the admitted graph.
-/

namespace VV.P5QuotientCertificate
open P5Graph P5Synchronize P5MachineGraph

def LabelDeterministic (G : Graph) : Prop :=
  ∀ v w z, G.edge v w = true → G.edge v z = true →
    G.label w = G.label z → w = z

theorem graphWith_labelDeterministic {V : Type} [Fintype V] [DecidableEq V]
    (C : ℕ) {n : ℕ} (code : (V × Fin C) ≃ Fin n) (s : Step V (Fin C)) :
    LabelDeterministic (graphWith C code s) := by
  intro v w z hw hz hl
  change decide ((s (code.symm v).1 (code.symm v).2).map Prod.fst =
    some (code.symm w).1) = true at hw
  change decide ((s (code.symm v).1 (code.symm v).2).map Prod.fst =
    some (code.symm z).1) = true at hz
  have heq : (code.symm w).1 = (code.symm z).1 :=
    Option.some.inj ((of_decide_eq_true hw).symm.trans (of_decide_eq_true hz))
  apply code.symm.injective
  apply Prod.ext heq
  apply Fin.ext
  change (code.symm w).2.val + 1 = (code.symm z).2.val + 1 at hl
  exact Nat.add_right_cancel hl

theorem graph_labelDeterministic {V : Type} [Fintype V] [DecidableEq V]
    (C : ℕ) (s : Step V (Fin C)) : LabelDeterministic (graph C s) :=
  graphWith_labelDeterministic C (vertexEquiv C) s

/-- Label preservation suffices; injectivity of the compression map is not
assumed. The size comparison only bounds the codomain of the lifted rank. -/
theorem rankCertificate_pullback (G H : Graph) (f : Fin G.size → Fin H.size)
    (hsize : H.size ≤ G.size) (hdet : LabelDeterministic G)
    (hlabel : ∀ v, H.label (f v) = G.label v)
    (hedge : ∀ v w, G.edge v w = true → H.edge (f v) (f w) = true)
    (rank : Fin H.size → Fin (H.size + 1)) (hcert : H.RankCertificate rank) :
    G.RankCertificate (fun v => ⟨(rank (f v)).val,
      lt_of_lt_of_le (rank (f v)).isLt (Nat.add_le_add_right hsize 1)⟩) := by
  refine ⟨?_, ?_⟩
  · intro v w hw
    exact hcert.1 (f v) (f w) (hedge v w hw)
  · intro v w z hw hz hrw hrz
    have hrw' : rank (f w) = rank (f v) := Fin.ext (congrArg (fun a : Fin (G.size + 1) => a.val) hrw)
    have hrz' : rank (f z) = rank (f v) := Fin.ext (congrArg (fun a : Fin (G.size + 1) => a.val) hrz)
    have heq := hcert.2 (f v) (f w) (f z) (hedge v w hw) (hedge v z hz) hrw' hrz'
    apply hdet v w z hw hz
    rw [← hlabel w, ← hlabel z, heq]

theorem check_of_smaller_graph (G H : Graph) (f : Fin G.size → Fin H.size)
    (hsize : H.size ≤ G.size) (hdet : LabelDeterministic G)
    (hlabel : ∀ v, H.label (f v) = G.label v)
    (hedge : ∀ v w, G.edge v w = true → H.edge (f v) (f w) = true)
    (hcheck : H.checkEventuallyDeterministic = true) :
    G.checkEventuallyDeterministic = true := by
  obtain ⟨rank,hcert⟩ := of_decide_eq_true hcheck
  apply decide_eq_true
  exact ⟨_, rankCertificate_pullback G H f hsize hdet hlabel hedge rank hcert⟩

theorem windowGraph_labelDeterministic (C r : ℕ) :
    LabelDeterministic (P5Window.windowGraph C r) := by
  letI : DecidableEq (StateAt (P5Machine.Pair C) r) :=
    P5Window.stateAtDecidableEq (P5Machine.Pair C) r
  exact graph_labelDeterministic C (iterate (P5Machine.step C) r)

/-- This conclusion is the existing check on the raw graph, not a new
check on a substituted graph. Finding the compression remains a finite
certificate construction problem, not an assumption about real numbers. -/
theorem window_check_of_compression (C r : ℕ) (H : Graph)
    (f : Fin (P5Window.windowGraph C r).size → Fin H.size)
    (hsize : H.size ≤ (P5Window.windowGraph C r).size)
    (hlabel : ∀ v, H.label (f v) = (P5Window.windowGraph C r).label v)
    (hedge : ∀ v w, (P5Window.windowGraph C r).edge v w = true →
      H.edge (f v) (f w) = true)
    (hcheck : H.checkEventuallyDeterministic = true) :
    (P5Window.windowGraph C r).checkEventuallyDeterministic = true :=
  check_of_smaller_graph _ H f hsize (windowGraph_labelDeterministic C r) hlabel hedge hcheck

/-- A sparse rank table for a smaller graph plus a certified compression
proves the original finite obligation. -/
theorem window_check_of_sparse_compression (C r : ℕ) (H : Graph)
    (f : Fin (P5Window.windowGraph C r).size → Fin H.size)
    (hsize : H.size ≤ (P5Window.windowGraph C r).size)
    (hlabel : ∀ v, H.label (f v) = (P5Window.windowGraph C r).label v)
    (hedge : ∀ v w, (P5Window.windowGraph C r).edge v w = true →
      H.edge (f v) (f w) = true)
    (successors : Fin H.size → List (Fin H.size))
    (hexact : P5SparseCertificate.ExactSuccessors H successors)
    (rank : Fin H.size → Fin (H.size + 1))
    (next : Fin H.size → Option (Fin H.size))
    (hcheck : P5SparseCertificate.check H successors rank next = true) :
    (P5Window.windowGraph C r).checkEventuallyDeterministic = true :=
  window_check_of_compression C r H f hsize hlabel hedge
    (P5SparseCertificate.eventuallyDeterministic_of_check H successors hexact rank next hcheck)

end VV.P5QuotientCertificate
