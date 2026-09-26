import VV.P5Graph
import Mathlib.Logic.Relation

/-!
The rank-existence proposition is exactly a strongly-connected-component
criterion. The proof constructs a rank from the number of reachable vertices,
without executing either transitive closure or a rank-function search.
The reachability-based construction here is mathematical; the existing sparse
checker is the executable boundary for externally discovered certificates.
-/

namespace VV.P5SCCCertificate
open P5Graph

def Reach (G : Graph) (v w : Fin G.size) : Prop :=
  Relation.ReflTransGen (fun v w => G.edge v w = true) v w

/-- An edge can remain inside its source SCC only if its target can return.
Within that SCC, every vertex must have at most one outgoing target. -/
def CyclicDeterministic (G : Graph) : Prop :=
  ∀ v w z, G.edge v w = true → G.edge v z = true →
    Reach G w v → Reach G z v → w = z

theorem rank_antitone_reach (G : Graph)
    (rank : Fin G.size → Fin (G.size + 1)) (hc : G.RankCertificate rank)
    {v w : Fin G.size} (h : Reach G v w) : (rank w).val ≤ (rank v).val := by
  induction h with
  | refl => exact le_rfl
  | tail _ hedge ih => exact (hc.1 _ _ hedge).trans ih

theorem cyclicDeterministic_of_rank (G : Graph)
    (rank : Fin G.size → Fin (G.size + 1)) (hc : G.RankCertificate rank) :
    CyclicDeterministic G := by
  intro v w z hw hz hwv hzv
  apply hc.2 v w z hw hz
  · apply Fin.ext
    exact Nat.le_antisymm (hc.1 v w hw) (rank_antitone_reach G rank hc hwv)
  · apply Fin.ext
    exact Nat.le_antisymm (hc.1 v z hz) (rank_antitone_reach G rank hc hzv)

noncomputable def reachableSet (G : Graph) (v : Fin G.size) : Finset (Fin G.size) := by
  classical
  exact Finset.univ.filter (Reach G v)

theorem mem_reachableSet (G : Graph) (v w : Fin G.size) :
    w ∈ reachableSet G v ↔ Reach G v w := by
  classical
  simp [reachableSet]

theorem reachableSet_subset (G : Graph) {v w : Fin G.size} (h : G.edge v w = true) :
    reachableSet G w ⊆ reachableSet G v := by
  intro z hz
  apply (mem_reachableSet G v z).mpr
  exact Relation.ReflTransGen.head h ((mem_reachableSet G w z).mp hz)

noncomputable def reachableRank (G : Graph) (v : Fin G.size) : Fin (G.size + 1) :=
  ⟨(reachableSet G v).card, by
    have h := Finset.card_le_univ (reachableSet G v)
    simpa using Nat.lt_succ_of_le h⟩

theorem return_path_of_equal_rank (G : Graph) {v w : Fin G.size}
    (hedge : G.edge v w = true) (hr : reachableRank G w = reachableRank G v) :
    Reach G w v := by
  have hcard : (reachableSet G v).card ≤ (reachableSet G w).card :=
    Nat.le_of_eq (congrArg Fin.val hr).symm
  have hset := Finset.eq_of_subset_of_card_le (reachableSet_subset G hedge) hcard
  apply (mem_reachableSet G w v).mp
  rw [hset]
  exact (mem_reachableSet G v v).mpr Relation.ReflTransGen.refl

theorem reachableRank_certificate (G : Graph) (h : CyclicDeterministic G) :
    G.RankCertificate (reachableRank G) := by
  refine ⟨?_, ?_⟩
  · intro v w hw
    exact Finset.card_le_card (reachableSet_subset G hw)
  · intro v w z hw hz hrw hrz
    exact h v w z hw hz (return_path_of_equal_rank G hw hrw)
      (return_path_of_equal_rank G hz hrz)

theorem exists_rank_iff_cyclicDeterministic (G : Graph) :
    (∃ rank : Fin G.size → Fin (G.size + 1), G.RankCertificate rank) ↔
      CyclicDeterministic G := by
  constructor
  · rintro ⟨rank,h⟩
    exact cyclicDeterministic_of_rank G rank h
  · intro h
    exact ⟨reachableRank G,reachableRank_certificate G h⟩

theorem check_iff_cyclicDeterministic (G : Graph) :
    G.checkEventuallyDeterministic = true ↔ CyclicDeterministic G := by
  rw [Graph.checkEventuallyDeterministic, decide_eq_true_eq]
  exact exists_rank_iff_cyclicDeterministic G

/-- A small finite pair of return paths is sufficient to refute any proposed
rank certificate; no enumeration of ranks is needed. -/
theorem not_check_of_cyclic_branch (G : Graph) (v w z : Fin G.size)
    (hw : G.edge v w = true) (hz : G.edge v z = true)
    (hwv : Reach G w v) (hzv : Reach G z v) (hne : w ≠ z) :
    ¬ G.checkEventuallyDeterministic = true := by
  intro h
  exact hne ((check_iff_cyclicDeterministic G).mp h v w z hw hz hwv hzv)

end VV.P5SCCCertificate
