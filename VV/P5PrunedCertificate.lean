import VV.P5GraphSimulation
import VV.P5QuotientCertificate
import VV.P5SCCCertificate

/-!
# Certified transient pruning for the original finite check

The simulation in P5GraphSimulation transfers infinite tails. Here the SCC
criterion strengthens that statement to the original Boolean obligation:
any certified natural-number descent is constant on a recurrent component,
so its internal edges survive in the simulated graph. Label determinism of
the actual machine then pulls successor uniqueness back. No size comparison
between the two graphs and no injectivity of the simulation are required.
-/

namespace VV.P5PrunedCertificate
open P5Graph P5SCCCertificate P5QuotientCertificate

theorem rank_antitone_reach {G H : Graph}
    {f : Fin G.size → Fin H.size} {rank : Fin G.size → ℕ}
    (hsim : G.RankedLabelSimulation H f rank)
    {v w : Fin G.size} (h : Reach G v w) : rank w ≤ rank v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hedge ih => exact (hsim.1 _ _ hedge).trans ih

/-- Every path whose endpoints have equal pruning rank survives the pruning. -/
theorem reach_map_ranked {G H : Graph}
    {f : Fin G.size → Fin H.size} {rank : Fin G.size → ℕ}
    (hsim : G.RankedLabelSimulation H f rank)
    {v w : Fin G.size} (h : Reach G v w) (heq : rank w = rank v) :
    Reach H (f v) (f w) := by
  revert heq
  induction h with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | tail hpath hedge ih =>
    intro heq
    have hpre := rank_antitone_reach hsim hpath
    have hstep := hsim.1 _ _ hedge
    exact Relation.ReflTransGen.tail (ih (by omega))
      (hsim.2.1 _ _ hedge (by omega))

theorem cyclicDeterministic_pullback_ranked {G H : Graph}
    {f : Fin G.size → Fin H.size} {rank : Fin G.size → ℕ}
    (hdet : LabelDeterministic G)
    (hsim : G.RankedLabelSimulation H f rank)
    (hc : CyclicDeterministic H) : CyclicDeterministic G := by
  intro v w z hw hz hwv hzv
  have hwRank : rank w = rank v :=
    Nat.le_antisymm (hsim.1 _ _ hw) (rank_antitone_reach hsim hwv)
  have hzRank : rank z = rank v :=
    Nat.le_antisymm (hsim.1 _ _ hz) (rank_antitone_reach hsim hzv)
  have heq := hc (f v) (f w) (f z)
    (hsim.2.1 _ _ hw hwRank) (hsim.2.1 _ _ hz hzRank)
    (reach_map_ranked hsim hwv hwRank.symm)
    (reach_map_ranked hsim hzv hzRank.symm)
  apply hdet v w z hw hz
  rw [← hsim.2.2 w, ← hsim.2.2 z, heq]

theorem check_of_pruned_compression (G H : Graph)
    (f : Fin G.size → Fin H.size) (rank : Fin G.size → ℕ)
    (hdet : LabelDeterministic G)
    (hsim : G.RankedLabelSimulation H f rank)
    (hcheck : H.checkEventuallyDeterministic = true) :
    G.checkEventuallyDeterministic = true :=
  (check_iff_cyclicDeterministic G).mpr
    (cyclicDeterministic_pullback_ranked hdet hsim
      ((check_iff_cyclicDeterministic H).mp hcheck))

/-- A descent-certified pruning discharges the same original window check. -/
theorem window_check_of_pruned_compression (C r : ℕ) (H : Graph)
    (f : Fin (P5Window.windowGraph C r).size → Fin H.size)
    (rank : Fin (P5Window.windowGraph C r).size → ℕ)
    (hsim : (P5Window.windowGraph C r).RankedLabelSimulation H f rank)
    (hcheck : H.checkEventuallyDeterministic = true) :
    (P5Window.windowGraph C r).checkEventuallyDeterministic = true :=
  check_of_pruned_compression _ H f rank
    (windowGraph_labelDeterministic C r) hsim hcheck

theorem window_check_of_sparse_pruned_compression (C r : ℕ) (H : Graph)
    (f : Fin (P5Window.windowGraph C r).size → Fin H.size)
    (pruneRank : Fin (P5Window.windowGraph C r).size → ℕ)
    (hsim : (P5Window.windowGraph C r).RankedLabelSimulation H f pruneRank)
    (successors : Fin H.size → List (Fin H.size))
    (hexact : P5SparseCertificate.ExactSuccessors H successors)
    (rank : Fin H.size → Fin (H.size + 1))
    (next : Fin H.size → Option (Fin H.size))
    (hcheck : P5SparseCertificate.check H successors rank next = true) :
    (P5Window.windowGraph C r).checkEventuallyDeterministic = true :=
  window_check_of_pruned_compression C r H f pruneRank hsim
    (P5SparseCertificate.eventuallyDeterministic_of_check H successors hexact rank next hcheck)

end VV.P5PrunedCertificate
