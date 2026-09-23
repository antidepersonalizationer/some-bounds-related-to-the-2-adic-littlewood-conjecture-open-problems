import VV.P5MachineGraph

namespace VV.P5Deterministic
open P5Graph P5MachineGraph P5Synchronize

/-- In a graph obtained from a deterministic streaming machine, two successors
with the same next input digit are equal. The internal monitor state cannot
branch invisibly while keeping the input label fixed. -/
theorem graphWith_successor_eq_of_label_eq {V : Type} [Fintype V] [DecidableEq V]
    (C : ℕ) {n : ℕ} (code : Vertex (V := V) C ≃ Fin n) (s : Step V (Fin C))
    (v w z : Fin n)
    (hw : (graphWith C code s).edge v w = true)
    (hz : (graphWith C code s).edge v z = true)
    (hl : (graphWith C code s).label w = (graphWith C code s).label z) : w = z := by
  have hw' : (s (code.symm v).1 (code.symm v).2).map Prod.fst = some (code.symm w).1 :=
    of_decide_eq_true hw
  have hz' : (s (code.symm v).1 (code.symm v).2).map Prod.fst = some (code.symm z).1 :=
    of_decide_eq_true hz
  have hs : (code.symm w).1 = (code.symm z).1 := Option.some.inj (hw'.symm.trans hz')
  have ha : (code.symm w).2 = (code.symm z).2 := by
    apply Fin.ext
    exact Nat.add_right_cancel hl
  exact code.symm.injective (Prod.ext hs ha)

theorem periodic_mod {A : Type} (f : ℕ → A) (p : ℕ) (hp : 0 < p)
    (hper : ∀ n, f (n + p) = f n) (n : ℕ) : f n = f (n % p) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < p
    · rw [Nat.mod_eq_of_lt hn]
    · have hle : p ≤ n := by omega
      have heq : n = (n-p)+p := by omega
      have hm : n % p = (n-p) % p := by
        conv_lhs => rw [heq]
        simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
      calc
        f n = f (n-p) := by conv_lhs => rw [heq]; exact hper _
        _ = f ((n-p)%p) := ih (n-p) (by omega)
        _ = f (n%p) := congrArg f hm.symm

/-- A periodic input label stream in a finite input-deterministic graph forces
the full vertex stream to be eventually periodic. Thus periodic labels cannot
hide a nonperiodic choice of internal monitor states. -/
theorem periodic_labels_force_periodic_path (G : Graph)
    (hdet : ∀ v w z, G.edge v w = true → G.edge v z = true → G.label w = G.label z → w = z)
    (s : ℕ → Fin G.size) (hpath : ∀ n, G.edge (s n) (s (n+1)) = true)
    (p : ℕ) (hp : 0 < p) (hper : ∀ n, G.label (s (n+p)) = G.label (s n)) :
    ∃ N q : ℕ, 0 < q ∧ ∀ k, s (N+q+k) = s (N+k) := by
  let t : ℕ → Fin G.size × Fin p := fun n => (s n,⟨n%p,Nat.mod_lt n hp⟩)
  have ht : ∀ i j, t i = t j → t (i+1) = t (j+1) := by
    intro i j heq
    have hv : s i = s j := congrArg Prod.fst heq
    have hm : i % p = j % p := congrArg (fun a => a.2.val) heq
    have hm' : (i+1)%p = (j+1)%p := by
      exact (Nat.add_mod i 1 p).trans ((congrArg (fun a => (a + 1 % p) % p) hm).trans (Nat.add_mod j 1 p).symm)
    apply Prod.ext
    · apply hdet (s i)
      · exact hpath i
      · rw [hv]
        exact hpath j
      · rw [periodic_mod (fun n => G.label (s n)) p hp hper (i+1),
          periodic_mod (fun n => G.label (s n)) p hp hper (j+1),hm']
    · exact Fin.ext hm'
  obtain ⟨N,q,hq,_,hperiod⟩ := finite_consistent_path_period_bound t ht
  exact ⟨N,q,hq,fun k => congrArg Prod.fst (hperiod k)⟩

end VV.P5Deterministic

