import VV.P5Period

/-!
A finite, executable certificate boundary for the graph part of Problem 5.
The checks below quantify only over `Fin n`. Infinite-path soundness and
the connection to quadratic discriminants are proved separately.
No concrete graph is fabricated from the source's vertex/edge counts.
-/

namespace VV.P5Graph

structure Graph where
  size : ℕ
  edge : Fin size → Fin size → Bool
  label : Fin size → ℕ

def Graph.Deterministic (G : Graph) : Prop :=
  ∀ v w z, G.edge v w = true → G.edge v z = true → w = z

instance (G : Graph) : Decidable G.Deterministic :=
  inferInstanceAs (Decidable (∀ v w z, G.edge v w = true → G.edge v z = true → w = z))

def Graph.checkDeterministic (G : Graph) : Bool := decide G.Deterministic

def Graph.checkLabels (G : Graph) (C : ℕ) : Bool := decide (∀ v, G.label v ≤ C)

theorem Graph.checkDeterministic_sound (G : Graph) (h : G.checkDeterministic = true) :
    G.Deterministic := of_decide_eq_true h

theorem Graph.checkLabels_sound (G : Graph) (C : ℕ) (h : G.checkLabels C = true) :
    ∀ v, G.label v ≤ C := of_decide_eq_true h

/-- The real semantic obligation: a positive-index tail of the actual CF
digits is read along an infinite path in this concrete graph. -/
def Graph.Realizes (G : Graph) (x : ℝ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ s : ℕ → Fin G.size,
    (∀ i, G.edge (s i) (s (i + 1)) = true) ∧
    (∀ i, partialQuotient x (N + i) = (G.label (s i) : ℤ))

theorem finite_consistent_path_period_bound {V : Type*} [Fintype V]
    (s : ℕ → V)
    (consistent : ∀ i j, s i = s j → s (i + 1) = s (j + 1)) :
    ∃ i p : ℕ, 0 < p ∧ p ≤ Fintype.card V ∧
      ∀ k : ℕ, s (i + p + k) = s (i + k) := by
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card V + 1) => s i.val) (by simp)
  have pair : ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card V ∧ s i = s j := by
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i.val, j.val, h, by omega, heq⟩
    · exact ⟨j.val, i.val, h, by omega, heq.symm⟩
  obtain ⟨i, j, hij, hj, heq⟩ := pair
  have rep : ∀ k : ℕ, s (i + k) = s (j + k) := by
    intro k
    induction k with
    | zero => simpa using heq
    | succ k ih => simpa only [Nat.add_succ] using consistent (i + k) (j + k) ih
  refine ⟨i, j - i, by omega, by omega, ?_⟩
  intro k
  have hindex : i + (j - i) = j := by omega
  rw [hindex]
  exact (rep k).symm

/-- A finite outdegree-at-most-one check forces every actual infinite
path to be periodic after a finite prefix, with period bounded by `size`.
Dead vertices and transient paths cause no exception. -/
theorem Graph.boundedPeriod_of_realizes (G : Graph) (C : ℕ) {x : ℝ}
    (hd : G.Deterministic) (hl : ∀ v, G.label v ≤ C)
    (hreal : G.Realizes x) : P5Period.BoundedPeriod x C G.size := by
  obtain ⟨N, hN, s, hpath, hlabel⟩ := hreal
  have hc : ∀ i j, s i = s j → s (i + 1) = s (j + 1) := by
    intro i j hij
    apply hd (s j) (s (i + 1)) (s (j + 1))
    · simpa only [hij] using hpath i
    · exact hpath j
  obtain ⟨i, p, hp, hsize, hper⟩ := finite_consistent_path_period_bound s hc
  refine ⟨N + i, p, by omega, hp, by simpa using hsize, ?_, ?_⟩
  · intro k
    have heq := congrArg (fun v => (G.label v : ℤ)) (hper k)
    simpa only [← hlabel, Nat.add_assoc] using heq
  · intro k
    have hb : (G.label (s (i + k)) : ℤ) ≤ (C : ℤ) := by exact_mod_cast hl (s (i + k))
    simpa only [← hlabel, Nat.add_assoc] using hb

/-- All noncomputational theory in the final graph-to-11 step. To apply
this theorem one must supply a CONCRETE graph, its two finite checks, and
the separately proved real-CF path-coverage theorem. -/
theorem problem5_of_graph
    (G : Graph) (hdet : G.checkDeterministic = true) (hlab : G.checkLabels 10 = true)
    (coverage : ∀ x : ℝ, Irrational x →
      (∀ k : ℕ, k ≤ 30 → EventualBound ((2 : ℝ) ^ k * x) 10) →
      G.Realizes ((2 : ℝ) ^ 15 * x)) : Problem5Statement := by
  apply Problem5Real.problem5_of_window_classification
  apply P5Period.windowClassification_of_bounded_period G.size
  intro x hx hlow
  exact G.boundedPeriod_of_realizes 10 (G.checkDeterministic_sound hdet)
    (G.checkLabels_sound 10 hlab) (coverage x hx hlow)

/-- A finite certificate permits transitions to lower ranks; within one
rank there is at most one successor. This handles transient branching. -/
def Graph.RankCertificate (G : Graph) (rank : Fin G.size → Fin (G.size + 1)) : Prop :=
  (∀ v w, G.edge v w = true → (rank w).val ≤ (rank v).val) ∧
  (∀ v w z, G.edge v w = true → G.edge v z = true →
    rank w = rank v → rank z = rank v → w = z)

instance (G : Graph) (rank : Fin G.size → Fin (G.size + 1)) : Decidable (G.RankCertificate rank) :=
  inferInstanceAs (Decidable (
    (∀ v w, G.edge v w = true → (rank w).val ≤ (rank v).val) ∧
    (∀ v w z, G.edge v w = true → G.edge v z = true →
      rank w = rank v → rank z = rank v → w = z)))

/-- This remains a purely finite Boolean check, even when the witness
ranking is not separately materialized as a table. -/
def Graph.checkEventuallyDeterministic (G : Graph) : Bool :=
  decide (∃ rank : Fin G.size → Fin (G.size + 1), G.RankCertificate rank)

theorem antitone_nat_eventually_constant (r : ℕ → ℕ)
    (step : ∀ n, r (n + 1) ≤ r n) :
    ∃ N : ℕ, ∀ k : ℕ, r (N + k) = r N := by
  classical
  have hex : ∃ m : ℕ, ∃ n : ℕ, r n = m := ⟨r 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  have hmin : ∀ n, Nat.find hex ≤ r n := fun n => Nat.find_min' hex ⟨n, rfl⟩
  refine ⟨N, ?_⟩
  intro k
  apply le_antisymm
  · induction k with
    | zero => simp
    | succ k ih => exact (step (N + k)).trans (by simpa only [Nat.add_succ] using ih)
  · rw [hN]
    exact hmin (N + k)

theorem Graph.boundedPeriod_of_rank_realizes (G : Graph) (C : ℕ)
    (rank : Fin G.size → Fin (G.size + 1)) (hcert : G.RankCertificate rank)
    {x : ℝ} (hl : ∀ v, G.label v ≤ C) (hreal : G.Realizes x) :
    P5Period.BoundedPeriod x C G.size := by
  obtain ⟨N, hN, s, hpath, hlabel⟩ := hreal
  obtain ⟨J, hJ⟩ := antitone_nat_eventually_constant
    (fun n => (rank (s n)).val) (fun n => hcert.1 _ _ (hpath n))
  have hc : ∀ i j, s (J + i) = s (J + j) → s (J + (i + 1)) = s (J + (j + 1)) := by
    intro i j hij
    apply hcert.2 (s (J + j)) _ _
    · simpa only [Nat.add_assoc, hij] using hpath (J + i)
    · simpa only [Nat.add_assoc] using hpath (J + j)
    · apply Fin.ext
      exact (hJ (i + 1)).trans (hJ j).symm
    · apply Fin.ext
      exact (hJ (j + 1)).trans (hJ j).symm
  obtain ⟨i, p, hp, hsize, hper⟩ := finite_consistent_path_period_bound
    (fun n => s (J + n)) hc
  refine ⟨N + (J + i), p, by omega, hp, by simpa using hsize, ?_, ?_⟩
  · intro k
    have heq := congrArg (fun v => (G.label v : ℤ)) (hper k)
    simpa only [← hlabel, Nat.add_assoc] using heq
  · intro k
    have hb : (G.label (s (J + (i + k))) : ℤ) ≤ (C : ℤ) := by
      exact_mod_cast hl (s (J + (i + k)))
    simpa only [← hlabel, Nat.add_assoc] using hb

theorem problem5_of_rank_graph
    (G : Graph) (hdet : G.checkEventuallyDeterministic = true)
    (hlab : G.checkLabels 10 = true)
    (coverage : ∀ x : ℝ, Irrational x →
      (∀ k : ℕ, k ≤ 30 → EventualBound ((2 : ℝ) ^ k * x) 10) →
      G.Realizes ((2 : ℝ) ^ 15 * x)) : Problem5Statement := by
  have hc : ∃ rank : Fin G.size → Fin (G.size + 1), G.RankCertificate rank :=
    of_decide_eq_true hdet
  obtain ⟨rank, hcert⟩ := hc
  apply Problem5Real.problem5_of_window_classification
  apply P5Period.windowClassification_of_bounded_period G.size
  intro x hx hlow
  exact G.boundedPeriod_of_rank_realizes 10 rank hcert
    (G.checkLabels_sound 10 hlab) (coverage x hx hlow)

end VV.P5Graph
