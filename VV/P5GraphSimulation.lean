import VV.P5GeneralWindow

/-!
# Sound finite graph compression for Problem 5

A label-preserving forward map transfers every real continued-fraction
path from the raw synchronized graph to a smaller graph. A rank certificate
need only be supplied on that smaller graph. The finite simulation must
still be proved; a vertex count or an unconnected computation is not enough.
-/

namespace VV.P5Graph

/-- A forward graph simulation preserves both allowed steps and the
continued-fraction digit attached to each vertex. It need not be injective. -/
def Graph.LabelSimulation (G H : Graph) (f : Fin G.size → Fin H.size) : Prop :=
  (∀ v w, G.edge v w = true → H.edge (f v) (f w) = true) ∧
  (∀ v, H.label (f v) = G.label v)

instance (G H : Graph) (f : Fin G.size → Fin H.size) :
    Decidable (G.LabelSimulation H f) :=
  inferInstanceAs (Decidable (
    (∀ v w, G.edge v w = true → H.edge (f v) (f w) = true) ∧
    (∀ v, H.label (f v) = G.label v)))

def Graph.checkLabelSimulation (G H : Graph) (f : Fin G.size → Fin H.size) : Bool :=
  decide (G.LabelSimulation H f)

theorem Graph.checkLabelSimulation_iff (G H : Graph) (f : Fin G.size → Fin H.size) :
    G.checkLabelSimulation H f = true ↔ G.LabelSimulation H f := by
  simp only [Graph.checkLabelSimulation, decide_eq_true_eq]

theorem Graph.LabelSimulation.refl (G : Graph) : G.LabelSimulation G id :=
  ⟨fun _ _ h => h, fun _ => rfl⟩

theorem Graph.LabelSimulation.trans {G H K : Graph}
    {f : Fin G.size → Fin H.size} {g : Fin H.size → Fin K.size}
    (hf : G.LabelSimulation H f) (hg : H.LabelSimulation K g) :
    G.LabelSimulation K (g ∘ f) := by
  refine ⟨fun v w h => hg.1 _ _ (hf.1 v w h), ?_⟩
  intro v
  exact (hg.2 (f v)).trans (hf.2 v)

/-- Every actual digit path is preserved by the finite simulation. -/
theorem Graph.Realizes.map {G H : Graph} {f : Fin G.size → Fin H.size}
    (hsim : G.LabelSimulation H f) {x : ℝ} (h : G.Realizes x) :
    H.Realizes x := by
  obtain ⟨N, hN, s, hedge, hlabel⟩ := h
  exact ⟨N, hN, fun n => f (s n), fun n => hsim.1 _ _ (hedge n),
    fun n => by rw [hsim.2]; exact hlabel n⟩

/-- The period bound is the compressed graph's size; no injectivity of
the compression and no determinism of the raw graph are assumed. -/
theorem Graph.boundedPeriod_of_simulation {G H : Graph}
    {f : Fin G.size → Fin H.size} (hsim : G.LabelSimulation H f)
    (C : ℕ) (rank : Fin H.size → Fin (H.size + 1))
    (hcert : H.RankCertificate rank) (hlab : ∀ v, H.label v ≤ C)
    {x : ℝ} (hreal : G.Realizes x) : P5Period.BoundedPeriod x C H.size :=
  H.boundedPeriod_of_rank_realizes C rank hcert hlab (hreal.map hsim)

/-- A finite pruning certificate may discard transitions that strictly
decrease a supplied natural-number rank. Only transitions that preserve
the rank must survive in the compressed graph. -/
def Graph.RankedLabelSimulation (G H : Graph) (f : Fin G.size → Fin H.size)
    (rank : Fin G.size → ℕ) : Prop :=
  (∀ v w, G.edge v w = true → rank w ≤ rank v) ∧
  (∀ v w, G.edge v w = true → rank w = rank v → H.edge (f v) (f w) = true) ∧
  (∀ v, H.label (f v) = G.label v)

instance (G H : Graph) (f : Fin G.size → Fin H.size) (rank : Fin G.size → ℕ) :
    Decidable (G.RankedLabelSimulation H f rank) :=
  inferInstanceAs (Decidable (
    (∀ v w, G.edge v w = true → rank w ≤ rank v) ∧
    (∀ v w, G.edge v w = true → rank w = rank v → H.edge (f v) (f w) = true) ∧
    (∀ v, H.label (f v) = G.label v)))

/-- Transient deletion preserves an actual tail after a further finite
prefix. The prefix is allowed to depend on the path, as required by B. -/
theorem Graph.Realizes.map_ranked {G H : Graph}
    {f : Fin G.size → Fin H.size} {rank : Fin G.size → ℕ}
    (hsim : G.RankedLabelSimulation H f rank) {x : ℝ} (h : G.Realizes x) :
    H.Realizes x := by
  obtain ⟨N, hN, s, hedge, hlabel⟩ := h
  obtain ⟨J, hJ⟩ := antitone_nat_eventually_constant
    (fun n => rank (s n)) (fun n => hsim.1 _ _ (hedge n))
  refine ⟨N + J, by omega, fun n => f (s (J + n)), ?_, ?_⟩
  · intro n
    apply hsim.2.1
    · simpa only [Nat.add_assoc] using hedge (J + n)
    · exact (hJ (n + 1)).trans (hJ n).symm
  · intro n
    rw [hsim.2.2]
    simpa only [Nat.add_assoc] using hlabel (J + n)

theorem Graph.LabelSimulation.ranked {G H : Graph}
    {f : Fin G.size → Fin H.size} (hsim : G.LabelSimulation H f) :
    G.RankedLabelSimulation H f (fun _ => 0) :=
  ⟨fun _ _ _ => le_rfl, fun v w h _ => hsim.1 v w h, hsim.2⟩

end VV.P5Graph

namespace VV.P5GeneralWindow

/-- A proved finite compression of the actual raw window graph suffices
to transport a small graph's certificate into the real-number argument. -/
theorem classification_of_window_simulation (C r : ℕ) (H : P5Graph.Graph)
    (f : Fin (P5Window.windowGraph C r).size → Fin H.size)
    (hsim : (P5Window.windowGraph C r).LabelSimulation H f)
    (rank : Fin H.size → Fin (H.size + 1)) (hcert : H.RankCertificate rank)
    (hlab : ∀ v, H.label v ≤ C) :
    WindowClassification C (2 * (r + 1)) (r + 1) := by
  apply classification_of_rank_graph H rank hcert hlab
  intro x hx hlow
  exact (P5Window.windowGraph_realizes C r hx hlow).map hsim

/-- The same finite-certificate reduction allows certified removal of
transient transitions before checking the smaller graph's rank. -/
theorem classification_of_pruned_window (C r : ℕ) (H : P5Graph.Graph)
    (f : Fin (P5Window.windowGraph C r).size → Fin H.size)
    (pruneRank : Fin (P5Window.windowGraph C r).size → ℕ)
    (hsim : (P5Window.windowGraph C r).RankedLabelSimulation H f pruneRank)
    (rank : Fin H.size → Fin (H.size + 1)) (hcert : H.RankCertificate rank)
    (hlab : ∀ v, H.label v ≤ C) :
    WindowClassification C (2 * (r + 1)) (r + 1) := by
  apply classification_of_rank_graph H rank hcert hlab
  intro x hx hlow
  exact (P5Window.windowGraph_realizes C r hx hlow).map_ranked hsim

/-- The full numerical consequence of a compressed finite certificate.
All extra hypotheses are finite graph conditions, not unproved statements
about irrational numbers or infinite paths. -/
theorem eventual_every_window_of_simulation (C r : ℕ) (H : P5Graph.Graph)
    (f : Fin (P5Window.windowGraph C r).size → Fin H.size)
    (hsim : (P5Window.windowGraph C r).LabelSimulation H f)
    (rank : Fin H.size → Fin (H.size + 1)) (hcert : H.RankCertificate rank)
    (hlab : ∀ v, H.label v ≤ C)
    (x : ℝ) (hx : Irrational x) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ k : ℕ, k ≤ 2 * (r + 1) ∧
      DigitsFrequentlyAtLeast ((2 : ℝ) ^ (j + k) * x) (C + 1) :=
  eventual_every_window
    (classification_of_window_simulation C r H f hsim rank hcert hlab) x hx

end VV.P5GeneralWindow
