import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Exponentially numerous orbit-separated finite sets extracted from the
actual mathlib definition of positive topological entropy. -/

noncomputable section
open Set Filter Function Uniformity UniformSpace
open scoped Topology ENNReal

namespace ErgodicTheory.Entropy

variable {X : Type*} [PseudoMetricSpace X]

structure SeparatedEntropyWitness (T : X → X) where
  scale : ℝ
  scale_pos : 0 < scale
  rate : ℝ
  rate_pos : 0 < rate
  time : ℕ → ℕ
  time_pos : ∀ j, 0 < time j
  time_strictMono : StrictMono time
  points : ℕ → Finset X
  points_nonempty : ∀ j, (points j).Nonempty
  separated : ∀ j, ∀ x ∈ points j, ∀ y ∈ points j, x ≠ y →
    ∃ k < time j, scale ≤ dist ((T^[k]) x) ((T^[k]) y)
  card_rate : ∀ j, rate * time j ≤ Real.log (points j).card

theorem separatedEntropyWitness_of_pos [CompactSpace X] [Nonempty X]
    (T : X → X) (hpos : 0 < Dynamics.coverEntropy T univ) :
    Nonempty (SeparatedEntropyWitness T) := by
  classical
  rw [Dynamics.coverEntropy_eq_iSup_netEntropyEntourage] at hpos
  obtain ⟨U, hU⟩ := lt_iSup_iff.mp hpos
  obtain ⟨hUuni, hUpos⟩ := lt_iSup_iff.mp hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hUuni
  let V : Set (X × X) := {p | dist p.1 p.2 < ε}
  have hV : V ∈ 𝓤 X := Metric.dist_mem_uniformity hε
  have hVsymm : IsSymmetricRel V := by
    ext p
    change dist p.2 p.1 < ε ↔ dist p.1 p.2 < ε
    rw [dist_comm]
  have hUV : U ⊇ V := fun p hp => hεU hp
  have hVpos : 0 < Dynamics.netEntropyEntourage T univ V :=
    hUpos.trans_le (Dynamics.netEntropyEntourage_antitone T univ hUV)
  obtain ⟨c, hc0, hcV⟩ := EReal.exists_between_coe_real hVpos
  have hc : 0 < c := by exact_mod_cast hc0
  have hfreq := ExpGrowth.frequently_exp_le hcV
  have hfreq' : ∃ᶠ n : ℕ in atTop,
      0 < n ∧ EReal.exp ((c : EReal) * n) ≤
        (Dynamics.netMaxcard T univ V n).toENNReal := by
    exact hfreq.and_eventually (eventually_gt_atTop 0) |>.mono (fun _ h => ⟨h.2,h.1⟩)
  obtain ⟨r, hr, hrprop⟩ := extraction_of_frequently_atTop hfreq'
  have hfinite : ∀ n, Dynamics.netMaxcard T univ V n < ⊤ := fun n =>
    (Dynamics.netMaxcard_le_coverMincard T univ hVsymm n).trans_lt
      (Dynamics.coverMincard_finite_of_isCompact_invariant isCompact_univ
        (mapsTo_univ T univ) hV n)
  choose S hS hcard using fun j =>
    (Dynamics.netMaxcard_finite_iff T univ V (r j)).mp (hfinite (r j))
  have hSne : ∀ j, (S j).Nonempty := by
    intro j
    have h1 := (Dynamics.one_le_netMaxcard_iff T univ V (r j)).mpr univ_nonempty
    rw [← hcard j] at h1
    exact Finset.card_pos.mp (by exact_mod_cast h1)
  refine ⟨⟨ε,hε,c,hc,r,(fun j => (hrprop j).1),hr,S,hSne,?_,?_⟩⟩
  · intro j x hx y hy hxy
    apply Classical.byContradiction
    intro hno
    have hn : ∀ k < r j, dist (T^[k] x) (T^[k] y) < ε := by
      intro k hk
      exact lt_of_not_ge (fun h => hno ⟨k,hk,h⟩)
    have hclose : x ∈ UniformSpace.ball y (Dynamics.dynEntourage T V (r j)) := by
      apply Dynamics.mem_ball_dynEntourage.mpr
      intro k hk
      simpa only [UniformSpace.ball, V, Set.mem_preimage, Set.mem_setOf_eq, dist_comm] using hn k hk
    have hself : x ∈ UniformSpace.ball x (Dynamics.dynEntourage T V (r j)) := by
      apply Dynamics.mem_ball_dynEntourage.mpr
      intro k hk
      change dist _ _ < ε
      simpa only [dist_self] using hε
    exact hxy (Set.PairwiseDisjoint.elim_set (hS j).2 hx hy x hself hclose)
  · intro j
    have he := (hrprop j).2
    rw [← hcard j] at he
    have hl := ENNReal.log_le_log he
    rw [EReal.log_exp] at hl
    have hp : (0 : ℝ) < (S j).card := by exact_mod_cast (hSne j).card_pos
    have hlog : ENNReal.log ((S j).card : ℝ≥0∞) = (Real.log (S j).card : EReal) := by
      rw [ENNReal.log_pos_real' (by simpa only [ENNReal.toReal_natCast] using hp),
        ENNReal.toReal_natCast]
    simpa only [ENat.toENNReal_coe, hlog,
      ← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff] using hl

end ErgodicTheory.Entropy



