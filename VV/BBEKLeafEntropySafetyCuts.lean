import VV.BBEKLeafEntropySafety

/-! Summable cuts of actual joint-root safety radii. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped Topology ENNReal
namespace VV.BBEKLeafEntropySafetyCuts
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKLeafEntropyBoundary BBEKLeafEntropySafety

theorem exists_positive_geometric_minorant {d : ℕ → ℝ} {θ : ℝ}
    (hθ : 0 < θ) (hd : ∀ n, 0 < d n)
    (he : ∀ᶠ n : ℕ in atTop, θ^n < d n) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n, ρ*θ^n ≤ d n := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let R : Unit ⊕ Fin N → ℝ := Sum.elim (fun _ => 1) (fun i => d i / θ^(i : ℕ))
  have hR : ∀ i, 0 < R i := by
    intro i
    rcases i with u | i
    · exact zero_lt_one
    · exact div_pos (hd i) (pow_pos hθ _)
  have hne : (Finset.univ : Finset (Unit ⊕ Fin N)).Nonempty := ⟨Sum.inl (),Finset.mem_univ _⟩
  let ρ : ℝ := Finset.univ.inf' hne R
  have hρ : 0 < ρ := (Finset.lt_inf'_iff hne).mpr (fun i _ => hR i)
  have hρone : ρ ≤ 1 := Finset.inf'_le R (Finset.mem_univ (Sum.inl ()))
  refine ⟨ρ,hρ,?_⟩
  intro n
  by_cases hn : n < N
  · have hρn : ρ ≤ d n / θ^n :=
      Finset.inf'_le R (Finset.mem_univ (Sum.inr (⟨n,hn⟩ : Fin N)))
    exact (le_div_iff₀ (pow_pos hθ _)).mp hρn
  · have hm : ρ*θ^n ≤ θ^n := by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hρone (pow_nonneg hθ.le n)
    exact hm.trans (hN n (Nat.le_of_not_gt hn)).le

theorem ae_all_time_boundary_margin (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {T : X → X}
    (hT : MeasurePreserving T μ μ) {r θ : ℝ} (hθ : 0 < θ)
    (hs : (∑' n : ℕ, μ (boundaryTube f r (θ^n))) < ∞) :
    ∀ᵐ q ∂μ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n,
      ρ*θ^n ≤ |f ((T^[n]) q)-r| := by
  have hs' : (∑' n : ℕ, μ (boundaryTube f r (1*θ^n))) < ∞ := by
    simpa only [one_mul] using hs
  have hz := measure_level_eq_zero μ (zero_le_one : (0:ℝ) ≤ 1) hθ.le hs'
  have hnull : ∀ᵐ q ∂μ, f q ≠ r := by simpa only [ae_iff,not_not] using hz
  have hn (n : ℕ) : ∀ᵐ q ∂μ, f ((T^[n]) q) ≠ r :=
    (hT.iterate n).quasiMeasurePreserving.ae hnull
  have he := ae_orbit_eventually_away μ hf hT hs'
  filter_upwards [ae_all_iff.mpr hn,he] with q hq hqe
  apply exists_positive_geometric_minorant hθ
  · intro n
    exact abs_pos.mpr (sub_ne_zero.mpr (hq n))
  · simpa only [one_mul] using hqe

theorem cut_root_shift_iff (c : Chart) (q : X) (u : Leaf) {r : ℝ}
    (h : ‖u‖ < |safetyRadius c q-r|) :
    (r < safetyRadius c (x u.1 u.2 • q) ↔ r < safetyRadius c q) := by
  have he := abs_safetyRadius_sub_le c q u
  obtain ⟨hl,hu⟩ := abs_le.mp he
  by_cases hq : r < safetyRadius c q
  · rw [abs_of_pos (sub_pos.mpr hq)] at h
    exact iff_of_true (by linarith) hq
  · have hn : safetyRadius c q-r ≤ 0 := by linarith
    rw [abs_of_nonpos hn] at h
    exact iff_of_false (by linarith) hq

/-- Every compact set has finitely many cuts inside genuine safe charts. The
cut boundaries have summable masses at every prescribed geometric scale. -/
theorem compact_summable_safe_cuts (μ : Measure X) [IsFiniteMeasure μ]
    {K : Set X} (hK : IsCompact K) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ C : Finset Chart, ∃ a : ℝ, 0 < a ∧ ∃ r : C → ℝ,
      (∀ c, a < r c) ∧
      (∀ q ∈ K, ∃ c : C, r c < safetyRadius c.val q) ∧
      ∀ c : C, (∑' n : ℕ, μ (boundaryTube (safetyRadius c.val) (r c) (θ^n))) < ∞ := by
  classical
  obtain ⟨C,ε,hε,hC⟩ := compact_uniform_safe_plaques hK
  let b : ℝ := min (ε/2) 1
  have hb : 0 < b := lt_min (half_pos hε) zero_lt_one
  have hcov : ∀ q ∈ K, ∃ c : C, b ≤ safetyRadius c.val q := by
    intro q hq
    obtain ⟨c,hc,p,hpq,hp⟩ := hC q hq
    refine ⟨⟨c,hc⟩,le_safetyRadius_of_mem hb.le (min_le_right _ _) ?_⟩
    refine ⟨p,?_,hpq⟩
    intro u hu
    apply hp u
    have hu' : ‖u‖ ≤ b := by simpa only [mem_closedBall,dist_zero_right] using hu
    have hbε : b ≤ ε/2 := min_le_left _ _
    linarith
  have hex (c : C) : ∃ r : ℝ, b/4 < r ∧ r < b/2 ∧
      (∑' n : ℕ, μ (boundaryTube (safetyRadius c.val) r (θ^n))) < ∞ := by
    obtain ⟨r,hr,hs,_,_⟩ := exists_geometric_boundary_cut μ (measurable_safetyRadius c.val)
      (a := b/4) (b := b/2) (c := 1) (θ := θ) (by linarith)
        zero_le_one hθ0 hθ1
    exact ⟨r,hr.1,hr.2,by simpa only [one_mul] using hs⟩
  choose r hra hrb hrs using hex
  refine ⟨C,b/4,by positivity,r,hra,?_,hrs⟩
  intro q hq
  obtain ⟨c,hc⟩ := hcov q hq
  exact ⟨c,(hrb c).trans_le (by linarith)⟩

end VV.BBEKLeafEntropySafetyCuts
