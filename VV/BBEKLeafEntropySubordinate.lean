import VV.BBEKLeafEntropySafetyCuts

/-!
# Measurable codes subordinate to actual root plaques

Every active chart records its transverse coordinate. Inactive charts record
a separate symbol. Recording these observations at all inverse iterates gives
a countably generated measurable partition, with genuine root plaques as fibers.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped Topology ENNReal
namespace VV.BBEKLeafEntropySubordinate
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKLeafEntropyBoundary BBEKLeafEntropySafety BBEKLeafEntropySafetyCuts
  BBEKRootLeafKernel

section Code
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

def plaqueCode (s : GroupParams ≃ₜ B × U) (c : Chart) (r : ℝ) (q : X) : Unit ⊕ B :=
  if r < safetyRadius c q then Sum.inr (s (chartCoordinates c q)).1 else Sum.inl ()

theorem measurable_plaqueCode (s : GroupParams ≃ₜ B × U) (c : Chart) (r : ℝ) :
    Measurable (plaqueCode s c r) := by
  apply Measurable.ite (isOpen_safetyRadius_superlevel c r).measurableSet
  · exact measurable_inr.comp ((s.measurable.comp (measurable_chartCoordinates c)).fst)
  · exact measurable_const

theorem chartCoordinates_root_shift (c : Chart) (q : X) (u : Leaf) {r : ℝ}
    (hr : 0 ≤ r) (hq : r < safetyRadius c q) (hu : ‖u‖ ≤ r) :
    chartCoordinates c (x u.1 u.2 • q) = leafShift (chartCoordinates c q) u := by
  obtain ⟨he,hs⟩ := chartCoordinates_safe hr (mem_safeImage_of_lt_safetyRadius hr hq)
  have hm := quotient_leafShift c.base (chartCoordinates c q) u
  rw [he] at hm
  rw [← hm]
  exact chartCoordinates_apply c ⟨_,hs u hu⟩

theorem plaqueCode_root_shift (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, (s (leafShift p (axis u))).1 = (s p).1)
    (c : Chart) (q : X) (u : U) {r : ℝ} (hr : 0 < r)
    (hu : ‖axis u‖ ≤ r) (hmargin : ‖axis u‖ < |safetyRadius c q-r|) :
    plaqueCode s c r (x (axis u).1 (axis u).2 • q) = plaqueCode s c r q := by
  have hi := cut_root_shift_iff c q (axis u) hmargin
  by_cases hq : r < safetyRadius c q
  · simp only [plaqueCode,if_pos hq,if_pos (hi.mpr hq),
      chartCoordinates_root_shift c q (axis u) hr.le hq hu,hs]
  · simp only [plaqueCode,if_neg hq,if_neg (fun h => hq (hi.mp h))]

/-- An active code fiber is contained in a literal orbit of the chosen root. -/
theorem exists_root_of_plaqueCode_eq (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (c : Chart) {q q' : X} {r : ℝ} (hr : 0 ≤ r)
    (hq : r < safetyRadius c q) (he : plaqueCode s c r q' = plaqueCode s c r q) :
    ∃ u : U, q' = x (axis u).1 (axis u).2 • q := by
  have hq' : r < safetyRadius c q' := by
    by_contra hh
    simp only [plaqueCode,if_neg hh,if_pos hq] at he
    contradiction
  have ht : (s (chartCoordinates c q')).1 = (s (chartCoordinates c q)).1 := by
    simpa only [plaqueCode,if_pos hq,if_pos hq',Sum.inr.injEq] using he
  let u := (s (chartCoordinates c q')).2-(s (chartCoordinates c q)).2
  have hc : chartCoordinates c q' = leafShift (chartCoordinates c q) (axis u) := by
    apply s.injective
    rw [hs]
    apply Prod.ext
    · exact ht
    · dsimp only [u]
      simp only [sub_add_cancel]
  obtain ⟨hcoord,_⟩ := chartCoordinates_safe hr (mem_safeImage_of_lt_safetyRadius hr hq)
  obtain ⟨hcoord',_⟩ := chartCoordinates_safe hr (mem_safeImage_of_lt_safetyRadius hr hq')
  refine ⟨u,?_⟩
  rw [← hcoord',hc,quotient_leafShift,hcoord]

def pastPlaqueCode {ι : Type*} (s : GroupParams ≃ₜ B × U)
    (c : ι → Chart) (r : ι → ℝ) (T : X → X) (q : X) : ℕ → ι → Unit ⊕ B :=
  fun n i => plaqueCode s (c i) (r i) ((T^[n]) q)

theorem measurable_pastPlaqueCode {ι : Type*} (s : GroupParams ≃ₜ B × U)
    (c : ι → Chart) (r : ι → ℝ) {T : X → X} (hT : Measurable T) :
    Measurable (pastPlaqueCode s c r T) := by
  apply measurable_pi_lambda
  intro n
  apply measurable_pi_lambda
  intro i
  exact (measurable_plaqueCode s (c i) (r i)).comp (hT.iterate n)

theorem exists_root_of_pastPlaqueCode_eq {ι : Type*} (s : GroupParams ≃ₜ B × U)
    (axis : U → Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (c : ι → Chart) (r : ι → ℝ) (T : X → X) {q q' : X}
    (hactive : ∃ i, 0 ≤ r i ∧ r i < safetyRadius (c i) q)
    (he : pastPlaqueCode s c r T q' = pastPlaqueCode s c r T q) :
    ∃ u : U, q' = x (axis u).1 (axis u).2 • q := by
  obtain ⟨i,hri,hqi⟩ := hactive
  apply exists_root_of_plaqueCode_eq s axis hs (c i) hri hqi
  exact congrFun (congrFun he 0) i

/-- Summable safety cuts and an actual contracting root action make the code
fiber contain a root neighborhood almost everywhere. -/
theorem ae_root_ball_in_pastPlaqueCode {ι : Type*} [Fintype ι]
    (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, (s (leafShift p (axis u))).1 = (s p).1)
    (μ : Measure X) [IsFiniteMeasure μ] (c : ι → Chart) (r : ι → ℝ)
    {a θ : ℝ} (ha : 0 < a) (har : ∀ i, a < r i)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hboundary : ∀ i, (∑' n : ℕ,
      μ (boundaryTube (safetyRadius (c i)) (r i) (θ^n))) < ∞)
    {T : X → X} (hT : MeasurePreserving T μ μ) (D : ℕ → U → U)
    (hconj : ∀ n u q, (T^[n]) (x (axis u).1 (axis u).2 • q) =
      x (axis (D n u)).1 (axis (D n u)).2 • (T^[n]) q)
    (hcontract : ∀ n u, ‖axis (D n u)‖ ≤ θ^n*‖u‖) :
    ∀ᵐ q ∂μ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : U, ‖u‖ < ρ →
      pastPlaqueCode s c r T (x (axis u).1 (axis u).2 • q) =
        pastPlaqueCode s c r T q := by
  classical
  have hm (i : ι) := ae_all_time_boundary_margin μ (measurable_safetyRadius (c i))
    hT hθ0 (hboundary i)
  filter_upwards [ae_all_iff.mpr hm] with q hq
  choose ρ hρ hρmargin using hq
  let R : Unit ⊕ ι → ℝ := Sum.elim (fun _ => a) ρ
  have hR : ∀ i, 0 < R i := by
    intro i
    rcases i with u | i
    · exact ha
    · exact hρ i
  have hne : (Finset.univ : Finset (Unit ⊕ ι)).Nonempty := ⟨Sum.inl (),Finset.mem_univ _⟩
  let R₀ : ℝ := Finset.univ.inf' hne R
  have hR₀ : 0 < R₀ := (Finset.lt_inf'_iff hne).mpr (fun i _ => hR i)
  have hRa : R₀ ≤ a := Finset.inf'_le R (Finset.mem_univ (Sum.inl ()))
  have hRi (i : ι) : R₀ ≤ ρ i := Finset.inf'_le R (Finset.mem_univ (Sum.inr i))
  refine ⟨R₀,hR₀,?_⟩
  intro u hu
  funext n i
  dsimp only [pastPlaqueCode]
  rw [hconj]
  apply plaqueCode_root_shift s axis hs (c i) ((T^[n]) q) (D n u) (ha.trans (har i))
  · have hn : ‖axis (D n u)‖ ≤ ‖u‖ :=
      (hcontract n u).trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (pow_le_one₀ hθ0.le hθ1) (norm_nonneg u))
    exact hn.trans ((hu.trans_le hRa).trans (har i)).le
  · calc
      ‖axis (D n u)‖ ≤ θ^n*‖u‖ := hcontract n u
      _ < θ^n*R₀ := mul_lt_mul_of_pos_left hu (pow_pos hθ0 n)
      _ ≤ θ^n*ρ i := mul_le_mul_of_nonneg_left (hRi i) (pow_nonneg hθ0.le n)
      _ = ρ i*θ^n := mul_comm _ _
      _ ≤ |safetyRadius (c i) ((T^[n]) q)-r i| := hρmargin i n

end Code

end VV.BBEKLeafEntropySubordinate
