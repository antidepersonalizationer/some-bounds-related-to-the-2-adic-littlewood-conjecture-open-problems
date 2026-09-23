import VV.BBEKExpandedPlaques
import VV.BBEKLocalRootFamily

/-! Measurable expanding local conditional measures on the actual compactly
trapped quotient. These are local pieces, not yet a global leaf measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped ENNReal
namespace VV.BBEKSelectedPlaques
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKExpandedPlaques BBEKLocalRootFamily BBEKLeafwiseTrapped

/-- The chosen chart at the inverse iterate, transported back to the point. -/
def selectedChart (c : ℕ → Chart) (index : X → ℕ) (t : ℝ) (n : ℕ) (q : X) : Chart :=
  expandedChart (c (index (((psi t 1)⁻¹)^n • q))) t n

def selectedMeasure (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℕ → Chart) (index : X → ℕ) (t : ℝ) (n : ℕ) (q : X) : Measure Leaf :=
  localMeasure μ (selectedChart c index t n q) q

set_option maxHeartbeats 1000000 in
theorem measurable_selectedMeasure (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℕ → Chart) {index : X → ℕ} (hi : Measurable index) (t : ℝ) (n : ℕ) :
    Measurable (selectedMeasure μ c index t n) := by
  have hf : Measurable (fun p : X × ℕ => localMeasure μ (expandedChart (c p.2) t n) p.1) :=
    measurable_from_prod_countable (fun k => measurable_localMeasure μ (expandedChart (c k) t n))
  exact hf.comp (measurable_id.prodMk (hi.comp (continuous_const_smul _).measurable))

instance selectedMeasure_probability (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℕ → Chart) (index : X → ℕ) (t : ℝ) (n : ℕ) (q : X) :
    IsProbabilityMeasure (selectedMeasure μ c index t n q) :=
  localMeasure_probability μ _ q

theorem selectedChart_safe {K : Set X} (c : ℕ → Chart) (index : X → ℕ)
    {r t : ℝ} (hr : 0 < r) (ht : Real.log 2 ≤ t)
    (hs : ∀ z ∈ K, quotientCoordinates (c (index z)).base
        (chartCoordinates (c (index z)) z) = z ∧
      ∀ u : Leaf, ‖u‖ ≤ r → leafShift (chartCoordinates (c (index z)) z) u ∈
        (c (index z)).domain)
    (q : X) (hq : ∀ n : ℕ, ((psi t 1)⁻¹)^n • q ∈ K) (n : ℕ) :
    quotientCoordinates (selectedChart c index t n q).base
        (chartCoordinates (selectedChart c index t n q) q) = q ∧
      ∀ u : Leaf, ‖u‖ ≤ (4 : ℝ)^n*r →
        leafShift (chartCoordinates (selectedChart c index t n q) q) u ∈
          (selectedChart c index t n q).domain := by
  let z := ((psi t 1)⁻¹)^n • q
  let d := c (index z)
  let p := chartCoordinates d z
  obtain ⟨hp,hpS⟩ := hs z (hq n)
  have hpq : quotientCoordinates (expandedChart d t n).base ((psiParams t 1)^[n] p) = q := by
    rw [expanded_quotient,hp,← mul_smul,inv_pow,mul_inv_cancel,one_smul]
  have hsafe := expanded_contains_ball d ht n p hpS
  have hpdom : (psiParams t 1)^[n] p ∈ (expandedChart d t n).domain := by
    simpa only [leafShift_zero] using hsafe 0 (by simp only [norm_zero]; positivity)
  have hcoords : chartCoordinates (expandedChart d t n) q = (psiParams t 1)^[n] p := by
    rw [← hpq]
    exact chartCoordinates_apply _ ⟨_,hpdom⟩
  change quotientCoordinates (expandedChart d t n).base
      (chartCoordinates (expandedChart d t n) q) = q ∧
      ∀ u : Leaf, ‖u‖ ≤ (4 : ℝ)^n*r →
        leafShift (chartCoordinates (expandedChart d t n) q) u ∈ (expandedChart d t n).domain
  rw [hcoords]
  exact ⟨hpq,hsafe⟩

/-- One conull set supports every selected local measure on every centered
positive-radius ball. Countably many actual charts, rather than an uncountable
choice of exceptional sets, are used in the proof. -/
theorem ae_selectedMeasure_ball_pos (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    (c : ℕ → Chart) (index : X → ℕ) {r t : ℝ} (hr : 0 < r)
    (ht : Real.log 2 ≤ t)
    (hs : ∀ z ∈ K, quotientCoordinates (c (index z)).base
        (chartCoordinates (c (index z)) z) = z ∧
      ∀ u : Leaf, ‖u‖ ≤ r → leafShift (chartCoordinates (c (index z)) z) u ∈
        (c (index z)).domain)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∀ᵐ q ∂μ, ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      0 < selectedMeasure μ c index t n q (ball 0 ε) := by
  have hall : ∀ᵐ q ∂μ, ∀ n k : ℕ,
      q ∈ (expandedChart (c k) t n).image → ∀ ε : ℝ, 0 < ε →
      0 < localMeasure μ (expandedChart (c k) t n) q (ball 0 ε) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact (ae_restrict_iff' (expandedChart (c k) t n).isOpen_image.measurableSet).mp
      (ae_localMeasure_ball_pos μ _)
  filter_upwards [ae_compact_inverse_orbit μ hK hμK (psi t 1) hT,hall] with q hq hpos
  intro n ε hε
  have hc := selectedChart_safe c index hr ht hs q hq n
  apply hpos n (index (((psi t 1)⁻¹)^n • q)) _ ε hε
  refine ⟨chartCoordinates (selectedChart c index t n q) q,?_,hc.1⟩
  simpa only [leafShift_zero] using hc.2 0 (by simp only [norm_zero]; positivity)

/-- Actual simultaneously measurable positive local pieces on expanding
plaques, constructed for every compactly supported invariant probability. -/
theorem exists_measurable_expanding_local_family (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : ℕ → Chart, ∃ index : X → ℕ,
      Measurable index ∧ (∀ n, Measurable (selectedMeasure μ c index t n)) ∧
      (∀ᵐ q ∂μ, ∀ n : ℕ,
        quotientCoordinates (selectedChart c index t n q).base
            (chartCoordinates (selectedChart c index t n q) q) = q ∧
        (∀ u : Leaf, ‖u‖ ≤ (4 : ℝ)^n*r →
          leafShift (chartCoordinates (selectedChart c index t n q) q) u ∈
            (selectedChart c index t n q).domain) ∧
        ∀ ε : ℝ, 0 < ε → 0 < selectedMeasure μ c index t n q (ball 0 ε)) := by
  obtain ⟨r,hr,c,index,hi,_,hs⟩ := compact_measurable_safe_selection hK
  refine ⟨r,hr,c,index,hi,fun n => measurable_selectedMeasure μ c hi t n,?_⟩
  filter_upwards [ae_compact_inverse_orbit μ hK hμK (psi t 1) hT,
    ae_selectedMeasure_ball_pos μ hK hμK c index hr ht hs hT] with q hq hpos
  intro n
  exact ⟨(selectedChart_safe c index hr ht hs q hq n).1,
    (selectedChart_safe c index hr ht hs q hq n).2,hpos n⟩

end VV.BBEKSelectedPlaques


