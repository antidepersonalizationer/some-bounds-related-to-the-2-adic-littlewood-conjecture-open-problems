import VV.BBEKEntropySemicontinuity
import VV.BBEKEntropySeed
import VV.BBEKCompactPreservation
import VV.Entropy.CompactAverageEntropy

/-! The actual compact diagonal Haar average on the quotient retains KS entropy.
The average is identified with the product-measure construction in Section 5. -/

noncomputable section
open Set MeasureTheory Function
open scoped Topology

namespace VV.BBEKCompactEntropy
open BBEKDynamics BBEKQuotient BBEKTopology BBEKDiagonal BBEKDiagonalAverage
open BBEKEntropyNets BBEKEntropyTrapped BBEKEntropyExpansion BBEKCompactPreservation
open BBEKConeAverage BBEKEntropySeed BBEKFiniteBowen
open ErgodicTheory.Entropy

local instance : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩

theorem compact_smul_mem_trapped (δ : ℝ) (k : K) {q : X}
    (hq : q ∈ trappedQuotient δ) : k • q ∈ trappedQuotient δ := by
  rintro _ ⟨t,n,hc,rfl⟩
  have hm := hq (show psi t n • q ∈ coneOrbit q from ⟨t,n,hc,rfl⟩)
  have he : psi t n • (k • q) = k • (psi t n • q) := by
    change psi t n • ((k:G) • q) = (k:G) • (psi t n • q)
    rw [← mul_smul,← mul_smul,(psi_commute_K t n k).eq]
  rw [he]
  exact (compact_smul_mem_K_iff k _ δ).mpr hm

def compactMap (δ : ℝ) (k : K) (q : trappedQuotient δ) : trappedQuotient δ :=
  ⟨k • q.val, compact_smul_mem_trapped δ k q.property⟩

theorem continuous_compactMap (δ : ℝ) :
    Continuous (fun p : K × trappedQuotient δ => compactMap δ p.1 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

def compactHomeomorph (δ : ℝ) (k : K) : trappedQuotient δ ≃ₜ trappedQuotient δ where
  toFun := compactMap δ k
  invFun := compactMap δ k⁻¹
  left_inv q := by apply Subtype.ext; change k⁻¹ • (k • q.val) = q.val; simp
  right_inv q := by apply Subtype.ext; change k • (k⁻¹ • q.val) = q.val; simp
  continuous_toFun := (continuous_compactMap δ).comp (continuous_const.prodMk continuous_id)
  continuous_invFun := (continuous_compactMap δ).comp (continuous_const.prodMk continuous_id)

theorem compactMap_commute (δ : ℝ) (k : K) :
    Function.Commute (compactMap δ k) (restrictedTimeMap (trappedTimeForward δ)) := by
  intro q
  apply Subtype.ext
  change (k:G) • (psi time0 1 • q.val) = psi time0 1 • ((k:G) • q.val)
  rw [← mul_smul,← mul_smul,(psi_commute_K time0 1 k).eq]

def compactHaar : ProbabilityMeasure K :=
  ⟨BBEKMeasureAverage.haarProbability, inferInstance⟩

def compactAverage (δ : ℝ) (μ : ProbabilityMeasure (trappedQuotient δ)) :
    ProbabilityMeasure (trappedQuotient δ) :=
  familyAverage (continuous_compactMap δ).measurable compactHaar μ

theorem compactAverage_timeInvariant (δ : ℝ) (μ : ProbabilityMeasure (trappedQuotient δ))
    (hμT : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (μ : Measure _) (μ : Measure _)) :
    MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (compactAverage δ μ : Measure _) (compactAverage δ μ : Measure _) :=
  familyAverage_measurePreserving (continuous_compactMap δ).measurable compactHaar μ hμT
    (compactMap_commute δ)

theorem toQuotient_compactAverage (δ : ℝ) (μ : ProbabilityMeasure (trappedQuotient δ)) :
    (toQuotient δ (compactAverage δ μ) : Measure X) =
      averaged (toQuotient δ μ : Measure X) := by
  change Measure.map Subtype.val (Measure.map (fun p => compactMap δ p.1 p.2)
      ((compactHaar : Measure K).prod (μ : Measure (trappedQuotient δ)))) =
    Measure.map (fun p : K × X => p.1 • p.2)
      ((compactHaar : Measure K).prod (Measure.map Subtype.val (μ : Measure (trappedQuotient δ))))
  rw [Measure.map_map measurable_subtype_coe (continuous_compactMap δ).measurable]
  rw [← Measure.map_id (μ := (compactHaar : Measure K)),
    Measure.map_prod_map _ _ measurable_id measurable_subtype_coe,
    Measure.map_map (measurable_fst.smul measurable_snd) (measurable_id.prodMap measurable_subtype_coe)]
  simp only [Measure.map_id]
  rfl

/-- Haar averaging over the literal compact norm-one diagonal group cannot
decrease the designated entropy on the compact trapped model. -/
theorem ksEntropy_le_compactAverage {δ : ℝ} (hδ : 0 < δ)
    (μ : ProbabilityMeasure (trappedQuotient δ))
    (hμT : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (μ : Measure _) (μ : Measure _)) :
    ksEntropy hμT ≤ ksEntropy (compactAverage_timeInvariant δ μ hμT) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace (trappedQuotient δ) :=
    isCompact_iff_compactSpace.mp (compact_trappedQuotient hδ)
  have htime : 0 < time0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans time0_gt_log_two
  obtain ⟨r,hr,hcover⟩ := compact_uniformBowenCover (compact_trappedQuotient hδ)
    htime (trappedTimeForward δ)
  exact ksEntropy_le_familyAverage (continuous_compactMap δ) compactHaar μ
    (restrictedTimeMap_continuous (trappedTimeForward δ)) hμT
    (fun k => (compactHomeomorph δ k).measurableEmbedding) (compactMap_commute δ) hr hcover

/-- This is the actual ambient average from BBEK Section 5, with its time
invariance proved and its full KS entropy bounded below by the original. -/
theorem ksEntropy_le_averaged {δ : ℝ} (hδ : 0 < δ)
    (μ : ProbabilityMeasure (trappedQuotient δ))
    (hμT : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (μ : Measure _) (μ : Measure _)) :
    ∃ hνT : MeasurePreserving (timeMap time0)
      (averaged (toQuotient δ μ : Measure X)) (averaged (toQuotient δ μ : Measure X)),
      ksEntropy hμT ≤ ksEntropy hνT := by
  obtain ⟨hνT,he⟩ := toQuotient_entropy δ (compactAverage δ μ)
    (compactAverage_timeInvariant δ μ hμT)
  rw [toQuotient_compactAverage] at hνT
  refine ⟨hνT,?_⟩
  have hbound := ksEntropy_le_compactAverage hδ μ hμT
  rw [← he] at hbound
  simpa only [toQuotient_compactAverage] using hbound

end VV.BBEKCompactEntropy
