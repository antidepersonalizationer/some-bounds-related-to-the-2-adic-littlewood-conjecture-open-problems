import VV.Entropy.AverageEntropy
import VV.Entropy.UniformEntropy
import VV.Entropy.SeparatedSequence
import VV.Entropy.SmallPartition
import VV.Entropy.KSEntropySystem

/-!
The positive-entropy direction of the variational principle.  Starting from
finite separated sets, we construct their uniform probabilities, pass to an
invariant weak limit of orbit averages, and use the finite blocking estimate
and a boundary-null partition to obtain strictly positive actual KS entropy.
-/

noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology ENNReal

namespace ErgodicTheory.Entropy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

theorem exists_pos_ksEntropy_of_separated {T : X → X} (hT : Continuous T)
    (w : SeparatedEntropyWitness T) :
    ∃ μ : ProbabilityMeasure X,
      ∃ hμT : MeasurePreserving T (μ : Measure X) (μ : Measure X), 0 < ksEntropy hμT := by
  classical
  let ν : ℕ → ProbabilityMeasure X := fun j =>
    ⟨(PMF.uniformOfFinset (w.points j) (w.points_nonempty j)).toMeasure, inferInstance⟩
  obtain ⟨μ, φ, hφ, hlim, hμT⟩ := exists_invariant_orbitAverage_subseq hT
    w.time w.time_pos w.time_strictMono.tendsto_atTop ν
  obtain ⟨m, P, hboundary, hmesh⟩ := exists_small_null_frontier_partition
    (μ : Measure X) w.scale_pos
  haveI : Nonempty X := ⟨(w.points_nonempty 0).choose⟩
  haveI : Nonempty (Fin m) := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have hx : x ∈ ⋃ i, P.cells i := by rw [P.cover]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i⟩
  have htime : Tendsto (fun j => w.time (φ j)) atTop atTop :=
    w.time_strictMono.tendsto_atTop.comp hφ.tendsto_atTop
  have hblock : ∀ q : ℕ, 0 < q →
      (q : ℝ) * w.rate ≤ blockEntropy (μ : Measure X) P T q := by
    intro q hq
    have hevent : ∀ᶠ j : ℕ in atTop,
        (q : ℝ) * w.rate ≤
          blockEntropy (orbitAverage hT.measurable (w.time (φ j))
            (w.time_pos (φ j)) (ν (φ j)) : Measure X) P T q +
              (3 * (q : ℝ)^2 * Real.log (Fintype.card (Fin m))) / w.time (φ j) := by
      filter_upwards [htime.eventually (eventually_ge_atTop q)] with j hj
      have hfinite := blockEntropy_le_average hT.measurable (w.time (φ j))
        (w.time_pos (φ j)) (ν (φ j)) P hq hj
      have huniform : blockEntropy (ν (φ j) : Measure X) P T (w.time (φ j)) =
          Real.log (w.points (φ j)).card :=
        blockEntropy_uniform_eq_log_card P hT.measurable (w.points (φ j))
          (w.points_nonempty (φ j)) (w.time (φ j)) hmesh (w.separated (φ j))
      rw [huniform] at hfinite
      have hr := mul_le_mul_of_nonneg_left (w.card_rate (φ j))
        (show (0 : ℝ) ≤ q by positivity)
      have hnR : (0 : ℝ) < w.time (φ j) := by exact_mod_cast w.time_pos (φ j)
      have hd : (q : ℝ) * w.rate ≤
          ((w.time (φ j) : ℝ) * blockEntropy
            (orbitAverage hT.measurable (w.time (φ j)) (w.time_pos (φ j))
              (ν (φ j)) : Measure X) P T q +
                3 * (q : ℝ)^2 * Real.log (Fintype.card (Fin m))) / w.time (φ j) :=
        (le_div_iff₀ hnR).mpr (by nlinarith)
      simpa only [add_div, mul_div_cancel_left₀ _ hnR.ne'] using hd
    have hc := entropy_dynJoin_tendsto P hlim hT hμT hboundary q
    have he := (tendsto_const_div_atTop_nhds_zero_nat
      (3 * (q : ℝ)^2 * Real.log (Fintype.card (Fin m)))).comp htime
    have hresult := ge_of_tendsto (hc.add he) hevent
    simpa only [add_zero] using hresult
  let Q := P.toMeasurePartition (μ : Measure X)
  have hrate : w.rate ≤ ksEntropyPartition hμT Q := by
    apply ge_of_tendsto (tendsto_ksEntropySeq hμT Q)
    filter_upwards [eventually_gt_atTop 0] with q hq
    apply (le_div_iff₀ (show (0 : ℝ) < q by exact_mod_cast hq)).mpr
    have h := hblock q hq
    simpa only [mul_comm] using h
  refine ⟨μ,hμT,?_⟩
  have hpositive : 0 < ksEntropyPartition hμT Q := w.rate_pos.trans_le hrate
  exact (EReal.coe_pos.mpr hpositive).trans_le (le_ksEntropy hμT Q)

/-- Positive mathlib topological entropy produces a genuinely invariant
probability measure with strictly positive Kolmogorov--Sinai entropy. -/
theorem exists_pos_ksEntropy_of_pos_coverEntropy {T : X → X} (hT : Continuous T)
    (hpos : 0 < Dynamics.coverEntropy T univ) :
    ∃ μ : ProbabilityMeasure X,
      ∃ hμT : MeasurePreserving T (μ : Measure X) (μ : Measure X), 0 < ksEntropy hμT := by
  classical
  by_cases hX : Nonempty X
  · letI := hX
    obtain ⟨w⟩ := separatedEntropyWitness_of_pos T hpos
    exact exists_pos_ksEntropy_of_separated hT w
  · haveI : IsEmpty X := not_nonempty_iff.mp hX
    rw [Set.univ_eq_empty_iff.mpr inferInstance, Dynamics.coverEntropy_empty] at hpos
    exact False.elim (not_lt_of_ge bot_le hpos)

end ErgodicTheory.Entropy

