import VV.BBEKEntropySeed
import VV.BBEKPsiEntropy

/-! The actual cone averages are ambient diagonal mixtures and preserve the seed entropy. -/
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology
namespace VV.BBEKConeEntropy
open BBEKDynamics BBEKQuotient BBEKTopology BBEKConeGenerators
open BBEKEntropyTrapped BBEKEntropyNets BBEKEntropyExpansion BBEKConeAverage
open BBEKEntropySeed BBEKPsiEntropy BBEKVariational BBEKReduction P7BoxCover
open ErgodicTheory.Entropy

def ambientGenerator (i : Fin 3) : X ≃ₜ X := psiAction (generator i).1 (generator i).2

theorem ambientGenerator_commute_time (i : Fin 3) :
    Function.Commute (ambientGenerator i) (timeMap time0) :=
  psiAction_commute (generator i).1 time0 (generator i).2 1

theorem toQuotient_orbitAverage (δ : ℝ) (i : Fin 3) (n : ℕ) (hn : 0 < n)
    (ν : ProbabilityMeasure (trappedQuotient δ)) :
    toQuotient δ (orbitAverage (continuous_generatorMap δ i).measurable n hn ν) =
      orbitAverage (ambientGenerator i).measurable n hn (toQuotient δ ν) :=
  orbitAverage_map_semiconj (continuous_generatorMap δ i).measurable
    (ambientGenerator i).measurable measurable_subtype_coe (fun _ => rfl) n hn ν

/-- Equality of the literal subtype cone average and the literal ambient triple average. -/
theorem toQuotient_coneAverage (δ : ℝ) (n : ℕ) (hn : 0 < n)
    (ν : ProbabilityMeasure (trappedQuotient δ)) :
    toQuotient δ (coneAverage δ n hn ν) =
      tripleAverage (ambientGenerator 0).measurable (ambientGenerator 1).measurable
        (ambientGenerator 2).measurable n hn (toQuotient δ ν) := by
  unfold coneAverage tripleAverage
  rw [toQuotient_orbitAverage, toQuotient_orbitAverage, toQuotient_orbitAverage]

theorem coneAverage_timeInvariant (δ : ℝ) (n : ℕ) (hn : 0 < n)
    (ν : ProbabilityMeasure (trappedQuotient δ))
    (hν : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (ν : Measure _) (ν : Measure _)) :
    MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (coneAverage δ n hn ν : Measure _) (coneAverage δ n hn ν : Measure _) :=
  tripleAverage_measurePreserving ν hν
    (continuous_generatorMap δ 0).measurable (continuous_generatorMap δ 1).measurable
    (continuous_generatorMap δ 2).measurable
    (generatorMap_commute δ 0 2) (generatorMap_commute δ 1 2) (generatorMap_commute δ 2 2) n hn

/-- Both the compact subtype dynamics and ambient dynamics carry the same unchanged entropy. -/
theorem ksEntropy_coneAverage (δ : ℝ) (n : ℕ) (hn : 0 < n)
    (ν : ProbabilityMeasure (trappedQuotient δ))
    (hν : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (ν : Measure _) (ν : Measure _)) :
    ksEntropy (coneAverage_timeInvariant δ n hn ν hν) = ksEntropy hν := by
  obtain ⟨hbase, hbaseE⟩ := toQuotient_entropy δ ν hν
  obtain ⟨havg, havgE⟩ := toQuotient_entropy δ (coneAverage δ n hn ν)
    (coneAverage_timeInvariant δ n hn ν hν)
  let hcube := tripleAverage_measurePreserving (toQuotient δ ν) hbase
    (ambientGenerator 0).measurable (ambientGenerator 1).measurable (ambientGenerator 2).measurable
    (ambientGenerator_commute_time 0) (ambientGenerator_commute_time 1)
    (ambientGenerator_commute_time 2) n hn
  have hsame := ksEntropy_eq_of_probability_eq (toQuotient_coneAverage δ n hn ν) havg hcube
  have hcubeE := ksEntropy_tripleAverage_eq (toQuotient δ ν) hbase
    (ambientGenerator 0).measurableEmbedding (ambientGenerator 1).measurableEmbedding
    (ambientGenerator 2).measurableEmbedding (ambientGenerator_commute_time 0)
    (ambientGenerator_commute_time 1) (ambientGenerator_commute_time 2) n hn
  exact havgE.symm.trans (hsame.trans (hcubeE.trans hbaseE))

/-- The positive variational seed yields genuine cone averages with one fixed positive entropy. -/
theorem exists_pos_ksEntropy_coneAverages {δ : ℝ} (hδ : 0 < δ)
    (hbox : ¬ GeometricZeroUpperBox (trappedParameters δ)) :
    ∃ ν : ProbabilityMeasure (trappedQuotient δ),
      ∃ hν : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
        (ν : Measure _) (ν : Measure _),
        0 < ksEntropy hν ∧ ∀ (n : ℕ) (hn : 0 < n),
          ksEntropy (coneAverage_timeInvariant δ n hn ν hν) = ksEntropy hν := by
  obtain ⟨ν,hν,hpos⟩ := exists_trapped_pos_ksEntropy hδ hbox
  exact ⟨ν,hν,hpos,fun n hn => ksEntropy_coneAverage δ n hn ν hν⟩

end VV.BBEKConeEntropy
