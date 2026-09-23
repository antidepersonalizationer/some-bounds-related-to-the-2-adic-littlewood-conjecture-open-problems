import VV.Entropy.MixtureEntropy

/-! Two-component convex mixtures, with an explicit affine entropy endpoint. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ErgodicTheory.Entropy
variable {X : Type*} [MeasurableSpace X]

def binaryMixture (a b : ℝ≥0) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure X) : ProbabilityMeasure X :=
  probabilityMixture ![a,b] (by simpa only [Fin.sum_univ_two] using hab) ![μ,ν]

theorem binaryMixture_coe (a b : ℝ≥0) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure X) :
    (binaryMixture a b hab μ ν : Measure X) =
      (a : ℝ≥0∞) • (μ : Measure X) + (b : ℝ≥0∞) • (ν : Measure X) := by
  simp [binaryMixture, probabilityMixture_coe, mixtureMeasure, Fin.sum_univ_two]

theorem binaryMixture_measurePreserving (a b : ℝ≥0) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure X) {T : X → X}
    (hμ : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (hν : MeasurePreserving T (ν : Measure X) (ν : Measure X)) :
    MeasurePreserving T (binaryMixture a b hab μ ν : Measure X)
      (binaryMixture a b hab μ ν : Measure X) := by
  apply probabilityMixture_measurePreserving _ _ _ hμ.measurable
  intro i
  fin_cases i
  · exact hμ
  · exact hν

theorem ksEntropy_binaryMixture (a b : ℝ≥0) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure X) {T : X → X}
    (hμ : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (hν : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (r s : ℝ) (hr : ksEntropy hμ = (r : EReal)) (hs : ksEntropy hν = (s : EReal)) :
    ksEntropy (binaryMixture_measurePreserving a b hab μ ν hμ hν) =
      (((a : ℝ) * r + (b : ℝ) * s : ℝ) : EReal) := by
  let hm : ∀ i : Fin 2, MeasurePreserving T ((![μ,ν] i : ProbabilityMeasure X) : Measure X)
      ((![μ,ν] i : ProbabilityMeasure X) : Measure X) := by
    intro i
    fin_cases i
    · exact hμ
    · exact hν
  have he : ∀ i : Fin 2, ksEntropy (hm i) = (![r,s] i : EReal) := by
    intro i
    fin_cases i
    · exact hr
    · exact hs
  have hh := ksEntropy_mixture_eq_weighted ![a,b]
    (by simpa only [Fin.sum_univ_two] using hab) ![μ,ν] hμ.measurable hm ![r,s] he
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hh

end ErgodicTheory.Entropy
