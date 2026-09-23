import VV.BBEKTopology
import VV.Entropy.OrbitMixture

/-! Entropy invariance for the actual BBEK diagonal action and its finite averages. -/
noncomputable section
open MeasureTheory Function
open ErgodicTheory.Entropy
namespace VV.BBEKPsiEntropy
open BBEKDynamics BBEKQuotient BBEKTopology
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The concrete diagonal element acts by a homeomorphism of the arithmetic quotient. -/
def psiAction (t : ℝ) (n : ℤ) : X ≃ₜ X := Homeomorph.smul (psi t n)

theorem psiAction_commute (t s : ℝ) (n m : ℤ) :
    Function.Commute (psiAction t n) (psiAction s m) := by
  intro x
  change psi t n • (psi s m • x) = psi s m • (psi t n • x)
  rw [← mul_smul, ← mul_smul, ← psi_add, ← psi_add, add_comm t s, add_comm n m]

theorem psiTranslate_measurePreserving (ν : ProbabilityMeasure X)
    (t s : ℝ) (n m : ℤ)
    (hν : MeasurePreserving (psiAction t n) (ν : Measure X) (ν : Measure X)) :
    MeasurePreserving (psiAction t n)
      (ν.map (psiAction s m).measurable.aemeasurable : Measure X)
      (ν.map (psiAction s m).measurable.aemeasurable : Measure X) :=
  measurePreserving_map_commute ν hν (psiAction s m).measurable (psiAction_commute s t m n)

/-- Pushforward along any actual diagonal parameter preserves the full KS entropy. -/
theorem ksEntropy_psiTranslate (ν : ProbabilityMeasure X)
    (t s : ℝ) (n m : ℤ)
    (hν : MeasurePreserving (psiAction t n) (ν : Measure X) (ν : Measure X)) :
    ksEntropy (psiTranslate_measurePreserving ν t s n m hν) = ksEntropy hν :=
  ksEntropy_map_commuting_embedding ν hν (psiAction s m).measurableEmbedding
    (psiAction_commute s t m n)

theorem psiAverage_measurePreserving (ν : ProbabilityMeasure X)
    (t s : ℝ) (n m : ℤ)
    (hν : MeasurePreserving (psiAction t n) (ν : Measure X) (ν : Measure X))
    (N : ℕ) (hN : 0 < N) :
    MeasurePreserving (psiAction t n)
      (orbitAverage (psiAction s m).measurable N hN ν : Measure X)
      (orbitAverage (psiAction s m).measurable N hN ν : Measure X) :=
  orbitAverage_measurePreserving ν hν (psiAction s m).measurable
    (psiAction_commute s t m n) N hN

/-- The concrete finite diagonal average loses no entropy, including for infinite entropy. -/
theorem ksEntropy_psiAverage (ν : ProbabilityMeasure X)
    (t s : ℝ) (n m : ℤ)
    (hν : MeasurePreserving (psiAction t n) (ν : Measure X) (ν : Measure X))
    (N : ℕ) (hN : 0 < N) :
    ksEntropy (psiAverage_measurePreserving ν t s n m hν N hN) = ksEntropy hν :=
  ksEntropy_orbitAverage_eq ν hν (psiAction s m).measurableEmbedding
    (psiAction_commute s t m n) N hN

end VV.BBEKPsiEntropy
