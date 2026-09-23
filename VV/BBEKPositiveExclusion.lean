import VV.BBEKPositiveFullDiagonal
import VV.BBEKReductiveConjugation

/-! The proper-reductive-orbit hypothesis of Theorem EL is verified for the
actual positive-entropy full-diagonal measure constructed from a failure of
zero box dimension. The excluded sets are literally g L(Q_S) Gamma, with
arbitrary g, not the different sets L(Q_S) g Gamma. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace VV.BBEKPositiveExclusion
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKReduction BBEKEntropyExpansion
open BBEKPositiveFullDiagonal BBEKRationalReductive BBEKReductiveConjugation
open P7BoxCover ErgodicTheory.Entropy

local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- Stronger than the periodic-orbit exclusion: every closed left translate
of the local points of a proper reductive rational group fails to have full
mass. No finite-volume premise about that closed orbit is needed. -/
def NoProperReductiveClosedOrbit (μ : Measure X) : Prop :=
  ∀ L : RationalMatrixGroup, L.IsProper → L.IsGeometricallyReductive →
    ∀ g : G, IsClosed (translatedOrbit L g) → μ (translatedOrbit L g) ≠ 1

theorem no_proper_reductive_closed_orbit_of_positive
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hK : μ (BBEKOrbit.K δ)=1)
    (hμT : MeasurePreserving (timeMap time0) μ μ) (hpos : 0 < ksEntropy hμT) :
    NoProperReductiveClosedOrbit μ := by
  intro L hproper hred g hclosed hfull
  have hz : ksEntropy hμT=0 :=
    translated_reductive_orbit_entropy_zero L hproper hred μ g hclosed hfull
      (BBEKMahler.compact_K hδ) hK time0 1
  rw [hz] at hpos
  exact lt_irrefl _ hpos

/-- A fully instantiated endpoint for the EL branch: the probability comes
from the existing entropy/averaging construction, is ergodic under all A,
has positive entropy at the literal designated time, and already satisfies
the proper-reductive periodic-orbit exclusion. No rigidity conclusion or
extra orbit-presentation conversion is assumed. -/
theorem exists_diagonal_positive_with_reductive_exclusion {δ : ℝ} (hδ : 0 < δ)
    (hbox : ¬ GeometricZeroUpperBox (trappedParameters δ)) :
    ∃ ν : ProbabilityMeasure X,
      ∃ _hA : SMulInvariantMeasure A X (ν : Measure X),
      ErgodicSMul A X (ν : Measure X) ∧
      (ν : Measure X) (BBEKOrbit.K δ)=1 ∧
      ∃ hνT : MeasurePreserving (timeMap time0) (ν : Measure X) (ν : Measure X),
        0 < ksEntropy hνT ∧ NoProperReductiveClosedOrbit (ν : Measure X) := by
  obtain ⟨ν,hA,hAE,hK,hνT,hpos⟩ := exists_diagonal_ergodic_pos_ksEntropy_supported_K hδ hbox
  letI : SMulInvariantMeasure A X (ν : Measure X) := hA
  letI : ErgodicSMul A X (ν : Measure X) := hAE
  exact ⟨ν,hA,hAE,hK,hνT,hpos,
    no_proper_reductive_closed_orbit_of_positive (ν : Measure X) hδ hK hνT hpos⟩

end VV.BBEKPositiveExclusion
