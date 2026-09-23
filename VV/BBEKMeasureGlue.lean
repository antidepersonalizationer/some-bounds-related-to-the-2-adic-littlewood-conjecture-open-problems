import VV.BBEKLeafwiseAtlas
import Mathlib.MeasureTheory.Measure.Regular

/-! Constructive countable gluing of agreeing local measures. This is the
measure-extension step needed after leaf-chart projective normalizations have
been matched. Agreement is used only on pairwise overlaps. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal Topology
namespace VV.BBEKMeasureGlue
variable {U : Type*} [MeasurableSpace U]

def glue (s : ℕ → Set U) (η : ℕ → Measure U) : Measure U :=
  Measure.sum (fun n => (η n).restrict (disjointed s n))

/-- The constructed sum really extends each of the local measures. -/
theorem glue_restrict (s : ℕ → Set U) (hs : ∀ n, MeasurableSet (s n))
    (hcover : ⋃ n, s n = univ) (η : ℕ → Measure U)
    (hagree : ∀ n m, (η n).restrict (s n ∩ s m) = (η m).restrict (s n ∩ s m))
    (k : ℕ) : (glue s η).restrict (s k) = (η k).restrict (s k) := by
  unfold glue
  rw [Measure.restrict_sum _ (hs k)]
  have he (n : ℕ) : ((η n).restrict (disjointed s n)).restrict (s k) =
      ((η k).restrict (disjointed s n)).restrict (s k) := by
    rw [Measure.restrict_restrict (hs k), Measure.restrict_restrict (hs k)]
    apply Measure.restrict_congr_mono _ (hagree n k)
    intro u hu
    exact ⟨disjointed_subset s n hu.2,hu.1⟩
  simp_rw [he]
  rw [← Measure.restrict_sum _ (hs k),
    ← Measure.restrict_iUnion (disjoint_disjointed s) (MeasurableSet.disjointed hs),
    iUnion_disjointed, hcover, Measure.restrict_univ]

theorem glue_unique (s : ℕ → Set U) (hs : ∀ n, MeasurableSet (s n))
    (hcover : ⋃ n, s n = univ) (η : ℕ → Measure U)
    (hagree : ∀ n m, (η n).restrict (s n ∩ s m) = (η m).restrict (s n ∩ s m))
    {ν : Measure U} (hν : ∀ n, ν.restrict (s n) = (η n).restrict (s n)) :
    ν = glue s η := by
  have hh : ν.restrict (⋃ n, s n) = (glue s η).restrict (⋃ n, s n) :=
    Measure.restrict_iUnion_congr.mpr (fun n => (hν n).trans (glue_restrict s hs hcover η hagree n).symm)
  simpa only [hcover, Measure.restrict_univ] using hh

theorem glue_apply_patch (s : ℕ → Set U) (hs : ∀ n, MeasurableSet (s n))
    (hcover : ⋃ n, s n = univ) (η : ℕ → Measure U)
    (hagree : ∀ n m, (η n).restrict (s n ∩ s m) = (η m).restrict (s n ∩ s m))
    (k : ℕ) : glue s η (s k) = η k (s k) := by
  have hh := congrArg (fun μ : Measure U => μ univ) (glue_restrict s hs hcover η hagree k)
  simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hh

/-- Finite local pieces on an open cover produce a locally finite measure. -/
theorem glue_locallyFinite [TopologicalSpace U] [OpensMeasurableSpace U]
    (s : ℕ → Set U) (hs : ∀ n, IsOpen (s n)) (hcover : ⋃ n, s n = univ)
    (η : ℕ → Measure U) [∀ n, IsFiniteMeasure (η n)]
    (hagree : ∀ n m, (η n).restrict (s n ∩ s m) = (η m).restrict (s n ∩ s m)) :
    IsLocallyFiniteMeasure (glue s η) := by
  constructor
  intro u
  have hu : u ∈ ⋃ n, s n := by rw [hcover]; trivial
  obtain ⟨n,hn⟩ := mem_iUnion.mp hu
  refine ⟨s n,(hs n).mem_nhds hn,?_⟩
  rw [glue_apply_patch s (fun n => (hs n).measurableSet) hcover η hagree]
  exact measure_lt_top _ _

/-- On the actual locally compact metrizable leaves, this construction is a
regular locally finite (Radon) measure, not merely a finitely additive object. -/
theorem glue_regular [PseudoMetricSpace U] [SigmaCompactSpace U] [BorelSpace U]
    (s : ℕ → Set U) (hs : ∀ n, IsOpen (s n)) (hcover : ⋃ n, s n = univ)
    (η : ℕ → Measure U) [∀ n, IsFiniteMeasure (η n)]
    (hagree : ∀ n m, (η n).restrict (s n ∩ s m) = (η m).restrict (s n ∩ s m)) :
    (glue s η).Regular := by
  letI := glue_locallyFinite s hs hcover η hagree
  infer_instance

end VV.BBEKMeasureGlue
