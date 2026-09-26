import VV.BBEKOneRootRecurrence

/-!
# Local invariance inherited from the actual full-root measure

A global leaf measure and its finite chart conditional probability agree
only after restriction and normalization. This file transfers invariance
on their common domain, without falsely asserting invariance of the entire
finite conditional probability. It does not yet glue the local identities
into invariance of the ambient quotient measure.
-/
noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped Topology ENNReal
namespace VV.BBEKOneRootLocalInvariance
open BBEKLeafwiseStabilizer BBEKDynamics BBEKQuotient BBEKGaussChart
open BBEKLeafwiseAtlas BBEKRootGrowingGlue BBEKOneRootGlobal
open BBEKOneRootCovariance

section Measure
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

omit [NormedAddCommGroup U] [BorelSpace U] [SecondCountableTopology U] in
/-- Recover the original local mass, including the positive normalizing
factor, from the normalized global restriction. -/
theorem mass_of_normalized_restriction (η P : Measure U) [IsFiniteMeasure P]
    {B S E : Set U} (hB : MeasurableSet B) (hBS : B ⊆ S)
    (hηB : η B = 1) (hres : η.restrict S = (P B)⁻¹ • P.restrict S)
    (hE : MeasurableSet E) (hES : E ⊆ S) : P E = P B * η E := by
  have heB := congrArg (fun ν : Measure U => ν B) hres
  simp only [Measure.restrict_apply hB, inter_eq_self_of_subset_left hBS,
    Measure.smul_apply, smul_eq_mul, hηB] at heB
  have hp : P B ≠ 0 := by
    intro hz
    simp only [hz, inv_zero, mul_zero] at heB
    exact one_ne_zero heB
  have heE := congrArg (fun ν : Measure U => ν E) hres
  simp only [Measure.restrict_apply hE, inter_eq_self_of_subset_left hES,
    Measure.smul_apply, smul_eq_mul] at heE
  rw [heE, ← mul_assoc, ENNReal.mul_inv_cancel hp (measure_ne_top P B), one_mul]

/-- A global leaf translation preserves the finite chart kernel on every
measurable set for which both the set and its translate lie in the common
restriction domain. No invariance outside the chart is inferred. -/
theorem local_preimage_mass_eq (η P : Measure U) [IsFiniteMeasure P]
    {B S E : Set U} (hB : MeasurableSet B) (hBS : B ⊆ S)
    (hηB : η B = 1) (hres : η.restrict S = (P B)⁻¹ • P.restrict S)
    (u : U) (hu : u ∈ translationStabilizer η)
    (hE : MeasurableSet E) (hES : E ⊆ S) (hpre : (u + ·) ⁻¹' E ⊆ S) :
    P ((u + ·) ⁻¹' E) = P E := by
  have htr : Measurable (fun v : U => u + v) := measurable_const.add measurable_id
  have hpreEq := mass_of_normalized_restriction η P hB hBS hηB hres
    (hE.preimage htr) hpre
  have htargetEq := mass_of_normalized_restriction η P hB hBS hηB hres hE hES
  calc
    P ((u + ·) ⁻¹' E) = P B * η ((u + ·) ⁻¹' E) := hpreEq
    _ = P B * η E := ?_
    _ = P E := htargetEq.symm
  · have he := congrArg (fun ν : Measure U => ν E) hu
    change translate u η E = η E at he
    rw [translate_apply u η hE] at he
    rw [he]

/-- Equality as restricted measures on the overlap of the chart domain and
its translated copy. This is the local identity a gluing theorem must use. -/
theorem map_restrict_overlap_eq (η P : Measure U) [IsFiniteMeasure P]
    {B S : Set U} (hB : MeasurableSet B) (hS : MeasurableSet S) (hBS : B ⊆ S)
    (hηB : η B = 1) (hres : η.restrict S = (P B)⁻¹ • P.restrict S)
    (u : U) (hu : u ∈ translationStabilizer η) :
    (P.map (u + ·)).restrict (S ∩ ((-u + ·) ⁻¹' S)) =
      P.restrict (S ∩ ((-u + ·) ⁻¹' S)) := by
  apply Measure.ext
  intro E hE
  rw [Measure.restrict_apply hE, Measure.restrict_apply hE]
  have hD : MeasurableSet (E ∩ (S ∩ ((-u + ·) ⁻¹' S))) :=
    hE.inter (hS.inter (hS.preimage (measurable_const.add measurable_id)))
  have htr : Measurable (fun v : U => u + v) := measurable_const.add measurable_id
  rw [Measure.map_apply htr hD]
  apply local_preimage_mass_eq η P hB hBS hηB hres u hu hD
  · exact fun _ hx => hx.2.1
  · intro v hv
    have hh := hv.2.2
    simpa only [mem_preimage, neg_add_cancel_left] using hh
end Measure

section Canonical
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U] [SigmaCompactSpace U]

omit [BorelSpace B] in
/-- The overlap identity for the literal selected chart probabilities of a
canonical root family. The charts and measurable selection are the same
ones that construct the globally glued measure. -/
theorem canonical_local_invariance
    (s : GroupParams ≃ₜ B × U) (μ : Measure X) [IsFiniteMeasure μ]
    {t r : ℝ} (hr : 0 < r) (η : X → Measure U)
    (hcanonical : IsConstructedRootFamily s μ t r η)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (htop : ∀ᵐ q ∂μ, translationStabilizer (η q) = ⊤) :
    ∃ c : ℕ → Chart, ∃ index : X → ℕ, Measurable index ∧
      η = globalMeasureWith s μ c index t r ∧
      (∀ᵐ q ∂μ, ∀ n : ℕ, ∀ u : U,
        ((selectedMeasureWith s μ c index t n q).map (u + ·)).restrict
            (growingBall r n ∩ ((-u + ·) ⁻¹' growingBall r n)) =
          (selectedMeasureWith s μ c index t n q).restrict
            (growingBall r n ∩ ((-u + ·) ⁻¹' growingBall r n))) := by
  obtain ⟨c, index, hi, hη, hrestrict⟩ := hcanonical
  refine ⟨c, index, hi, hη, ?_⟩
  filter_upwards [hrestrict, hnormal, htop] with q hq hn ht n u
  have hbase : ball (0 : U) r ⊆ growingBall r n := by
    simpa only [growingBall, pow_zero, one_mul] using
      growingBall_mono hr.le (Nat.zero_le n)
  apply map_restrict_overlap_eq (η q) (selectedMeasureWith s μ c index t n q)
    isOpen_ball.measurableSet (growingBall_open r n).measurableSet hbase hn (hq n).1 u
  rw [ht]
  trivial
end Canonical

end VV.BBEKOneRootLocalInvariance
