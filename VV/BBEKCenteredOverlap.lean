import VV.BBEKActualKernelOverlap

/-!
# Recentring compatible local leaf measures

An arithmetic chart transition translates the leaf coordinate.  The local
conditional probabilities on an overlap are normalized restrictions of two
larger leaf measures.  The lemma below restricts once more to a common plaque
and recentres at the represented point.  It is the purely measure-theoretic
bridge from an actual overlap identity to projective compatibility of centred
leaf measures.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace VV.BBEKCenteredOverlap

variable {U : Type*} [AddCommGroup U] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [MeasurableSpace U] [BorelSpace U]

/-- Restrict a translated normalized overlap to a common centred set.  The
normalizing constants are the masses of the original (possibly larger)
overlap sets. -/
theorem normalized_centered_restrictions_eq_of_translate
    (μ ν : Measure U) {s t B : Set U}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hB : MeasurableSet B)
    (u d : U)
    (hsource : (fun v : U => v - u) ⁻¹' B ⊆ s)
    (htarget : (fun v : U => v - (u + d)) ⁻¹' B ⊆ t)
    (htranslate :
      ((μ s)⁻¹ • μ.restrict s).map (fun v : U => v + d) =
        (ν t)⁻¹ • ν.restrict t) :
    (μ s)⁻¹ • (μ.map (fun v : U => v - u)).restrict B =
      (ν t)⁻¹ • (ν.map (fun v : U => v - (u + d))).restrict B := by
  have hshift : Measurable (fun v : U => v + d) := measurable_id.add_const d
  have hcenter : Measurable (fun v : U => v - u) := measurable_id.sub_const u
  have hcenter' : Measurable (fun v : U => v - (u + d)) :=
    measurable_id.sub_const (u + d)
  apply Measure.ext
  intro E hE
  let R : Set U := (fun v : U => v - (u + d)) ⁻¹' (E ∩ B)
  have hR : MeasurableSet R := (hE.inter hB).preimage hcenter'
  have hpre : (fun v : U => v + d) ⁻¹' R =
      (fun v : U => v - u) ⁻¹' (E ∩ B) := by
    ext v
    change (v + d - (u + d) ∈ E ∧ v + d - (u + d) ∈ B) ↔
      (v - u ∈ E ∧ v - u ∈ B)
    have hv : v + d - (u + d) = v - u := by abel
    rw [hv]
  have hpreS : (fun v : U => v + d) ⁻¹' R ⊆ s := by
    rw [hpre]
    intro v hv
    exact hsource hv.2
  have hRT : R ⊆ t := by
    intro v hv
    exact htarget hv.2
  have heq := congrArg (fun m : Measure U => m R) htranslate
  change (((μ s)⁻¹ • μ.restrict s).map (fun v : U => v + d)) R =
    ((ν t)⁻¹ • ν.restrict t) R at heq
  rw [Measure.map_apply hshift hR, Measure.smul_apply,
    Measure.restrict_apply (hR.preimage hshift),
    inter_eq_self_of_subset_left hpreS,
    Measure.smul_apply, Measure.restrict_apply hR,
    inter_eq_self_of_subset_left hRT, hpre] at heq
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hE,
    Measure.map_apply hcenter (hE.inter hB),
    Measure.map_apply hcenter' (hE.inter hB)]
  exact heq

end VV.BBEKCenteredOverlap
