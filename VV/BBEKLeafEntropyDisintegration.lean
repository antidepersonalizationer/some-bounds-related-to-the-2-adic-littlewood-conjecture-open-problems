import VV.Entropy.ConditionalEntropyNontrivial
import VV.BBEKOneRootLocal

/-! Exact conditional entropy in the literal one-root disintegration.

Conditioning on the transverse coordinate has conditional probabilities given
by the actual `condKernel`. This identifies the entropy object used by a future
root-entropy formula with the existing chart kernel; no dynamical entropy
formula or root product-structure assertion is assumed here.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafEntropyDisintegration
open ErgodicTheory.Entropy BBEKOneRootLocal

section Product
variable {B U I : Type*} [MeasurableSpace B] [MeasurableSpace U]
  [StandardBorelSpace B] [StandardBorelSpace U] [Nonempty U]

omit [StandardBorelSpace B] in
/-- The product-coordinate conditional distribution is the literal kernel
already used in the canonical root chart construction. -/
theorem condDistrib_snd_fst (ρ : Measure (B × U)) [IsFiniteMeasure ρ] :
    condDistrib Prod.snd Prod.fst ρ = ρ.condKernel := by
  rw [condDistrib]
  have h : (fun p : B × U => (p.1,p.2)) = id := rfl
  simp only [h, Measure.map_id]

/-- Conditional probabilities of an arbitrary measurable product set are its
fiber masses in the actual transverse disintegration. -/
theorem condExpKernel_fst_apply (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {S : Set (B × U)} (hS : MeasurableSet S) :
    ∀ᵐ p ∂ρ,
      condExpKernel ρ ((inferInstance : MeasurableSpace B).comap Prod.fst) p S =
        ρ.condKernel p.1 (Prod.mk p.1 ⁻¹' S) := by
  let f : B × U → ℝ := S.indicator (fun _ => 1)
  have hfi : Integrable f ρ := (integrable_const (1 : ℝ)).indicator hS
  have hcond := condExp_prod_ae_eq_integral_condDistrib
    (μ := ρ) (X := Prod.fst) (Y := Prod.snd) measurable_fst measurable_snd.aemeasurable
    ((stronglyMeasurable_const.indicator hS) : StronglyMeasurable f) hfi
  have hk := condExpKernel_ae_eq_condExp (μ := ρ) measurable_fst.comap_le hS
  filter_upwards [hcond,hk] with p hp hkp
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (condExpKernel ρ _ p).real S = (ρ.condKernel p.1).real (Prod.mk p.1 ⁻¹' S)
  rw [hkp]
  change ρ[f | (inferInstance : MeasurableSpace B).comap Prod.fst] p = _
  rw [hp, condDistrib_snd_fst]
  change (∫ u, (Prod.mk p.1 ⁻¹' S).indicator (fun _ => (1 : ℝ)) u ∂ρ.condKernel p.1) = _
  rw [integral_indicator_const _ (hS.preimage measurable_prodMk_left)]
  simp only [smul_eq_mul, mul_one]

variable [Fintype I]

/-- Shannon conditional entropy is exactly the average entropy of the
measurable-set fibers under the actual root conditional kernel. -/
theorem condEntropy_fst_eq (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    (cells : I → Set (B × U)) (hcells : ∀ i, MeasurableSet (cells i)) :
    condEntropy ρ ((inferInstance : MeasurableSpace B).comap Prod.fst) cells =
      ∫ p, entropy (ρ.condKernel p.1) (fun i => Prod.mk p.1 ⁻¹' cells i) ∂ρ := by
  unfold condEntropy
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i => condExpKernel_fst_apply ρ (hcells i))] with p hp
  simp only [entropy]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun v : ℝ≥0∞ => Real.negMulLog v.toReal) (hp i))

/-- A positive transverse conditional entropy excludes Dirac root kernels.
This is a statement about the actual product disintegration, not a supplied
family of unrelated leaf measures. -/
theorem not_ae_dirac_of_pos_condEntropy_fst
    (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    (cells : I → Set (B × U)) (hcells : ∀ i, MeasurableSet (cells i))
    (hpos : 0 < condEntropy ρ ((inferInstance : MeasurableSpace B).comap Prod.fst) cells) :
    ¬ (∀ᵐ p ∂ρ, ∃ u : U, ρ.condKernel p.1 = Measure.dirac u) := by
  intro hd
  rw [condEntropy_fst_eq ρ cells hcells] at hpos
  have hz : (∫ p, entropy (ρ.condKernel p.1) (fun i => Prod.mk p.1 ⁻¹' cells i) ∂ρ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hd] with p hp
    obtain ⟨u,hu⟩ := hp
    change entropy (ρ.condKernel p.1) (fun i => Prod.mk p.1 ⁻¹' cells i) = 0
    rw [hu, entropy_dirac_eq_zero]
  rw [hz] at hpos
  exact lt_irrefl _ hpos

end Product

section Center
variable {B U I : Type*} [MeasurableSpace B] [NormedAddCommGroup U]
  [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]

/-- Centering an actual conditional probability gives unit Dirac at zero
exactly when the original kernel is unit Dirac at the sampled coordinate. -/
theorem centeredKernel_eq_dirac_zero_iff (κ : Kernel B U) [IsSFiniteKernel κ]
    (p : B × U) : centeredKernel κ p = Measure.dirac 0 ↔ κ p.1 = Measure.dirac p.2 := by
  have hp : Measurable (fun v : U => v+p.2) := measurable_id.add measurable_const
  have hm : Measurable (fun v : U => v-p.2) := measurable_id.sub measurable_const
  constructor
  · intro h
    have he := congrArg (fun ν : Measure U => ν.map (fun v => v+p.2)) h
    change ((κ p.1).map (fun v => v-p.2)).map (fun v => v+p.2) = _ at he
    dsimp only at he
    rw [Measure.map_map hp hm, Measure.map_dirac hp] at he
    have hfun : (fun v : U => v+p.2) ∘ (fun v => v-p.2) = id := by
      funext v
      exact sub_add_cancel v p.2
    simpa only [hfun, Measure.map_id, zero_add] using he
  · intro h
    change (κ p.1).map (fun v => v-p.2) = _
    rw [h, Measure.map_dirac hm, sub_self]

variable [StandardBorelSpace B] [StandardBorelSpace U] [Fintype I]

/-- Positive entropy conditioned on the transverse coordinate forces the
literal centered one-root conditional family to be non-Dirac on nonzero mass. -/
theorem not_ae_centered_dirac_of_pos_condEntropy_fst
    (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    (cells : I → Set (B × U)) (hcells : ∀ i, MeasurableSet (cells i))
    (hpos : 0 < condEntropy ρ ((inferInstance : MeasurableSpace B).comap Prod.fst) cells) :
    ¬ (∀ᵐ p ∂ρ, centeredKernel ρ.condKernel p = Measure.dirac 0) := by
  intro hd
  apply not_ae_dirac_of_pos_condEntropy_fst ρ cells hcells hpos
  exact hd.mono (fun p hp => ⟨p.2, (centeredKernel_eq_dirac_zero_iff _ p).mp hp⟩)

end Center

section Chart
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel BBEKLeafwiseChart BBEKLeafwiseAtlas
open BBEKLocalRootFamily BBEKUniformPlaques
variable {B U I : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [StandardBorelSpace B] [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U] [Fintype I]

omit [StandardBorelSpace B] in
/-- The zero-root-kernel statement on the quotient chart is equivalent to
the zero-root-kernel statement on its literal coordinate measure. -/
theorem ae_local_dirac_iff (s : GroupParams ≃ₜ B × U)
    (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    (∀ᵐ q ∂μ.restrict c.image, localMeasureWith s μ c q = Measure.dirac 0) ↔
    (∀ᵐ p ∂(coordinateMeasureOf μ c).map s,
      centeredKernel ((coordinateMeasureOf μ c).map s).condKernel p = Measure.dirac 0) := by
  have hmap : (μ.comap (c.domain.restrict (quotientCoordinates c.base))).map
      (c.domain.restrict (quotientCoordinates c.base)) = μ.restrict c.image := by
    rw [c.embedding.measurableEmbedding.map_comap, Set.range_restrict]
    rfl
  rw [← hmap, c.embedding.measurableEmbedding.ae_map_iff,
    s.measurableEmbedding.ae_map_iff]
  change _ ↔ ∀ᵐ p ∂(μ.comap (c.domain.restrict (quotientCoordinates c.base))).map
      Subtype.val,
    centeredKernel ((coordinateMeasureOf μ c).map s).condKernel (s p) = Measure.dirac 0
  rw [(MeasurableEmbedding.subtype_coe c.isOpen_domain.measurableSet).ae_map_iff]
  apply Filter.eventually_congr
  filter_upwards [] with p
  unfold localMeasureWith
  dsimp only [Set.restrict]
  rw [chartCoordinates_apply]

/-- Positive transverse conditional entropy for the actual coordinate
measure forces a nontrivial local root conditional on the original quotient.
No conditional measure has been supplied as an unproved compatibility input.
This single-step entropy does not yet exclude finite atomic conditional
probabilities; a dynamical entropy-rate argument is still required. -/
theorem not_ae_local_dirac_of_pos_condEntropy
    (s : GroupParams ≃ₜ B × U) (μ : Measure X) [IsFiniteMeasure μ] (c : Chart)
    (cells : I → Set (B × U)) (hcells : ∀ i, MeasurableSet (cells i))
    (hpos : 0 < condEntropy ((coordinateMeasureOf μ c).map s)
      ((inferInstance : MeasurableSpace B).comap Prod.fst) cells) :
    ¬ (∀ᵐ q ∂μ.restrict c.image, localMeasureWith s μ c q = Measure.dirac 0) := by
  intro hd
  exact not_ae_centered_dirac_of_pos_condEntropy_fst _ cells hcells hpos
    ((ae_local_dirac_iff s μ c).mp hd)

end Chart
end VV.BBEKLeafEntropyDisintegration
