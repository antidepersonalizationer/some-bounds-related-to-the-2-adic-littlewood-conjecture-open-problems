import VV.BBEKReverseMaximal
import Mathlib.Probability.Kernel.CondDistrib

/-! Identifying the reverse maximal inequality with the literal conditional
laws of a measurable root code. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter MeasurableSpace
open scoped ENNReal NNReal
namespace VV.BBEKCodeMaximal

theorem ae_measure_eq_of_setwise
    {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z] [StandardBorelSpace Z]
    (μ : Measure W) (ν κ : W → Measure Z)
    (hν : ∀ w, IsFiniteMeasure (ν w)) (hκ : ∀ w, IsFiniteMeasure (κ w))
    (he : ∀ s : Set Z, MeasurableSet s → ∀ᵐ w ∂μ, ν w s = κ w s) :
    ∀ᵐ w ∂μ, ν w = κ w := by
  let e := embeddingReal Z
  have hem : MeasurableEmbedding e := measurableEmbedding_embeddingReal Z
  let V := fun w => (ν w).map e
  let K := fun w => (κ w).map e
  letI (w : W) : IsFiniteMeasure (V w) := inferInstanceAs (IsFiniteMeasure ((ν w).map e))
  letI (w : W) : IsFiniteMeasure (K w) := inferInstanceAs (IsFiniteMeasure ((κ w).map e))
  have hs (s : Set ℝ) (hsm : MeasurableSet s) : ∀ᵐ w ∂μ, V w s = K w s := by
    filter_upwards [he (e ⁻¹' s) (hem.measurable hsm)] with w hw
    simpa only [V,K,Measure.map_apply hem.measurable hsm] using hw
  have htotal := hs univ MeasurableSet.univ
  have hall : ∀ᵐ w ∂μ, ∀ s : Set ℝ, MeasurableSet s → V w s = K w s := by
    apply MeasurableSpace.ae_induction_on_inter Real.borel_eq_generateFrom_Iic_rat Real.isPiSystem_Iic_rat
    · simp
    · simp only [iUnion_singleton_eq_range,mem_range,forall_exists_index,forall_apply_eq_imp_iff]
      exact ae_all_iff.mpr (fun q => hs (Iic (q : ℝ)) measurableSet_Iic)
    · filter_upwards [htotal] with w hw s hsm heq
      rw [measure_compl hsm (measure_ne_top _ _),heq,hw,
        measure_compl hsm (measure_ne_top _ _)]
    · refine ae_of_all _ (fun w s hdisj hsm heq => ?_)
      rw [measure_iUnion hdisj hsm,measure_iUnion hdisj hsm]
      exact tsum_congr heq
  filter_upwards [hall] with w hw
  ext s hs
  have hh := hw (e '' s) (hem.measurableSet_image.mpr hs)
  change (ν w).map e (e '' s) = (κ w).map e (e '' s) at hh
  simpa only [Measure.map_apply hem.measurable (hem.measurableSet_image.mpr hs),
    Set.preimage_image_eq _ hem.injective] using hh

theorem condExpKernel_comap_eq_condDistrib_id
    {Z Y : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableSpace Y] (μ : Measure Z) [IsFiniteMeasure μ]
    (f : Z → Y) (hf : Measurable f) :
    ∀ᵐ z ∂μ, condExpKernel μ ((inferInstance : MeasurableSpace Y).comap f) z =
      condDistrib id f μ (f z) := by
  apply ae_measure_eq_of_setwise μ _ _ (fun _ => inferInstance) (fun _ => inferInstance)
  intro s hs
  have h₁ := condExpKernel_ae_eq_condExp (μ := μ) hf.comap_le hs
  have h₂ := condDistrib_ae_eq_condExp (μ := μ) hf (measurable_id (α := Z)) hs
  filter_upwards [h₁,h₂] with z hz hz'
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact hz.trans hz'.symm

open BBEKReverseMaximal

theorem tail_code_condDistrib_maximal
    {Z Y : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableSpace Y] (μ : Measure Z) [IsFiniteMeasure μ]
    (f : Z → ℕ → Y) (hf : Measurable f) {B : Set Z} (hB : MeasurableSet B)
    (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * μ {z | ∃ n,
      (ε : ℝ) ≤ (condDistrib id (tailCode f n) μ (tailCode f n z)).real B} ≤ μ B := by
  have he := ae_all_iff.mpr (fun n =>
    condExpKernel_comap_eq_condDistrib_id μ (tailCode f n) (measurable_tailCode f hf n))
  have hsets : {z | ∃ n,
      (ε : ℝ) ≤ (condDistrib id (tailCode f n) μ (tailCode f n z)).real B} =ᵐ[μ]
      {z | ∃ n, (ε : ℝ) ≤ (condExpKernel μ (tailSigma f n) z).real B} := by
    filter_upwards [he] with z hz
    apply propext
    exact exists_congr (fun n => by rw [show condExpKernel μ (tailSigma f n) z = _ from hz n])
  rw [measure_congr hsets]
  exact reverse_condKernel_maximal μ (tailSigma f) (tailSigma_antitone f)
    (tailSigma_le f hf) hB ε

end VV.BBEKCodeMaximal
