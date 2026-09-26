import VV.BBEKLeafEntropySubordinateCharts
import VV.BBEKKernelFiberRestriction
import VV.BBEKLeafwiseSupport
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditioning the actual transverse kernel on a measurable plaque code

This identifies the conditional law after recording both the transverse
coordinate and a code. At a code fiber of positive leaf mass, the result is
the original leaf kernel restricted to that fiber and normalized.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafEntropyRefinement

variable {B U Y : Type*} [MeasurableSpace B] [MeasurableSpace U] [MeasurableSpace Y]

def codeKernel (κ : Kernel B U) [IsSFiniteKernel κ]
    {f : B × U → Y} (hf : Measurable f) : Kernel B (Y × U) where
  toFun b := (κ b).map (fun u => (f (b,u),u))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro t ht
    have hm (b : B) : Measurable (fun u => (f (b,u),u)) :=
      (hf.comp measurable_prodMk_left).prodMk measurable_id
    simp only [Measure.map_apply (hm _) ht]
    exact Kernel.measurable_kernel_prodMk_left
      (ht.preimage (hf.prodMk measurable_snd))

theorem codeKernel_apply (κ : Kernel B U) [IsSFiniteKernel κ]
    {f : B × U → Y} (hf : Measurable f) (b : B) :
    codeKernel κ hf b = (κ b).map (fun u => (f (b,u),u)) := rfl

instance codeKernel_markov (κ : Kernel B U) [IsMarkovKernel κ]
    {f : B × U → Y} (hf : Measurable f) : IsMarkovKernel (codeKernel κ hf) :=
  ⟨fun _ => isProbabilityMeasure_map
    ((hf.comp measurable_prodMk_left).prodMk measurable_id).aemeasurable⟩

variable [StandardBorelSpace U] [Nonempty U] [StandardBorelSpace Y]

def refinedMeasure (ρ : Measure (B × U)) (f : B × U → Y) : Measure ((B × Y) × U) :=
  ρ.map (fun p => ((p.1,f p),p.2))

instance refinedMeasure_finite (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    (f : B × U → Y) : IsFiniteMeasure (refinedMeasure ρ f) := by
  unfold refinedMeasure
  infer_instance

theorem disintegrate_refinement (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {f : B × U → Y} (hf : Measurable f) :
    (ρ.fst ⊗ₘ Kernel.fst (codeKernel ρ.condKernel hf)) ⊗ₘ
      Kernel.condKernel (codeKernel ρ.condKernel hf) = refinedMeasure ρ f := by
  let κ := codeKernel ρ.condKernel hf
  have hm : Measurable (fun p : B × U => ((p.1,f p),p.2)) :=
    (measurable_fst.prodMk hf).prodMk measurable_snd
  apply Measure.ext
  intro s hs
  rw [Measure.compProd_apply hs]
  rw [Measure.lintegral_compProd
    (Kernel.measurable_kernel_prodMk_left hs)]
  change (∫⁻ b, ∫⁻ y, Kernel.condKernel κ (b,y)
    ((fun u => ((b,y),u)) ⁻¹' s) ∂Kernel.fst κ b ∂ρ.fst) = _
  have hpoint (b : B) :
      (∫⁻ y, Kernel.condKernel κ (b,y) ((fun u => ((b,y),u)) ⁻¹' s) ∂Kernel.fst κ b) =
        κ b ((fun p : Y × U => ((b,p.1),p.2)) ⁻¹' s) := by
    have hm' : Measurable (fun p : Y × U => ((b,p.1),p.2)) := by fun_prop
    have hs' := hs.preimage hm'
    conv_rhs => rw [← κ.disintegrate (Kernel.condKernel κ)]
    rw [Kernel.compProd_apply hs']
    rfl
  simp_rw [hpoint]
  rw [refinedMeasure,Measure.map_apply hm hs]
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.compProd_apply (hs.preimage hm)]
  apply lintegral_congr
  intro b
  have hm' : Measurable (fun p : Y × U => ((b,p.1),p.2)) := by fun_prop
  have hm'' : Measurable (fun u : U => (f (b,u),u)) :=
    (hf.comp measurable_prodMk_left).prodMk measurable_id
  rw [codeKernel_apply,Measure.map_apply hm'' (hs.preimage hm')]
  rfl

def codeFiber {f : B × U → Y} (b : B) (y : Y) : Set U := {u | f (b,u) = y}

omit [StandardBorelSpace U] [Nonempty U] in
theorem measurableSet_code_relation {f : B × U → Y} (hf : Measurable f) :
    MeasurableSet {p : (B × Y) × U | f (p.1.1,p.2) = p.1.2} := by
  letI := upgradeStandardBorel Y
  exact isClosed_diagonal.measurableSet.preimage
    ((hf.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd)

def codeMass (κ : Kernel B U) [IsSFiniteKernel κ] (f : B × U → Y) (p : B × Y) : ℝ≥0∞ :=
  κ p.1 (codeFiber (f := f) p.1 p.2)

omit [StandardBorelSpace U] [Nonempty U] in
theorem measurable_codeMass (κ : Kernel B U) [IsSFiniteKernel κ]
    {f : B × U → Y} (hf : Measurable f) : Measurable (codeMass κ f) :=
  Kernel.measurable_kernel_prodMk_left (κ := κ.comap Prod.fst measurable_fst)
    (measurableSet_code_relation hf)

def atomicCodeKernel (κ : Kernel B U) [IsSFiniteKernel κ]
    {f : B × U → Y} (hf : Measurable f) : Kernel (B × Y) U :=
  BBEKLeafwiseKernel.fiberCondition (κ.comap Prod.fst measurable_fst)
    (measurableSet_code_relation hf)

instance atomicCodeKernel_finite (κ : Kernel B U) [IsSFiniteKernel κ]
    {f : B × U → Y} (hf : Measurable f) : IsFiniteKernel (atomicCodeKernel κ hf) := by
  unfold atomicCodeKernel
  infer_instance

omit [StandardBorelSpace U] [Nonempty U] in
theorem atomicCodeKernel_apply (κ : Kernel B U) [IsSFiniteKernel κ]
    {f : B × U → Y} (hf : Measurable f) (p : B × Y) :
    atomicCodeKernel κ hf p =
      (codeMass κ f p)⁻¹ • (κ p.1).restrict (codeFiber (f := f) p.1 p.2) := rfl

omit [StandardBorelSpace U] [Nonempty U] [StandardBorelSpace Y] in
theorem codeKernel_fst (κ : Kernel B U) [IsSFiniteKernel κ]
    {f : B × U → Y} (hf : Measurable f) (b : B) :
    (codeKernel κ hf b).fst = (κ b).map (fun u => f (b,u)) := by
  have hm : Measurable (fun u : U => (f (b,u),u)) :=
    (hf.comp measurable_prodMk_left).prodMk measurable_id
  rw [Measure.fst,codeKernel_apply,Measure.map_map measurable_fst hm]
  rfl

theorem codeKernel_condKernel_of_pos (κ : Kernel B U) [IsMarkovKernel κ]
    {f : B × U → Y} (hf : Measurable f) (b : B) (y : Y)
    (hpos : codeMass κ f (b,y) ≠ 0) :
    (codeKernel κ hf b).condKernel y = atomicCodeKernel κ hf (b,y) := by
  have hm : Measurable (fun u : U => f (b,u)) := hf.comp measurable_prodMk_left
  have hm' : Measurable (fun u : U => (f (b,u),u)) := hm.prodMk measurable_id
  have hmass : (codeKernel κ hf b).fst {y} = codeMass κ f (b,y) := by
    rw [codeKernel_fst,Measure.map_apply hm (measurableSet_singleton y)]
    rfl
  apply Measure.ext
  intro t ht
  rw [Measure.condKernel_apply_of_ne_zero (by rwa [hmass]),hmass,
    codeKernel_apply,Measure.map_apply hm'
      ((measurableSet_singleton y).prod ht),
    atomicCodeKernel_apply,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply ht]
  congr 1
  apply congrArg (κ b)
  ext u
  simp only [mem_preimage,mem_prod,mem_singleton_iff,mem_inter_iff,codeFiber,mem_setOf_eq,and_comm]

theorem disintegrate_atomic_refinement (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {f : B × U → Y} (hf : Measurable f)
    (hpos : ∀ᵐ p ∂ρ, codeMass ρ.condKernel f (p.1,f p) ≠ 0) :
    (ρ.fst ⊗ₘ Kernel.fst (codeKernel ρ.condKernel hf)) ⊗ₘ
      atomicCodeKernel ρ.condKernel hf = refinedMeasure ρ f := by
  let κ := codeKernel ρ.condKernel hf
  let η := atomicCodeKernel ρ.condKernel hf
  have hp : ∀ᵐ p ∂ρ.fst ⊗ₘ ρ.condKernel, codeMass ρ.condKernel f (p.1,f p) ≠ 0 := by
    rwa [Measure.disintegrate]
  have hpoint : ∀ᵐ b ∂ρ.fst, (κ b).fst ⊗ₘ η.comap (Prod.mk b) measurable_prodMk_left = κ b := by
    filter_upwards [Measure.ae_ae_of_ae_compProd hp] with b hb
    have hmb : Measurable (fun u : U => f (b,u)) := hf.comp measurable_prodMk_left
    have hy : ∀ᵐ y ∂(ρ.condKernel b).map (fun u => f (b,u)), codeMass ρ.condKernel f (b,y) ≠ 0 := by
      apply (ae_map_iff hmb.aemeasurable ?_).mpr hb
      exact (measurableSet_eq_fun' ((measurable_codeMass ρ.condKernel hf).comp measurable_prodMk_left)
        measurable_const).compl
    have he : η.comap (Prod.mk b) measurable_prodMk_left =ᵐ[(κ b).fst] (κ b).condKernel := by
      rw [codeKernel_fst]
      filter_upwards [hy] with y hmass
      exact (codeKernel_condKernel_of_pos ρ.condKernel hf b y hmass).symm
    rw [Measure.compProd_congr he,Measure.disintegrate]
  have hm : Measurable (fun p : B × U => ((p.1,f p),p.2)) :=
    (measurable_fst.prodMk hf).prodMk measurable_snd
  apply Measure.ext
  intro s hs
  rw [Measure.compProd_apply hs,
    Measure.lintegral_compProd (Kernel.measurable_kernel_prodMk_left hs),
    refinedMeasure,Measure.map_apply hm hs]
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.compProd_apply (hs.preimage hm)]
  apply lintegral_congr_ae
  filter_upwards [hpoint] with b hb
  have hm' : Measurable (fun p : Y × U => ((b,p.1),p.2)) := by fun_prop
  have hm'' : Measurable (fun u : U => (f (b,u),u)) :=
    (hf.comp measurable_prodMk_left).prodMk measurable_id
  have he := congrArg (fun ν : Measure (Y × U) => ν ((fun p => ((b,p.1),p.2)) ⁻¹' s)) hb
  dsimp only at he
  rw [Measure.compProd_apply (hs.preimage hm'),codeKernel_apply,
    Measure.map_apply hm'' (hs.preimage hm')] at he
  exact he

omit [StandardBorelSpace U] [Nonempty U] [StandardBorelSpace Y] in
theorem refinedMeasure_fst (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {f : B × U → Y} (hf : Measurable f) :
    (refinedMeasure ρ f).fst = ρ.map (fun p => (p.1,f p)) := by
  have hm : Measurable (fun p : B × U => ((p.1,f p),p.2)) :=
    (measurable_fst.prodMk hf).prodMk measurable_snd
  rw [Measure.fst,refinedMeasure,Measure.map_map measurable_fst hm]
  rfl

/-- The conditional law after recording a transverse coordinate and a code
is exactly the normalized restriction of the actual transverse kernel. -/
theorem refined_condKernel_eq_normalized_restrict (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {f : B × U → Y} (hf : Measurable f)
    (hpos : ∀ᵐ p ∂ρ, codeMass ρ.condKernel f (p.1,f p) ≠ 0) :
    ∀ᵐ p ∂ρ, (refinedMeasure ρ f).condKernel (p.1,f p) =
      (ρ.condKernel p.1 (codeFiber (f := f) p.1 (f p)))⁻¹ •
        (ρ.condKernel p.1).restrict (codeFiber (f := f) p.1 (f p)) := by
  have hfst : (refinedMeasure ρ f).fst = ρ.fst ⊗ₘ Kernel.fst (codeKernel ρ.condKernel hf) := by
    rw [← disintegrate_refinement ρ hf,Measure.fst_compProd]
  have hd : refinedMeasure ρ f = (refinedMeasure ρ f).fst ⊗ₘ atomicCodeKernel ρ.condKernel hf := by
    rw [hfst]
    exact (disintegrate_atomic_refinement ρ hf hpos).symm
  have he := eq_condKernel_of_measure_eq_compProd (atomicCodeKernel ρ.condKernel hf) hd
  rw [refinedMeasure_fst ρ hf] at he
  have hh := ae_of_ae_map (measurable_fst.prodMk hf).aemeasurable he
  filter_upwards [hh] with p hp
  exact hp.symm

section PositiveFiber
variable [PseudoMetricSpace U] [BorelSpace U] [SecondCountableTopology U]

omit [MeasurableSpace Y] [StandardBorelSpace Y] in
/-- A genuine leaf neighborhood inside a code fiber gives positive mass for
that fiber under the actual conditional kernel. No atomicity assumption is used. -/
theorem codeMass_pos_of_ae_local_const (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    (f : B × U → Y)
    (hlocal : ∀ᵐ p ∂ρ, ∃ ε : ℝ, 0 < ε ∧ ∀ v : U, dist v p.2 < ε → f (p.1,v) = f p) :
    ∀ᵐ p ∂ρ, 0 < codeMass ρ.condKernel f (p.1,f p) := by
  filter_upwards [hlocal,BBEKLeafwiseKernel.condKernel_ae_all_ball_pos ρ] with p hp hs
  obtain ⟨ε,hε,hf⟩ := hp
  exact (hs ε hε).trans_le (measure_mono (fun v hv => hf v hv))

end PositiveFiber

end VV.BBEKLeafEntropyRefinement
