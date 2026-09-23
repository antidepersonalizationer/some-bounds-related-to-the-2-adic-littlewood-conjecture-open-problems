import VV.BBEKTopology
import VV.BBEKDiagonalAverage
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
Three explicit elements of the positive cone generate a dense subgroup of
the full parameter group. Thus finite commuting Cesaro averages can replace
continuous cone averages, once their weak limits and entropy are controlled.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace VV.BBEKConeGenerators
open BBEKDynamics BBEKDiagonal BBEKQuotient BBEKTopology BBEKDiagonalAverage

def generator (i : Fin 3) : ℝ × ℤ := ![(1,0),(Real.sqrt 2,0),(time0,1)] i

theorem generator_mem_cone (i : Fin 3) : Cone (generator i).1 (generator i).2 := by
  fin_cases i
  · rw [cone_iff]; norm_num [generator]
  · rw [cone_iff]; simpa [generator] using Real.sqrt_nonneg (2:ℝ)
  · exact time0_cone_unstable.1

theorem closed_addSubgroup_eq_top_of_generators
    (S : AddSubgroup (ℝ × ℤ)) (hc : IsClosed (S : Set (ℝ × ℤ)))
    (hg : ∀ i, generator i ∈ S) : S = ⊤ := by
  let R := S.comap (AddMonoidHom.inl ℝ ℤ)
  have hR : IsClosed (R : Set ℝ) := hc.preimage (continuous_id.prodMk continuous_const)
  have hpair : AddSubgroup.closure {Real.sqrt 2,1} ≤ R := by
    apply (AddSubgroup.closure_le R).mpr
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact hg 1
    · rcases hx with rfl
      exact hg 0
  have hd : Dense (R : Set ℝ) :=
    ((dense_addSubgroupClosure_pair_iff).mpr (by simpa using irrational_sqrt_two)).mono hpair
  have hreal (t : ℝ) : (t,0) ∈ S := by
    have ht := hd t
    rwa [hR.closure_eq] at ht
  have hunit : ((0:ℝ),(1:ℤ)) ∈ S := by
    have hh := S.sub_mem (hg 2) (hreal time0)
    simpa [generator] using hh
  apply (AddSubgroup.eq_top_iff' S).mpr
  intro a
  have hi := S.zsmul_mem hunit a.2
  have hh := S.add_mem (hreal a.1) hi
  simpa using hh

def preservingParameters (μ : Measure X) : AddSubgroup (ℝ × ℤ) where
  carrier := {a | MeasurePreserving (fun q : X => psi a.1 a.2 • q) μ μ}
  zero_mem' := by simpa using MeasurePreserving.id μ
  add_mem' := by
    intro a b ha hb
    change MeasurePreserving (fun q : X => psi (a.1+b.1) (a.2+b.2) • q) μ μ
    simpa only [Prod.fst_add,Prod.snd_add,psi_add,mul_smul,Function.comp_def] using ha.comp hb
  neg_mem' := by
    intro a ha
    have hi := MeasurePreserving.symm (MeasurableEquiv.smul (psi a.1 a.2)) ha
    change MeasurePreserving (fun q : X => (psi a.1 a.2)⁻¹ • q) μ μ at hi
    change MeasurePreserving (fun q : X => psi (-a.1) (-a.2) • q) μ μ
    simpa only [psi_neg] using hi

theorem continuous_integral_parameter (μ : Measure X) [IsFiniteMeasure μ]
    (f : X →ᵇ ℝ) : Continuous (fun a : ℝ × ℤ => ∫ q, f (psi a.1 a.2 • q) ∂μ) := by
  apply continuous_of_dominated (bound:=fun _ : X => ‖f‖)
  · intro a
    exact (f.continuous.comp (continuous_const.smul continuous_id)).aestronglyMeasurable
  · intro a
    exact ae_of_all _ (fun q => f.norm_coe_le_norm _)
  · exact integrable_const _
  · apply ae_of_all
    intro q
    exact f.continuous.comp (continuous_psiHom.smul continuous_const)

theorem preservingParameters_closed (μ : Measure X) [IsFiniteMeasure μ] :
    IsClosed (preservingParameters μ : Set (ℝ × ℤ)) := by
  have he : (preservingParameters μ : Set (ℝ × ℤ)) =
      ⋂ f : X →ᵇ ℝ, {a | (∫ q, f (psi a.1 a.2 • q) ∂μ) = ∫ q, f q ∂μ} := by
    ext a
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    constructor
    · intro ha f
      exact ha.integral_comp (MeasurableEquiv.smul (psi a.1 a.2)).measurableEmbedding f
    · intro ha
      refine ⟨(continuous_const.smul continuous_id).measurable,?_⟩
      apply ext_of_forall_integral_eq_of_IsFiniteMeasure
      intro f
      exact ((MeasurableEquiv.smul (psi a.1 a.2)).measurableEmbedding.integral_map f).trans (ha f)
  rw [he]
  exact isClosed_iInter fun f => isClosed_eq (continuous_integral_parameter μ f) continuous_const

theorem psi_invariant_of_generators (μ : Measure X) [IsFiniteMeasure μ]
    (hg : ∀ i, MeasurePreserving (fun q : X => psi (generator i).1 (generator i).2 • q) μ μ) :
    SMulInvariantMeasure H X μ := by
  have ht : preservingParameters μ = ⊤ :=
    closed_addSubgroup_eq_top_of_generators _ (preservingParameters_closed μ) hg
  constructor
  intro h s hs
  have hp : MeasurePreserving (fun q : X => psi h.toAdd.1 h.toAdd.2 • q) μ μ :=
    ((AddSubgroup.eq_top_iff' _).mp ht) h.toAdd
  exact hp.measure_preimage hs.nullMeasurableSet

end VV.BBEKConeGenerators
