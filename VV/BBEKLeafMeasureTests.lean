import VV.BBEKLeafwiseStabilizer
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Continuous compact-support integral tests for locally finite Radon measures.
These will supply the countable measurable tests for leaf stabilizer fields. -/
noncomputable section
open Set MeasureTheory Filter Metric Function TopologicalSpace
open scoped Topology ENNReal
namespace VV.BBEKLeafMeasureTests

variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [ProperSpace U] [SecondCountableTopology U]

/-- Compactly supported continuous integrals determine a Radon measure,
including measures with infinite total mass. -/
theorem ext_of_compact_integrals (μ ν : Measure U) [μ.Regular] [ν.Regular]
    (he : ∀ f : C(U,ℝ), HasCompactSupport f → ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν := by
  have hle (μ ν : Measure U) [μ.Regular] [ν.Regular]
      (he : ∀ f : C(U,ℝ), HasCompactSupport f → ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ ≤ ν := by
    have ho (O : Set U) (hO : IsOpen O) : μ O ≤ ν O := by
      rw [hO.measure_eq_iSup_isCompact μ]
      refine iSup_le fun K => iSup_le fun hKO => iSup_le fun hK => ?_
      obtain ⟨f,hfK,hfO,hfc,hfb⟩ := exists_continuous_one_zero_of_isCompact hK
        hO.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKO)
      calc
        μ K ≤ ENNReal.ofReal (∫ x, f x ∂μ) :=
          (f.continuous.integrable_of_hasCompactSupport hfc).measure_le_integral
            (ae_of_all _ fun x => (hfb x).1) (fun x hx => by rw [hfK hx]; rfl)
        _ = ENNReal.ofReal (∫ x, f x ∂ν) := congrArg ENNReal.ofReal (he f hfc)
        _ ≤ ν O := integral_le_measure (fun x _ => (hfb x).2)
          (fun x hx => le_of_eq (hfO hx))
    apply Measure.le_iff.mpr
    intro S _
    rw [S.measure_eq_iInf_isOpen ν]
    exact le_iInf fun O => le_iInf fun hSO => le_iInf fun hO =>
      (measure_mono hSO).trans (ho O hO)
  exact le_antisymm (hle μ ν he) (hle ν μ (fun f hf => (he f hf).symm))

/-- The integral of a translate of a compactly supported continuous function
is continuous in the translation parameter, even for an infinite Radon measure. -/
theorem continuous_integral_translate (μ : Measure U) [IsFiniteMeasureOnCompacts μ]
    (f : C(U,ℝ)) (hf : HasCompactSupport f) :
    Continuous (fun u : U => ∫ x, f (u+x) ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro u₀
  let K : Set U := (tsupport f ×ˢ closedBall u₀ 1).image (fun p : U × U => p.1-p.2)
  have hK : IsCompact K := (hf.prod (isCompact_closedBall u₀ 1)).image
    (continuous_fst.sub continuous_snd)
  have hc : ContinuousOn (fun u : U => ∫ x, f (u+x) ∂μ) (closedBall u₀ 1) := by
    apply continuousOn_integral_of_compact_support (f := fun u x => f (u+x)) hK
      (f.continuous.comp (continuous_fst.add continuous_snd)).continuousOn
    intro u x hu hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hx
    refine ⟨(u+x,u),⟨hmem,hu⟩,?_⟩
    dsimp
    abel
  exact hc.continuousAt (closedBall_mem_nhds u₀ zero_lt_one)

/-- With a fixed compact support, integration is continuous for the compact-open
topology on continuous test functions. -/
def SupportedTest (n : ℕ) := {f : C(U,ℝ) | tsupport f ⊆ closedBall 0 (n : ℝ)}

instance (n : ℕ) : Nonempty (SupportedTest (U := U) n) :=
  ⟨⟨0,by change closure {x : U | (0 : ℝ) ≠ 0} ⊆ _; simp⟩⟩

theorem continuous_integral_supported (μ : Measure U) [IsFiniteMeasureOnCompacts μ] (n : ℕ) :
    Continuous (fun f : SupportedTest (U := U) n => ∫ x, f.val x ∂μ) := by
  apply continuous_iff_continuousOn_univ.mpr
  apply continuousOn_integral_of_compact_support (μ := μ) (f := fun (f : SupportedTest (U := U) n) (x : U) => f.val x) (s := univ) (isCompact_closedBall (0 : U) (n : ℝ))
  · exact (continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)).continuousOn
  · intro f x _ hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (f.property h))

/-- Evaluation of the integral of each fixed continuous test is measurable in
any measurable family of measures; no finite-total-mass condition is needed. -/
theorem measurable_integral_family {Z : Type*} [MeasurableSpace Z]
    (η : Z → Measure U) (hη : Measurable η) (f : C(U,ℝ)) :
    Measurable (fun z => ∫ x, f x ∂η z) := by
  let κ : ProbabilityTheory.Kernel Z U := ⟨η,hη⟩
  exact (f.continuous.stronglyMeasurable.integral_kernel (κ := κ)).measurable





/-- One countable family, independent of the measure, exhausting all compact
support bounds in the compact-open topology. -/
def testPair (p : ℕ × ℕ) : C(U,ℝ) :=
  (denseSeq (SupportedTest (U := U) p.1) p.2).val

def testFunction (j : ℕ) : C(U,ℝ) := testPair (U := U) (Nat.unpair j)

theorem testFunction_compact (j : ℕ) : HasCompactSupport (testFunction (U := U) j) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : U) ((Nat.unpair j).1 : ℝ))
  exact (subset_tsupport _).trans
    (denseSeq (SupportedTest (U := U) (Nat.unpair j).1) (Nat.unpair j).2).property

/-- Equality on the literal countable tests determines every locally finite
Radon measure. -/
theorem ext_of_test_integrals (μ ν : Measure U) [μ.Regular] [ν.Regular]
    (he : ∀ j : ℕ, ∫ x, testFunction (U := U) j x ∂μ =
      ∫ x, testFunction (U := U) j x ∂ν) : μ = ν := by
  apply ext_of_compact_integrals μ ν
  intro f hf
  obtain ⟨R,hR⟩ := hf.isBounded.subset_ball (0 : U)
  obtain ⟨n,hn⟩ := exists_nat_ge R
  have hfsub : tsupport f ⊆ closedBall 0 (n : ℝ) :=
    hR.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall hn))
  let f' : SupportedTest (U := U) n := ⟨f,hfsub⟩
  let E : Set (SupportedTest (U := U) n) :=
    {g | ∫ x, g.val x ∂μ = ∫ x, g.val x ∂ν}
  have hE : IsClosed E := isClosed_eq (continuous_integral_supported μ n)
    (continuous_integral_supported ν n)
  have hd : range (denseSeq (SupportedTest (U := U) n)) ⊆ E := by
    rintro g ⟨k,rfl⟩
    have hh := he (Nat.pair n k)
    simp only [testFunction,Nat.unpair_pair] at hh
    exact hh
  have hsub := closure_minimal hd hE
  rw [(denseRange_denseSeq (SupportedTest (U := U) n)).closure_range] at hsub
  exact hsub (mem_univ f')

end VV.BBEKLeafMeasureTests



