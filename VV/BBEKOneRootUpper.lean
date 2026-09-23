import VV.BBEKRootWeyl
import VV.BBEKOneRootCovariance

/-! Upper-root conditional families transported through the actual arithmetic
Weyl action. Its minus sign is retained in the root parameter. -/
noncomputable section
open Set MeasureTheory Filter Metric Topology
open scoped ENNReal
namespace VV.BBEKOneRootUpper
open BBEKDynamics BBEKQuotient BBEKRootWeyl BBEKRootLeafKernel BBEKOneRootCovariance
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

section General
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]

def negateMeasure (ν : Measure U) : Measure U := ν.map (fun u => -u)

theorem measurable_negateMeasure : Measurable (negateMeasure (U := U)) :=
  Measure.measurable_map _ measurable_neg

theorem negateMeasure_ball (ν : Measure U) (r : ℝ) :
    negateMeasure ν (ball 0 r)=ν (ball 0 r) := by
  rw [negateMeasure,Measure.map_apply measurable_neg isOpen_ball.measurableSet]
  congr 1
  ext u
  simp [mem_ball,dist_zero_right]

theorem negateMeasure_locallyFinite (ν : Measure U) [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (negateMeasure ν) := by
  constructor
  intro u
  obtain ⟨s,hs,hopen,hfinite⟩ := ν.exists_isOpen_measure_lt_top (-u)
  refine ⟨(fun v : U => -v) ⁻¹' s,(hopen.preimage continuous_neg).mem_nhds hs,?_⟩
  rw [negateMeasure,Measure.map_apply measurable_neg (hopen.preimage continuous_neg).measurableSet]
  simpa only [preimage_preimage,Function.comp_def,neg_neg,preimage_id'] using hfinite

theorem negateMeasure_regular (ν : Measure U) [ν.Regular] : (negateMeasure ν).Regular :=
  Measure.Regular.map (Homeomorph.neg U)

theorem negateMeasure_smul (a : ℝ≥0∞) (ν : Measure U) :
    negateMeasure (a • ν)=a • negateMeasure ν := Measure.map_smul _ _ _

theorem negateMeasure_scaling (ν : Measure U) (σ : U ≃ₜ U)
    (hσ : ∀u, σ (-u)= -σ u) :
    negateMeasure (ν.map σ)=(negateMeasure ν).map σ := by
  unfold negateMeasure
  rw [Measure.map_map measurable_neg σ.measurable,Measure.map_map σ.measurable measurable_neg]
  congr 1
  funext u
  exact (hσ u).symm

def upperFamily (η : X → Measure U) : X → Measure U :=
  fun q => negateMeasure (η (W⁻¹ • q))

theorem measurable_upperFamily {η : X → Measure U} (hη : Measurable η) :
    Measurable (upperFamily η) :=
  measurable_negateMeasure.comp (hη.comp (continuous_const_smul W⁻¹).measurable)

theorem upperFamily_properties (μ : Measure X) (η : X → Measure U) {r : ℝ}
    (hgood : ∀ᵐ q ∂reflectedMeasure μ,
      IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r)=1 ∧
        ∀ε : ℝ, 0<ε → 0<η q (ball 0 ε)) :
    ∀ᵐ q ∂μ, IsLocallyFiniteMeasure (upperFamily η q) ∧ (upperFamily η q).Regular ∧
      upperFamily η q (ball 0 r)=1 ∧
      ∀ε : ℝ, 0<ε → 0<upperFamily η q (ball 0 ε) := by
  have hp := ae_of_ae_map (continuous_const_smul W⁻¹).measurable.aemeasurable hgood
  filter_upwards [hp] with q hq
  letI := hq.1
  letI := hq.2.1
  refine ⟨negateMeasure_locallyFinite _,negateMeasure_regular _,?_,?_⟩
  · exact (negateMeasure_ball _ r).trans hq.2.2.1
  · intro ε hε
    change 0<negateMeasure _ (ball 0 ε)
    rw [negateMeasure_ball]
    exact hq.2.2.2 ε hε

theorem upperFamily_covariance (μ : Measure X) (η : X → Measure U)
    (σ : U ≃ₜ U) (hσ : ∀u, σ (-u)= -σ u) (t r : ℝ)
    (hcov : ∀ᵐ q ∂reflectedMeasure μ,
      η (psi t 1 • q)=((η q).map σ (ball 0 r))⁻¹ • (η q).map σ ∧
      0<(η q).map σ (ball 0 r) ∧ (η q).map σ (ball 0 r)≠∞) :
    ∀ᵐ q ∂μ,
      upperFamily η ((psi t 1)⁻¹ • q)=
        ((upperFamily η q).map σ (ball 0 r))⁻¹ • (upperFamily η q).map σ ∧
      0<(upperFamily η q).map σ (ball 0 r) ∧
        (upperFamily η q).map σ (ball 0 r)≠∞ := by
  have hc := ae_of_ae_map (continuous_const_smul W⁻¹).measurable.aemeasurable hcov
  filter_upwards [hc] with q hq
  have haction : W⁻¹ • ((psi t 1)⁻¹ • q)=psi t 1 • (W⁻¹ • q) := by
    simpa only [psi_neg,inv_inv] using inverse_W_psi_action (-t) (-1) q
  have he : (upperFamily η q).map σ=negateMeasure ((η (W⁻¹ • q)).map σ) :=
    (negateMeasure_scaling _ σ hσ).symm
  rw [he,negateMeasure_ball]
  refine ⟨?_,hq.2.1,hq.2.2⟩
  change negateMeasure (η (W⁻¹ • ((psi t 1)⁻¹ • q)))=_
  rw [haction,hq.1,negateMeasure_smul]
end General

def IsConstructedUpperRootFamily {B U : Type*}
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
    [SecondCountableTopology U] [StandardBorelSpace U] [SigmaCompactSpace U]
    (s : BBEKGaussChart.GroupParams ≃ₜ B × U) (μ : Measure X) [IsProbabilityMeasure μ]
    (t r : ℝ) (η : X → Measure U) : Prop :=
  ∃η₀ : X → Measure U,
    IsConstructedRootFamily s (reflectedMeasure μ) t r η₀ ∧ η=upperFamily η₀

theorem exists_real_upper_covariant_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K=1)
    {t : ℝ} (ht : Real.log 2≤t)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∃r : ℝ, 0<r ∧ ∃η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r)=1 ∧
        ∀ε : ℝ, 0<ε → 0<η q (ball 0 ε)) ∧
      (∀ᵐ q ∂μ,
        η ((psi t 1)⁻¹ • q)=((η q).map (realLeafScaling t) (ball 0 r))⁻¹ •
          (η q).map (realLeafScaling t) ∧
        0<(η q).map (realLeafScaling t) (ball 0 r) ∧
          (η q).map (realLeafScaling t) (ball 0 r)≠∞) ∧
      IsConstructedUpperRootFamily realSplit μ t r η := by
  obtain ⟨hK',hμK'⟩ := reflectedMeasure_compact_mass μ hK hμK
  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ := exists_real_lower_covariant_data
    (reflectedMeasure μ) hK' hμK' ht (reflectedMeasure_inverse_invariant μ t 1 hA)
  exact ⟨r,hr,upperFamily η,measurable_upperFamily hη,upperFamily_properties μ η hgood,
    upperFamily_covariance μ η (realLeafScaling t)
      (fun u => by simp [realLeafScaling]) t r hcov,η,hcanonical,rfl⟩

theorem exists_padic_upper_covariant_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K=1)
    {t : ℝ} (ht : Real.log 2≤t)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∃r : ℝ, 0<r ∧ ∃η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r)=1 ∧
        ∀ε : ℝ, 0<ε → 0<η q (ball 0 ε)) ∧
      (∀ᵐ q ∂μ,
        η ((psi t 1)⁻¹ • q)=((η q).map (padicLeafScaling 1) (ball 0 r))⁻¹ •
          (η q).map (padicLeafScaling 1) ∧
        0<(η q).map (padicLeafScaling 1) (ball 0 r) ∧
          (η q).map (padicLeafScaling 1) (ball 0 r)≠∞) ∧
      IsConstructedUpperRootFamily padicSplit μ t r η := by
  obtain ⟨hK',hμK'⟩ := reflectedMeasure_compact_mass μ hK hμK
  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ := exists_padic_lower_covariant_data
    (reflectedMeasure μ) hK' hμK' ht (reflectedMeasure_inverse_invariant μ t 1 hA)
  exact ⟨r,hr,upperFamily η,measurable_upperFamily hη,upperFamily_properties μ η hgood,
    upperFamily_covariance μ η (padicLeafScaling 1)
      (fun u => by simp [padicLeafScaling]) t r hcov,η,hcanonical,rfl⟩

end VV.BBEKOneRootUpper
