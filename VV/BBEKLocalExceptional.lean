import VV.BBEKExceptionalOrbitNull
import VV.BBEKPairExceptional
import Mathlib.Topology.Compactness.Lindelof

/-! The local exceptional alternative has zero mass. Second countability
turns local containment in null orbits into a null set, without requiring a
single global orbit or an ergodic-decomposition theorem. The actual pair of
canonical leaf fields supplies the invariant conditional probabilities. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology ENNReal MatrixGroups
namespace VV.BBEKLocalExceptional
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKRootLeafKernel
open BBEKOneRootCovariance BBEKOneRootUpper BBEKExceptionalCentralizer
open BBEKCanonicalExceptional BBEKConditionalLeafFibres BBEKExceptionalOrbitNull
open BBEKPairExceptional
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Nonempty X := ⟨basePoint⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- A set locally contained in null sets is null in a second-countable space.
No measurability of the set itself or of the null-set assignment is needed. -/
theorem null_of_locally_contained_in_null_sets
    {Z : Type*} [TopologicalSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z]
    (ν : Measure Z) (K : Set Z) (R : Z → Set Z) (hnull : ∀ q, ν (R q) = 0)
    (hlocal : ∀ q ∈ K, ∃ O : Set Z, IsOpen O ∧ q ∈ O ∧ K ∩ O ⊆ R q) : ν K = 0 := by
  classical
  choose O hO hqO hsub using hlocal
  let W : K → Set Z := fun q => O q q.property
  have hcover : K ⊆ ⋃ q : K, W q := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q,hq⟩,hqO q hq⟩
  obtain ⟨I,hI,hcover'⟩ := (HereditarilyLindelof_LindelofSets K).elim_countable_subcover
    W (fun q => hO q q.property) hcover
  have hz : ν (⋃ q ∈ I, K ∩ W q) = 0 :=
    (measure_biUnion_null_iff hI).mpr (fun q _ =>
      measure_mono_null (hsub q q.property) (hnull q))
  apply measure_mono_null _ hz
  intro z hzK
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp (hcover' hzK)
  exact mem_iUnion₂.mpr ⟨q,hq,hzK,hzq⟩

/-- A measure carried by one observable fibre cannot charge a set where
locally every pair with the same observable belongs to a common null orbit. -/
theorem null_of_fibre_and_local_orbits
    {Z B : Type*} [TopologicalSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z]
    (ν : Measure Z) (f : Z → B) (b : B) (hfibre : ∀ᵐ z ∂ν, f z = b)
    (K : Set Z) (R : Z → Set Z) (hnull : ∀ q, ν (R q) = 0)
    (hlocal : ∀ q ∈ K, ∃ O : Set Z, IsOpen O ∧ q ∈ O ∧
      ∀ z ∈ K ∩ O, f z = f q → z ∈ R q) : ν K = 0 := by
  let L := K ∩ {z | f z = b}
  have hL : ν L = 0 := null_of_locally_contained_in_null_sets ν L R hnull (by
    intro q hq
    obtain ⟨O,hO,hqO,hsub⟩ := hlocal q hq.1
    refine ⟨O,hO,hqO,?_⟩
    intro z hz
    exact hsub z ⟨hz.1.1,hz.2⟩ (hz.1.2.trans hq.2.symm))
  have hEq : L =ᵐ[ν] K := by
    filter_upwards [hfibre] with z hz
    apply propext
    exact ⟨fun h => h.1,fun h => ⟨h,hz⟩⟩
  exact (measure_congr hEq).symm.trans hL

/-- The literal conditionals reconstruct the original measure on every
measurable set, so almost-sure conditional nullity implies ambient nullity. -/
theorem null_of_condDistrib_id_null
    {Z B : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableSpace B] (μ : Measure Z) [IsFiniteMeasure μ]
    (f : Z → B) (hf : Measurable f) {K : Set Z} (hK : MeasurableSet K)
    (hnull : ∀ᵐ q ∂μ, condDistrib id f μ (f q) K = 0) : μ K = 0 := by
  have he := setLIntegral_condDistrib_of_measurableSet (μ := μ) hf aemeasurable_id hK
    (MeasurableSet.univ : MeasurableSet[(inferInstance : MeasurableSpace B).comap f] univ)
  simp only [Measure.restrict_univ,univ_inter,preimage_id] at he
  rw [lintegral_congr_ae hnull,lintegral_zero] at he
  exact he.symm
/-- On the actual arithmetic quotient, the local real-root exceptional
alternative has zero ambient measure. The local same-pair implication is the
remaining EL alternative's content; all conditioning and orbit-null steps
are proved here. -/
theorem real_local_exceptional_set_null
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {tlo tup rlo rup : ℝ} (hrlo : 0 < rlo) (hrup : 0 < rup)
    (ηlo ηup : X → Measure ℝ) (hlo : Measurable ηlo) (hup : Measurable ηup)
    (hnlo : ∀ᵐ q ∂μ, ηlo q (ball 0 rlo) = 1)
    (hnup : ∀ᵐ q ∂μ, ηup q (ball 0 rup) = 1)
    (hclo : IsConstructedRootFamily realSplit μ tlo rlo ηlo)
    (hcup : IsConstructedUpperRootFamily realSplit μ tup rup ηup)
    (hrglo : ∀ᵐ q ∂μ, (ηlo q).Regular)
    (hrgup : ∀ᵐ q ∂μ, (ηup q).Regular)
    {K : Set X} (hK : MeasurableSet K)
    (hlocal : ∀ q ∈ K, ∃ O : Set X, IsOpen O ∧ q ∈ O ∧
      ∀ z ∈ K ∩ O, ηlo z = ηlo q → ηup z = ηup q →
        z ∈ centralizerOrbit realCommonCentralizer q) : μ K = 0 := by
  have hh := real_pair_conditionals μ hrlo hrup ηlo ηup hlo hup hnlo hnup
    hclo hcup hrglo hrgup
  have hi := ae_of_ae_map (hlo.prodMk hup).aemeasurable hh.1
  apply null_of_condDistrib_id_null μ (fun q => (ηlo q,ηup q)) (hlo.prodMk hup) hK
  filter_upwards [hi,hh.2.2] with q hqi hqf
  rw [psi_zero_one] at hqi
  apply null_of_fibre_and_local_orbits
    (condDistrib id (fun q => (ηlo q,ηup q)) μ (ηlo q,ηup q))
    (fun z => (ηlo z,ηup z)) (ηlo q,ηup q)
    (hqf.mono fun z hz => Prod.ext hz.1 hz.2) K
    (centralizerOrbit realCommonCentralizer)
    (fun z => real_centralizer_orbit_null _ z hqi)
  intro z hz
  obtain ⟨O,hO,hzO,hsub⟩ := hlocal z hz
  exact ⟨O,hO,hzO,fun w hw he => hsub w hw (congrArg Prod.fst he) (congrArg Prod.snd he)⟩
/-- On the actual arithmetic quotient, the local padic-root exceptional
alternative has zero ambient measure. The local same-pair implication is the
remaining EL alternative's content; all conditioning and orbit-null steps
are proved here. -/
theorem padic_local_exceptional_set_null
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {tlo tup rlo rup : ℝ} (hrlo : 0 < rlo) (hrup : 0 < rup)
    (ηlo ηup : X → Measure Q2) (hlo : Measurable ηlo) (hup : Measurable ηup)
    (hnlo : ∀ᵐ q ∂μ, ηlo q (ball 0 rlo) = 1)
    (hnup : ∀ᵐ q ∂μ, ηup q (ball 0 rup) = 1)
    (hclo : IsConstructedRootFamily padicSplit μ tlo rlo ηlo)
    (hcup : IsConstructedUpperRootFamily padicSplit μ tup rup ηup)
    (hrglo : ∀ᵐ q ∂μ, (ηlo q).Regular)
    (hrgup : ∀ᵐ q ∂μ, (ηup q).Regular)
    {K : Set X} (hK : MeasurableSet K)
    (hlocal : ∀ q ∈ K, ∃ O : Set X, IsOpen O ∧ q ∈ O ∧
      ∀ z ∈ K ∩ O, ηlo z = ηlo q → ηup z = ηup q →
        z ∈ centralizerOrbit padicCommonCentralizer q) : μ K = 0 := by
  have hh := padic_pair_conditionals μ hrlo hrup ηlo ηup hlo hup hnlo hnup
    hclo hcup hrglo hrgup
  have hi := ae_of_ae_map (hlo.prodMk hup).aemeasurable hh.1
  apply null_of_condDistrib_id_null μ (fun q => (ηlo q,ηup q)) (hlo.prodMk hup) hK
  filter_upwards [hi,hh.2.2] with q hqi hqf
  rw [psi_log_two_zero] at hqi
  apply null_of_fibre_and_local_orbits
    (condDistrib id (fun q => (ηlo q,ηup q)) μ (ηlo q,ηup q))
    (fun z => (ηlo z,ηup z)) (ηlo q,ηup q)
    (hqf.mono fun z hz => Prod.ext hz.1 hz.2) K
    (centralizerOrbit padicCommonCentralizer)
    (fun z => padic_centralizer_orbit_null _ z hqi)
  intro z hz
  obtain ⟨O,hO,hzO,hsub⟩ := hlocal z hz
  exact ⟨O,hO,hzO,fun w hw he => hsub w hw (congrArg Prod.fst he) (congrArg Prod.snd he)⟩
end VV.BBEKLocalExceptional

