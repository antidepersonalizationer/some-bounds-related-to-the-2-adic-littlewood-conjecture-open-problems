import VV.BBEKRootFieldSeparation
import VV.BBEKLocalExceptional

/-! The proved terminal contradictions for the two EL alternatives in the
compact arithmetic application. This file does not prove that positive entropy
produces either alternative. Its explicit disjunction is an interface to the
remaining nontransience/shearing theorem, never an axiom or an admitted proof. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace VV.BBEKLowEntropyBackend
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKOrbit BBEKMautner
open BBEKRootLeafKernel BBEKOneRootCovariance BBEKOneRootUpper
open BBEKLeafwiseStabilizer BBEKCompactLeafStabilizers BBEKRootFieldSeparation
open BBEKExceptionalCentralizer BBEKLocalExceptional
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- A nonzero root displacement between points of the specified conull set
that leaves the literal canonical leaf measure unchanged. -/
def EqualFieldRootReturn {U : Type*} [MeasurableSpace U] [Zero U]
    (root : U → G) (η : X → Measure U) (S : Set X) : Prop :=
  ∃ q ∈ S, ∃ u : U, u ≠ 0 ∧ root u • q ∈ S ∧ η (root u • q) = η q

/-- The precise local exceptional condition discharged by the proved
conditional-probability and arithmetic-orbit argument. -/
def LocalExceptionalSet {U : Type*} [MeasurableSpace U]
    (C : Set G) (ηlo ηup : X → Measure U) (K : Set X) : Prop :=
  ∀ q ∈ K, ∃ O : Set X, IsOpen O ∧ q ∈ O ∧
    ∀ z ∈ K ∩ O, ηlo z = ηlo q → ηup z = ηup q → z ∈ centralizerOrbit C q
/-- One full-measure set excludes both equal-field root returns and every
positive-mass local exceptional set, for the same real canonical pair. -/
theorem real_pair_terminal
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {tlo tup rlo rup : ℝ} (hrlo : 0 < rlo) (hrup : 0 < rup)
    (ηlo ηup : X → Measure ℝ) (hlo : Measurable ηlo) (hup : Measurable ηup)
    (hnlo : ∀ᵐ q ∂μ, ηlo q (ball 0 rlo) = 1)
    (hnup : ∀ᵐ q ∂μ, ηup q (ball 0 rup) = 1)
    (hclo : IsConstructedRootFamily realSplit μ tlo rlo ηlo)
    (hcup : IsConstructedUpperRootFamily realSplit μ tup rup ηup)
    (hrglo : ∀ᵐ q ∂μ, (ηlo q).Regular)
    (hrgup : ∀ᵐ q ∂μ, (ηup q).Regular)
    (hblo : ∀ᵐ q ∂μ, projectiveTranslationStabilizer (ηlo q) = ⊥)
    (hbup : ∀ᵐ q ∂μ, projectiveTranslationStabilizer (ηup q) = ⊥) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      ¬ (EqualFieldRootReturn (fun u : ℝ => x u 0) ηlo S ∨
        EqualFieldRootReturn (fun u : ℝ => upperPoint u 0) ηup S ∨
        ∃ K : Set X, MeasurableSet K ∧ μ K ≠ 0 ∧
          LocalExceptionalSet realCommonCentralizer ηlo ηup K) := by
  obtain ⟨Slo,hSlo,hμSlo,hSepLo⟩ :=
    real_lower_separates_on_conull_set μ hrlo ηlo hnlo hclo hblo
  obtain ⟨Sup,hSup,hμSup,hSepUp⟩ :=
    real_upper_separates_on_conull_set μ hrup ηup hnup hcup hbup
  refine ⟨Slo ∩ Sup,hSlo.inter hSup,hμSlo.and hμSup,?_⟩
  rintro (⟨q,hq,u,hu,huS,he⟩ | ⟨q,hq,u,hu,huS,he⟩ | ⟨K,hK,hKpos,hlocal⟩)
  · exact hu (hSepLo q hq.1 u huS.1 he)
  · exact hu (hSepUp q hq.2 u huS.2 he)
  · exact hKpos (real_local_exceptional_set_null μ hrlo hrup ηlo ηup hlo hup hnlo hnup
      hclo hcup hrglo hrgup hK hlocal)

/-- The literal compact-support constructions supply the pair and all
hypotheses of the terminal exclusion. No EL dichotomy is claimed. -/
theorem exists_real_pair_terminal_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ rlo rup : ℝ, 0 < rlo ∧ 0 < rup ∧ ∃ ηlo ηup : X → Measure ℝ,
      Measurable ηlo ∧ Measurable ηup ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (ηlo q) ∧ (ηlo q).Regular ∧ ηlo q (ball 0 rlo) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < ηlo q (ball 0 ε)) ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (ηup q) ∧ (ηup q).Regular ∧ ηup q (ball 0 rup) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < ηup q (ball 0 ε)) ∧
      IsConstructedRootFamily realSplit μ t rlo ηlo ∧
      IsConstructedUpperRootFamily realSplit μ t rup ηup ∧
      ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
        ¬ (EqualFieldRootReturn (fun u : ℝ => x u 0) ηlo S ∨
          EqualFieldRootReturn (fun u : ℝ => upperPoint u 0) ηup S ∨
          ∃ K : Set X, MeasurableSet K ∧ μ K ≠ 0 ∧
            LocalExceptionalSet realCommonCentralizer ηlo ηup K) := by
  obtain ⟨rlo,hrlo,ηlo,hlo,hgoodlo,hclo,hblo⟩ :=
    exists_real_lower_trivial_stabilizer_data μ hδ hmass ht
  obtain ⟨rup,hrup,ηup,hup,hgoodup,hcup,hbup⟩ :=
    exists_real_upper_trivial_stabilizer_data μ hδ hmass ht
  exact ⟨rlo,rup,hrlo,hrup,ηlo,ηup,hlo,hup,hgoodlo,hgoodup,hclo,hcup,
    real_pair_terminal μ hrlo hrup ηlo ηup hlo hup
      (hgoodlo.mono fun _ h => h.2.2.1) (hgoodup.mono fun _ h => h.2.2.1) hclo hcup
      (hgoodlo.mono fun _ h => h.2.1) (hgoodup.mono fun _ h => h.2.1)
      (hblo.mono fun _ h => h.2) (hbup.mono fun _ h => h.2)⟩
/-- One full-measure set excludes both equal-field root returns and every
positive-mass local exceptional set, for the same padic canonical pair. -/
theorem padic_pair_terminal
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {tlo tup rlo rup : ℝ} (hrlo : 0 < rlo) (hrup : 0 < rup)
    (ηlo ηup : X → Measure Q2) (hlo : Measurable ηlo) (hup : Measurable ηup)
    (hnlo : ∀ᵐ q ∂μ, ηlo q (ball 0 rlo) = 1)
    (hnup : ∀ᵐ q ∂μ, ηup q (ball 0 rup) = 1)
    (hclo : IsConstructedRootFamily padicSplit μ tlo rlo ηlo)
    (hcup : IsConstructedUpperRootFamily padicSplit μ tup rup ηup)
    (hrglo : ∀ᵐ q ∂μ, (ηlo q).Regular)
    (hrgup : ∀ᵐ q ∂μ, (ηup q).Regular)
    (hblo : ∀ᵐ q ∂μ, projectiveTranslationStabilizer (ηlo q) = ⊥)
    (hbup : ∀ᵐ q ∂μ, projectiveTranslationStabilizer (ηup q) = ⊥) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      ¬ (EqualFieldRootReturn (fun u : Q2 => x 0 u) ηlo S ∨
        EqualFieldRootReturn (fun u : Q2 => upperPoint 0 u) ηup S ∨
        ∃ K : Set X, MeasurableSet K ∧ μ K ≠ 0 ∧
          LocalExceptionalSet padicCommonCentralizer ηlo ηup K) := by
  obtain ⟨Slo,hSlo,hμSlo,hSepLo⟩ :=
    padic_lower_separates_on_conull_set μ hrlo ηlo hnlo hclo hblo
  obtain ⟨Sup,hSup,hμSup,hSepUp⟩ :=
    padic_upper_separates_on_conull_set μ hrup ηup hnup hcup hbup
  refine ⟨Slo ∩ Sup,hSlo.inter hSup,hμSlo.and hμSup,?_⟩
  rintro (⟨q,hq,u,hu,huS,he⟩ | ⟨q,hq,u,hu,huS,he⟩ | ⟨K,hK,hKpos,hlocal⟩)
  · exact hu (hSepLo q hq.1 u huS.1 he)
  · exact hu (hSepUp q hq.2 u huS.2 he)
  · exact hKpos (padic_local_exceptional_set_null μ hrlo hrup ηlo ηup hlo hup hnlo hnup
      hclo hcup hrglo hrgup hK hlocal)

/-- The literal compact-support constructions supply the pair and all
hypotheses of the terminal exclusion. No EL dichotomy is claimed. -/
theorem exists_padic_pair_terminal_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ rlo rup : ℝ, 0 < rlo ∧ 0 < rup ∧ ∃ ηlo ηup : X → Measure Q2,
      Measurable ηlo ∧ Measurable ηup ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (ηlo q) ∧ (ηlo q).Regular ∧ ηlo q (ball 0 rlo) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < ηlo q (ball 0 ε)) ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (ηup q) ∧ (ηup q).Regular ∧ ηup q (ball 0 rup) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < ηup q (ball 0 ε)) ∧
      IsConstructedRootFamily padicSplit μ t rlo ηlo ∧
      IsConstructedUpperRootFamily padicSplit μ t rup ηup ∧
      ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
        ¬ (EqualFieldRootReturn (fun u : Q2 => x 0 u) ηlo S ∨
          EqualFieldRootReturn (fun u : Q2 => upperPoint 0 u) ηup S ∨
          ∃ K : Set X, MeasurableSet K ∧ μ K ≠ 0 ∧
            LocalExceptionalSet padicCommonCentralizer ηlo ηup K) := by
  obtain ⟨rlo,hrlo,ηlo,hlo,hgoodlo,hclo,hblo⟩ :=
    exists_padic_lower_trivial_stabilizer_data μ hδ hmass ht
  obtain ⟨rup,hrup,ηup,hup,hgoodup,hcup,hbup⟩ :=
    exists_padic_upper_trivial_stabilizer_data μ hδ hmass ht
  exact ⟨rlo,rup,hrlo,hrup,ηlo,ηup,hlo,hup,hgoodlo,hgoodup,hclo,hcup,
    padic_pair_terminal μ hrlo hrup ηlo ηup hlo hup
      (hgoodlo.mono fun _ h => h.2.2.1) (hgoodup.mono fun _ h => h.2.2.1) hclo hcup
      (hgoodlo.mono fun _ h => h.2.1) (hgoodup.mono fun _ h => h.2.1)
      (hblo.mono fun _ h => h.2) (hbup.mono fun _ h => h.2)⟩
end VV.BBEKLowEntropyBackend
