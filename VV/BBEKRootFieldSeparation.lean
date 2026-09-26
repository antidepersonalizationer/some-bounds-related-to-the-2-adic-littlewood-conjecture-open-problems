import VV.BBEKCompactLeafStabilizers
import VV.BBEKUpperRootTranslation

/-! Strong separation of actual canonical leaf fields on one conull set.
The exceptional set is independent of the translation parameter. Trivial
projective stabilizers are supplied by the proved compact-support theorem;
no EL nontransience conclusion is asserted here. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace VV.BBEKRootFieldSeparation
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKOrbit BBEKMautner
open BBEKRootLeafKernel BBEKOneRootCovariance BBEKOneRootUpper
open BBEKOneRootTranslation BBEKUpperRootTranslation BBEKLeafwiseStabilizer
open BBEKCompactLeafStabilizers
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

section General
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

def SeparatesRootOn (root : U → G) (η : X → Measure U) (S : Set X) : Prop :=
  ∀ q ∈ S, ∀ u : U, root u • q ∈ S → η (root u • q) = η q → u = 0

theorem zero_of_normalized_translate_eq (ν : Measure U) (u : U) (r : ℝ)
    (hbot : projectiveTranslationStabilizer ν = ⊥)
    (he : ν = ((translate (-u) ν) (ball 0 r))⁻¹ • translate (-u) ν)
    (hpos : 0 < (translate (-u) ν) (ball 0 r))
    (hfinite : (translate (-u) ν) (ball 0 r) ≠ ∞) : u = 0 := by
  let c := translate (-u) ν (ball 0 r)
  have hc0 : c ≠ 0 := hpos.ne'
  have hc : translate (-u) ν = c • ν := by
    calc
      translate (-u) ν = c • (c⁻¹ • translate (-u) ν) := by
        rw [smul_smul,ENNReal.mul_inv_cancel hc0 hfinite,one_smul]
      _ = c • ν := congrArg (fun ξ : Measure U => c • ξ) he.symm
  have hm : -u ∈ projectiveTranslationStabilizer ν := by
    refine ⟨c.toNNReal,?_,?_⟩
    · exact ENNReal.toNNReal_ne_zero.mpr ⟨hc0,hfinite⟩
    · simpa only [ENNReal.smul_def,ENNReal.coe_toNNReal (show c ≠ ∞ from hfinite)] using hc
  rw [hbot,AddSubgroup.mem_bot] at hm
  exact neg_eq_zero.mp hm

/-- One conull set works simultaneously for every translation parameter. -/
theorem separates_on_conull_set (μ : Measure X) (root : U → G)
    (η : X → Measure U) (r : ℝ)
    (hcov : ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      ∀ q ∈ S, ∀ u : U, root u • q ∈ S →
        η (root u • q) = ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q) ∧
        0 < (translate (-u) (η q)) (ball 0 r) ∧ (translate (-u) (η q)) (ball 0 r) ≠ ∞)
    (hbot : ∀ᵐ q ∂μ, projectiveTranslationStabilizer (η q) = ⊥) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧ SeparatesRootOn root η S := by
  obtain ⟨S,hS,hμS,hSprop⟩ := hcov
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hbot)
  have hμN : ∀ᵐ q ∂μ, q ∈ Nᶜ := by
    apply ae_iff.mpr
    simpa only [mem_compl_iff,not_not] using hN0
  refine ⟨S ∩ Nᶜ,hS.inter hNm.compl,hμS.and hμN,?_⟩
  intro q hq u hu he
  have hb : projectiveTranslationStabilizer (η q) = ⊥ := by
    by_contra hn
    exact hq.2 (hN hn)
  obtain ⟨hc,hp,hf⟩ := hSprop q hq.1 u hu.1
  rw [he] at hc
  exact zero_of_normalized_translate_eq (η q) u r hb hc hp hf
end General
/-- Strong separation for the same canonical real lower field. -/
theorem real_lower_separates_on_conull_set
    (μ : Measure X) [IsProbabilityMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure ℝ) (hn : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hc : IsConstructedRootFamily realSplit μ t r η)
    (hb : ∀ᵐ q ∂μ, projectiveTranslationStabilizer (η q) = ⊥) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      SeparatesRootOn (fun u : ℝ => x u 0) η S :=
  separates_on_conull_set μ (fun u : ℝ => x u 0) η r
    (canonical_real_lower_translation_on_conull_set μ hr η hn hc) hb

/-- The compact-support construction supplies all premises for real lower
separation, retaining the original field and its normalization radius. -/
theorem exists_real_lower_separating_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily realSplit μ t r η ∧
      ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
        SeparatesRootOn (fun u : ℝ => x u 0) η S := by
  obtain ⟨r,hr,η,hη,hgood,hc,hb⟩ :=
    exists_real_lower_trivial_stabilizer_data μ hδ hmass ht
  exact ⟨r,hr,η,hη,hgood,hc,real_lower_separates_on_conull_set μ hr η
    (hgood.mono fun _ h => h.2.2.1) hc (hb.mono fun _ h => h.2)⟩
/-- Strong separation for the same canonical real upper field. -/
theorem real_upper_separates_on_conull_set
    (μ : Measure X) [IsProbabilityMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure ℝ) (hn : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hc : IsConstructedUpperRootFamily realSplit μ t r η)
    (hb : ∀ᵐ q ∂μ, projectiveTranslationStabilizer (η q) = ⊥) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      SeparatesRootOn (fun u : ℝ => upperPoint u 0) η S :=
  separates_on_conull_set μ (fun u : ℝ => upperPoint u 0) η r
    (canonical_real_upper_translation_on_conull_set μ hr η hn hc) hb

/-- The compact-support construction supplies all premises for real upper
separation, retaining the original field and its normalization radius. -/
theorem exists_real_upper_separating_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily realSplit μ t r η ∧
      ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
        SeparatesRootOn (fun u : ℝ => upperPoint u 0) η S := by
  obtain ⟨r,hr,η,hη,hgood,hc,hb⟩ :=
    exists_real_upper_trivial_stabilizer_data μ hδ hmass ht
  exact ⟨r,hr,η,hη,hgood,hc,real_upper_separates_on_conull_set μ hr η
    (hgood.mono fun _ h => h.2.2.1) hc (hb.mono fun _ h => h.2)⟩
/-- Strong separation for the same canonical padic lower field. -/
theorem padic_lower_separates_on_conull_set
    (μ : Measure X) [IsProbabilityMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure Q2) (hn : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hc : IsConstructedRootFamily padicSplit μ t r η)
    (hb : ∀ᵐ q ∂μ, projectiveTranslationStabilizer (η q) = ⊥) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      SeparatesRootOn (fun u : Q2 => x 0 u) η S :=
  separates_on_conull_set μ (fun u : Q2 => x 0 u) η r
    (canonical_padic_lower_translation_on_conull_set μ hr η hn hc) hb

/-- The compact-support construction supplies all premises for padic lower
separation, retaining the original field and its normalization radius. -/
theorem exists_padic_lower_separating_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily padicSplit μ t r η ∧
      ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
        SeparatesRootOn (fun u : Q2 => x 0 u) η S := by
  obtain ⟨r,hr,η,hη,hgood,hc,hb⟩ :=
    exists_padic_lower_trivial_stabilizer_data μ hδ hmass ht
  exact ⟨r,hr,η,hη,hgood,hc,padic_lower_separates_on_conull_set μ hr η
    (hgood.mono fun _ h => h.2.2.1) hc (hb.mono fun _ h => h.2)⟩
/-- Strong separation for the same canonical padic upper field. -/
theorem padic_upper_separates_on_conull_set
    (μ : Measure X) [IsProbabilityMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure Q2) (hn : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hc : IsConstructedUpperRootFamily padicSplit μ t r η)
    (hb : ∀ᵐ q ∂μ, projectiveTranslationStabilizer (η q) = ⊥) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      SeparatesRootOn (fun u : Q2 => upperPoint 0 u) η S :=
  separates_on_conull_set μ (fun u : Q2 => upperPoint 0 u) η r
    (canonical_padic_upper_translation_on_conull_set μ hr η hn hc) hb

/-- The compact-support construction supplies all premises for padic upper
separation, retaining the original field and its normalization radius. -/
theorem exists_padic_upper_separating_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily padicSplit μ t r η ∧
      ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
        SeparatesRootOn (fun u : Q2 => upperPoint 0 u) η S := by
  obtain ⟨r,hr,η,hη,hgood,hc,hb⟩ :=
    exists_padic_upper_trivial_stabilizer_data μ hδ hmass ht
  exact ⟨r,hr,η,hη,hgood,hc,padic_upper_separates_on_conull_set μ hr η
    (hgood.mono fun _ h => h.2.2.1) hc (hb.mono fun _ h => h.2)⟩
end VV.BBEKRootFieldSeparation


