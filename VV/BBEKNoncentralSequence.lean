import VV.BBEKLowEntropyBackend
import VV.BBEKBowenLift

/-! The actual sequence front end for the remaining EL shearing argument.
Failure of local exceptional concentration supplies equal-field points in
arbitrarily small open quotient displacement neighborhoods. Their lifts
converge to the identity and stay outside the common centralizer. This file
does not assert the nontransience or positive-root-entropy conclusions. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal MatrixGroups
namespace VV.BBEKNoncentralSequence
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKMautner
open BBEKRootLeafKernel BBEKOneRootCovariance BBEKOneRootUpper
open BBEKExceptionalCentralizer BBEKLocalExceptional BBEKLowEntropyBackend
open BBEKBowenLift
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- A point where the exceptional condition fails has noncentral equal-field
partners in every open neighborhood. The partner stays in the original set. -/
theorem exists_nonlocal_point {U : Type*} [MeasurableSpace U]
    (C : Set G) (ηlo ηup : X → Measure U) (K : Set X)
    (hnot : ¬ LocalExceptionalSet C ηlo ηup K) :
    ∃ q ∈ K, ∀ O : Set X, IsOpen O → q ∈ O →
      ∃ z ∈ K ∩ O, ηlo z = ηlo q ∧ ηup z = ηup q ∧
        z ∉ centralizerOrbit C q := by
  classical
  by_contra h
  apply hnot
  intro q hq
  have hq' : ¬ ∀ O : Set X, IsOpen O → q ∈ O →
      ∃ z ∈ K ∩ O, ηlo z = ηlo q ∧ ηup z = ηup q ∧
        z ∉ centralizerOrbit C q := by
    intro hh
    exact h ⟨q,hq,hh⟩
  push_neg at hq'
  obtain ⟨O,hO,hqO,hz⟩ := hq'
  refine ⟨O,hO,hqO,?_⟩
  intro z hzKO hlo hup
  exact hz z hzKO hlo hup

/-- The small displacements are genuine matrices acting on the quotient;
no separate compatibility hypothesis between the points and matrices occurs. -/
theorem exists_noncentral_sequence {U : Type*} [MeasurableSpace U]
    (C : Set G) (ηlo ηup : X → Measure U) (K : Set X)
    (hnot : ¬ LocalExceptionalSet C ηlo ηup K) :
    ∃ q ∈ K, ∃ g : ℕ → G, Tendsto g atTop (𝓝 1) ∧
      (∀ n, dist (g n) 1 < 1 / ((n : ℝ) + 1)) ∧
      ∀ n, g n • q ∈ K ∧ ηlo (g n • q) = ηlo q ∧
        ηup (g n • q) = ηup q ∧ g n ∉ C := by
  classical
  obtain ⟨q,hq,hnear⟩ := exists_nonlocal_point C ηlo ηup K hnot
  have hex (n : ℕ) : ∃ g : G, dist g 1 < 1 / ((n : ℝ) + 1) ∧
      g • q ∈ K ∧ ηlo (g • q) = ηlo q ∧ ηup (g • q) = ηup q ∧ g ∉ C := by
    let O : Set X := (fun z : X => (q,z)) ⁻¹'
      displacementRelation (1 / ((n : ℝ) + 1))
    have hO : IsOpen O := (isOpen_displacementRelation _).preimage
      (continuous_const.prodMk continuous_id)
    have hqO : q ∈ O := diagonal_mem_displacementRelation (by positivity) q
    obtain ⟨z,hz,hlo,hup,hnorbit⟩ := hnear O hO hqO
    obtain ⟨g,hg,he⟩ := hz.2
    refine ⟨g,hg,?_,?_,?_,?_⟩
    · simpa only [← he] using hz.1
    · simpa only [← he] using hlo
    · simpa only [← he] using hup
    · intro hgC
      exact hnorbit ⟨g,hgC,he.symm⟩
  choose g hsmall hgood using hex
  refine ⟨q,hq,g,?_,hsmall,hgood⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun n => dist_nonneg) (fun n => (hsmall n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Along these lifts the actual quotient points converge to the base point. -/
theorem points_tendsto {g : ℕ → G} (hg : Tendsto g atTop (𝓝 1)) (q : X) :
    Tendsto (fun n => g n • q) atTop (𝓝 q) := by
  simpa only [one_smul] using hg.smul_const q

/-- From two possible noncentral root directions, one direction remains
noncentral on an infinite subsequence. -/
theorem fixed_branch_subsequence (P Q : ℕ → Prop) (h : ∀ n, P n ∨ Q n) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n)) ∨
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, Q (φ n)) := by
  classical
  by_cases hP : ∃ᶠ n in atTop, P n
  · exact Or.inl (extraction_of_frequently_atTop hP)
  · right
    have hnP : ∀ᶠ n in atTop, ¬ P n := not_frequently.mp hP
    exact extraction_of_eventually_atTop (hnP.mono fun n hn => (h n).resolve_left hn)


/-- Failure to lie in the common real-root centralizer is failure to commute
with at least one of the two actual matrix root groups. -/
theorem real_noncentral_direction {g : G} (h : g ∉ realCommonCentralizer) :
    (¬ ∀ u : ℝ, BBEKFiniteQuotients.lower u * g.1 = g.1 * BBEKFiniteQuotients.lower u) ∨
    (¬ ∀ u : ℝ, BBEKFiniteQuotients.upper u * g.1 = g.1 * BBEKFiniteQuotients.upper u) := by
  by_contra! hc
  apply h
  constructor
  · intro u
    change x u 0 * g = g * x u 0
    apply Prod.ext
    · exact hc.1 u
    · simp [x]
  · intro u
    change upperPoint u 0 * g = g * upperPoint u 0
    apply Prod.ext
    · exact hc.2 u
    · simp [upperPoint]

/-- The corresponding statement in the active 2-adic matrix factor. -/
theorem padic_noncentral_direction {g : G} (h : g ∉ padicCommonCentralizer) :
    (¬ ∀ u : Q2, BBEKFiniteQuotients.lower u * g.2 = g.2 * BBEKFiniteQuotients.lower u) ∨
    (¬ ∀ u : Q2, BBEKFiniteQuotients.upper u * g.2 = g.2 * BBEKFiniteQuotients.upper u) := by
  by_contra! hc
  apply h
  constructor
  · intro u
    change x 0 u * g = g * x 0 u
    apply Prod.ext
    · simp [x]
    · exact hc.1 u
  · intro u
    change upperPoint 0 u * g = g * upperPoint 0 u
    apply Prod.ext
    · simp [upperPoint]
    · exact hc.2 u

/-- One fixed real root direction is noncommuting along a subsequence.
The subsequence still tends to the identity and preserves every pointwise
property of the original sequence. -/
theorem real_noncentral_subsequence (g : ℕ → G)
    (hg : ∀ n, g n ∉ realCommonCentralizer) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∀ n, ¬ ∀ u : ℝ, BBEKFiniteQuotients.lower u * (g (φ n)).1 =
        (g (φ n)).1 * BBEKFiniteQuotients.lower u) ∨
       (∀ n, ¬ ∀ u : ℝ, BBEKFiniteQuotients.upper u * (g (φ n)).1 =
        (g (φ n)).1 * BBEKFiniteQuotients.upper u)) := by
  rcases fixed_branch_subsequence _ _ (fun n => real_noncentral_direction (hg n)) with
    ⟨φ,hφ,h⟩ | ⟨φ,hφ,h⟩
  · exact ⟨φ,hφ,Or.inl h⟩
  · exact ⟨φ,hφ,Or.inr h⟩

/-- One fixed 2-adic root direction is noncommuting along a subsequence. -/
theorem padic_noncentral_subsequence (g : ℕ → G)
    (hg : ∀ n, g n ∉ padicCommonCentralizer) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∀ n, ¬ ∀ u : Q2, BBEKFiniteQuotients.lower u * (g (φ n)).2 =
        (g (φ n)).2 * BBEKFiniteQuotients.lower u) ∨
       (∀ n, ¬ ∀ u : Q2, BBEKFiniteQuotients.upper u * (g (φ n)).2 =
        (g (φ n)).2 * BBEKFiniteQuotients.upper u)) := by
  rcases fixed_branch_subsequence _ _ (fun n => padic_noncentral_direction (hg n)) with
    ⟨φ,hφ,h⟩ | ⟨φ,hφ,h⟩
  · exact ⟨φ,hφ,Or.inl h⟩
  · exact ⟨φ,hφ,Or.inr h⟩

/-- Every positive measurable set supplies actual equal-field real-root
partners and identity-convergent matrix lifts, for the specified canonical
opposite-root families. No new choice of either family occurs. -/
theorem real_sequence_of_positive_set
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {tlo tup rlo rup : ℝ} (hrlo : 0 < rlo) (hrup : 0 < rup)
    (ηlo ηup : X → Measure ℝ) (hlo : Measurable ηlo) (hup : Measurable ηup)
    (hnlo : ∀ᵐ q ∂μ, ηlo q (ball 0 rlo) = 1)
    (hnup : ∀ᵐ q ∂μ, ηup q (ball 0 rup) = 1)
    (hclo : IsConstructedRootFamily realSplit μ tlo rlo ηlo)
    (hcup : IsConstructedUpperRootFamily realSplit μ tup rup ηup)
    (hrglo : ∀ᵐ q ∂μ, (ηlo q).Regular)
    (hrgup : ∀ᵐ q ∂μ, (ηup q).Regular)
    {K : Set X} (hK : MeasurableSet K) (hpos : μ K ≠ 0) :
    ∃ q ∈ K, ∃ g : ℕ → G, Tendsto g atTop (𝓝 1) ∧
      (∀ n, dist (g n) 1 < 1 / ((n : ℝ) + 1)) ∧
      ∀ n, g n • q ∈ K ∧ ηlo (g n • q) = ηlo q ∧
        ηup (g n • q) = ηup q ∧ g n ∉ realCommonCentralizer := by
  apply exists_noncentral_sequence
  intro hlocal
  exact hpos (real_local_exceptional_set_null μ hrlo hrup ηlo ηup hlo hup hnlo hnup
    hclo hcup hrglo hrgup hK hlocal)

/-- The same actual sequence construction for the 2-adic opposite-root pair. -/
theorem padic_sequence_of_positive_set
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {tlo tup rlo rup : ℝ} (hrlo : 0 < rlo) (hrup : 0 < rup)
    (ηlo ηup : X → Measure Q2) (hlo : Measurable ηlo) (hup : Measurable ηup)
    (hnlo : ∀ᵐ q ∂μ, ηlo q (ball 0 rlo) = 1)
    (hnup : ∀ᵐ q ∂μ, ηup q (ball 0 rup) = 1)
    (hclo : IsConstructedRootFamily padicSplit μ tlo rlo ηlo)
    (hcup : IsConstructedUpperRootFamily padicSplit μ tup rup ηup)
    (hrglo : ∀ᵐ q ∂μ, (ηlo q).Regular)
    (hrgup : ∀ᵐ q ∂μ, (ηup q).Regular)
    {K : Set X} (hK : MeasurableSet K) (hpos : μ K ≠ 0) :
    ∃ q ∈ K, ∃ g : ℕ → G, Tendsto g atTop (𝓝 1) ∧
      (∀ n, dist (g n) 1 < 1 / ((n : ℝ) + 1)) ∧
      ∀ n, g n • q ∈ K ∧ ηlo (g n • q) = ηlo q ∧
        ηup (g n • q) = ηup q ∧ g n ∉ padicCommonCentralizer := by
  apply exists_noncentral_sequence
  intro hlocal
  exact hpos (padic_local_exceptional_set_null μ hrlo hrup ηlo ηup hlo hup hnlo hnup
    hclo hcup hrglo hrgup hK hlocal)


/-- A ready-to-use real shearing sequence with the same literal pair of leaf
fields, actual quotient displacement, and one fixed noncommuting root. -/
theorem real_shearing_sequence_of_positive_set
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {tlo tup rlo rup : ℝ} (hrlo : 0 < rlo) (hrup : 0 < rup)
    (ηlo ηup : X → Measure ℝ) (hlo : Measurable ηlo) (hup : Measurable ηup)
    (hnlo : ∀ᵐ q ∂μ, ηlo q (ball 0 rlo) = 1)
    (hnup : ∀ᵐ q ∂μ, ηup q (ball 0 rup) = 1)
    (hclo : IsConstructedRootFamily realSplit μ tlo rlo ηlo)
    (hcup : IsConstructedUpperRootFamily realSplit μ tup rup ηup)
    (hrglo : ∀ᵐ q ∂μ, (ηlo q).Regular)
    (hrgup : ∀ᵐ q ∂μ, (ηup q).Regular)
    {K : Set X} (hK : MeasurableSet K) (hpos : μ K ≠ 0) :
    ∃ q ∈ K, ∃ g : ℕ → G, Tendsto g atTop (𝓝 1) ∧
      (∀ n, g n • q ∈ K ∧ ηlo (g n • q) = ηlo q ∧ ηup (g n • q) = ηup q) ∧
      ((∀ n, ¬ ∀ u : ℝ, BBEKFiniteQuotients.lower u * (g n).1 =
        (g n).1 * BBEKFiniteQuotients.lower u) ∨
       (∀ n, ¬ ∀ u : ℝ, BBEKFiniteQuotients.upper u * (g n).1 =
        (g n).1 * BBEKFiniteQuotients.upper u)) := by
  obtain ⟨q,hq,g,hg,_hsmall,hgood⟩ := real_sequence_of_positive_set μ hrlo hrup
    ηlo ηup hlo hup hnlo hnup hclo hcup hrglo hrgup hK hpos
  obtain ⟨φ,hφ,hbranch⟩ := real_noncentral_subsequence g (fun n => (hgood n).2.2.2)
  refine ⟨q,hq,fun n => g (φ n),hg.comp hφ.tendsto_atTop,?_,hbranch⟩
  intro n
  exact ⟨(hgood (φ n)).1,(hgood (φ n)).2.1,(hgood (φ n)).2.2.1⟩

/-- The corresponding complete front end in the 2-adic active factor. -/
theorem padic_shearing_sequence_of_positive_set
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {tlo tup rlo rup : ℝ} (hrlo : 0 < rlo) (hrup : 0 < rup)
    (ηlo ηup : X → Measure Q2) (hlo : Measurable ηlo) (hup : Measurable ηup)
    (hnlo : ∀ᵐ q ∂μ, ηlo q (ball 0 rlo) = 1)
    (hnup : ∀ᵐ q ∂μ, ηup q (ball 0 rup) = 1)
    (hclo : IsConstructedRootFamily padicSplit μ tlo rlo ηlo)
    (hcup : IsConstructedUpperRootFamily padicSplit μ tup rup ηup)
    (hrglo : ∀ᵐ q ∂μ, (ηlo q).Regular)
    (hrgup : ∀ᵐ q ∂μ, (ηup q).Regular)
    {K : Set X} (hK : MeasurableSet K) (hpos : μ K ≠ 0) :
    ∃ q ∈ K, ∃ g : ℕ → G, Tendsto g atTop (𝓝 1) ∧
      (∀ n, g n • q ∈ K ∧ ηlo (g n • q) = ηlo q ∧ ηup (g n • q) = ηup q) ∧
      ((∀ n, ¬ ∀ u : Q2, BBEKFiniteQuotients.lower u * (g n).2 =
        (g n).2 * BBEKFiniteQuotients.lower u) ∨
       (∀ n, ¬ ∀ u : Q2, BBEKFiniteQuotients.upper u * (g n).2 =
        (g n).2 * BBEKFiniteQuotients.upper u)) := by
  obtain ⟨q,hq,g,hg,_hsmall,hgood⟩ := padic_sequence_of_positive_set μ hrlo hrup
    ηlo ηup hlo hup hnlo hnup hclo hcup hrglo hrgup hK hpos
  obtain ⟨φ,hφ,hbranch⟩ := padic_noncentral_subsequence g (fun n => (hgood n).2.2.2)
  refine ⟨q,hq,fun n => g (φ n),hg.comp hφ.tendsto_atTop,?_,hbranch⟩
  intro n
  exact ⟨(hgood (φ n)).1,(hgood (φ n)).2.1,(hgood (φ n)).2.2.1⟩

end VV.BBEKNoncentralSequence
