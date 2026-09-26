import VV.BBEKShearLimit

/-! A single large set giving both real paired return times and nondegenerate
root parameters for the genuine SL₂ quadratic shear. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal MatrixGroups
namespace VV.BBEKPairedShear
open BBEKPairedReturnTimes BBEKQuadraticScale BBEKShearFamilyNonconcentration

variable {F Z : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
  [ProperSpace F] [SecondCountableTopology F] [MeasurableSpace Z]
  {μ : Measure Z} [IsProbabilityMeasure μ] {T : Z → Z}

/-- Uniform leaf nonconcentration and the proved Hopf estimate give a single
large set of base points. For every two such points and every sufficiently
small noncentral matrix displacement, actual scales and a common return time
are constructed. At that time, every root bad set of mass at most one half
can be avoided while retaining a uniform nonzero shearing polynomial. -/
theorem exists_paired_shear_good_set (hT : MeasurePreserving T μ μ)
    (S : Set Z) (hS : MeasurableSet S) (hSsmall : μ.real Sᶜ < 1/20000)
    (η : Z → Measure F) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnorm : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hnoatom : ∀ᵐ q ∂μ, NoAtoms (η q))
    {a : F} (ha : ‖a‖ = 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Q G : Set Z,
      MeasurableSet Q ∧ Q ⊆ S ∧ MeasurableSet G ∧ (99 / 100 : ℝ) < μ.real G ∧
      ∀ x ∈ G, ∀ y ∈ G, ∀ g : SL(2,F),
        ‖g 0 0-g 1 1‖ ≤ 1 → ‖g 0 1‖ ≤ 1 →
        (¬∀ u : F, BBEKFiniteQuotients.lower u*g = g*BBEKFiniteQuotients.lower u) →
        ∃ s t k : ℕ, k < min s (t / 2) / 4+1 ∧
          T^[k] x ∈ Q ∧ T^[k] y ∈ Q ∧
          T^[shearTime s t k] x ∈ Q ∧ T^[shearTime s t k] y ∈ Q ∧
          ‖linearCoefficient a g (extraTime s t k)‖ ≤ 1 ∧
          ‖quadraticCoefficient a g k (extraTime s t k)‖ ≤ 1 ∧
          ∀ D : Set F, η (T^[k] x) D ≤ (1/2 : ℝ≥0∞) →
            ∃ v : F, ‖v‖ < r ∧ v ∉ D ∧
              δ < ‖linearCoefficient a g (extraTime s t k)*v +
                quadraticCoefficient a g k (extraTime s t k)*v^2‖ := by
  classical
  obtain ⟨δ,hδ,Q₀,hQ₀,hQmass,hbound⟩ :=
    exists_uniform_leaf_sublevel_good_set η hη hr hnorm hnoatom
      (by norm_num : (0 : ℝ) < 1/16) (by norm_num : (1/16 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 1/20000) (by norm_num : (0 : ℝ≥0∞) < 1/4)
  let N : Set Z := {q | η q (ball 0 r) = 1}
  have hN : MeasurableSet N :=
    (measurableSet_singleton (1 : ℝ≥0∞)).preimage
      ((Measure.measurable_coe measurableSet_ball).comp hη)
  let Q₁ := Q₀ ∩ N
  let Q := Q₁ ∩ S
  have hQ₁ : MeasurableSet Q₁ := hQ₀.inter hN
  have hQ : MeasurableSet Q := hQ₁.inter hS
  have hmass : μ.real Q₁ = μ.real Q₀ := by
    have he : Q₁ =ᵐ[μ] Q₀ := by
      filter_upwards [hnorm] with q hq
      apply propext
      change (q ∈ Q₀ ∧ η q (ball 0 r) = 1) ↔ q ∈ Q₀
      simp [hq]
    exact congrArg ENNReal.toReal (measure_congr he)
  have hsmall : μ.real Qᶜ < (1/100 : ℝ)^2 := by
    have hQ₁small : μ.real Q₁ᶜ < 1/20000 := by
      rw [measureReal_compl hQ₁,measureReal_univ_eq_one,hmass]
      linarith
    change μ.real (Q₁ ∩ S)ᶜ < _
    rw [compl_inter]
    have hu := measureReal_union_le (μ := μ) Q₁ᶜ Sᶜ
    linarith
  obtain ⟨G,hG,hGmass,hreturns⟩ := exists_uniform_paired_return_set hT hQ.compl hsmall
  refine ⟨δ,hδ,Q,G,hQ,inter_subset_right,hG,hGmass,?_⟩
  intro x hx y hy g hd hb hnc
  obtain ⟨s,t,hscales⟩ := exists_actual_shear_scales ha g hd hb hnc
  obtain ⟨k,hk,hxk,hyk,hxn,hyn⟩ := hreturns x hx y hy s t
  have hxQ : T^[k] x ∈ Q := by simpa only [mem_compl_iff,not_not] using hxk
  have hyQ : T^[k] y ∈ Q := by simpa only [mem_compl_iff,not_not] using hyk
  have hxQn : T^[shearTime s t k] x ∈ Q := by simpa only [mem_compl_iff,not_not] using hxn
  have hyQn : T^[shearTime s t k] y ∈ Q := by simpa only [mem_compl_iff,not_not] using hyn
  obtain ⟨_,hl,hq,hlq⟩ := hscales k hk
  refine ⟨s,t,k,hk,hxQ,hyQ,hxQn,hyQn,hl,hq,?_⟩
  intro D hD
  let L := linearCoefficient a g (extraTime s t k)
  let P := quadraticCoefficient a g k (extraTime s t k)
  have hbad := hbound (T^[k] x) hxQ.1.1 L P hl hq hlq.le
  have hnormx : η (T^[k] x) (ball 0 r) = 1 := hxQ.1.2
  apply Classical.byContradiction
  intro hnot
  have hnotle (v : F) (hvr : ‖v‖ < r) (hvD : v ∉ D) : ‖L*v+P*v^2‖ ≤ δ := by
    apply le_of_not_gt
    intro hh
    exact hnot ⟨v,hvr,hvD,hh⟩
  have hsub : ball (0 : F) r ⊆ D ∪ {v | ‖v‖ < r ∧ ‖L*v+P*v^2‖ ≤ δ} := by
    intro v hvball
    have hvr : ‖v‖ < r := by simpa only [mem_ball,dist_zero_right] using hvball
    by_cases hvD : v ∈ D
    · exact Or.inl hvD
    · exact Or.inr ⟨hvr,hnotle v hvr hvD⟩
  have hle : (1 : ℝ≥0∞) ≤ η (T^[k] x) D +
      η (T^[k] x) {v | ‖v‖ < r ∧ ‖L*v+P*v^2‖ ≤ δ} := by
    rw [← hnormx]
    exact (measure_mono hsub).trans (measure_union_le _ _)
  have hadd : η (T^[k] x) D + η (T^[k] x) {v | ‖v‖ < r ∧ ‖L*v+P*v^2‖ ≤ δ}
      < (1/2 : ℝ≥0∞)+(1/4 : ℝ≥0∞) :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top (by norm_num) hD) hD hbad
  have hnum : (1/2 : ℝ≥0∞)+(1/4 : ℝ≥0∞) < 1 := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mp
    norm_num [ENNReal.toReal_add,ENNReal.toReal_div]
  exact (not_lt_of_ge hle) (hadd.trans hnum)

/-- The version for the literal normalized leaf-coordinate change: the
small parameter is sampled from the leaf field at the total return time
`k + extraTime`. Positive diagonal time contracts the lower root, so this
is the base point corresponding to the large parameter at time `k`. -/
theorem exists_paired_shear_good_set_at_total_time (hT : MeasurePreserving T μ μ)
    (S : Set Z) (hS : MeasurableSet S) (hSsmall : μ.real Sᶜ < 1/20000)
    (η : Z → Measure F) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnorm : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hnoatom : ∀ᵐ q ∂μ, NoAtoms (η q))
    {a : F} (ha : ‖a‖ = 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Q G : Set Z,
      MeasurableSet Q ∧ Q ⊆ S ∧ MeasurableSet G ∧ (99 / 100 : ℝ) < μ.real G ∧
      ∀ x ∈ G, ∀ y ∈ G, ∀ g : SL(2,F),
        ‖g 0 0-g 1 1‖ ≤ 1 → ‖g 0 1‖ ≤ 1 →
        (¬∀ u : F, BBEKFiniteQuotients.lower u*g = g*BBEKFiniteQuotients.lower u) →
        ∃ s t k : ℕ, k < min s (t / 2) / 4+1 ∧
          T^[k] x ∈ Q ∧ T^[k] y ∈ Q ∧
          T^[shearTime s t k] x ∈ Q ∧ T^[shearTime s t k] y ∈ Q ∧
          ‖linearCoefficient a g (extraTime s t k)‖ ≤ 1 ∧
          ‖quadraticCoefficient a g k (extraTime s t k)‖ ≤ 1 ∧
          ∀ D : Set F, η (T^[shearTime s t k] x) D ≤ (1/2 : ℝ≥0∞) →
            ∃ v : F, ‖v‖ < r ∧ v ∉ D ∧
              δ < ‖linearCoefficient a g (extraTime s t k)*v +
                quadraticCoefficient a g k (extraTime s t k)*v^2‖ := by
  classical
  obtain ⟨δ,hδ,Q₀,hQ₀,hQmass,hbound⟩ :=
    exists_uniform_leaf_sublevel_good_set η hη hr hnorm hnoatom
      (by norm_num : (0 : ℝ) < 1/16) (by norm_num : (1/16 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 1/20000) (by norm_num : (0 : ℝ≥0∞) < 1/4)
  let N : Set Z := {q | η q (ball 0 r) = 1}
  have hN : MeasurableSet N :=
    (measurableSet_singleton (1 : ℝ≥0∞)).preimage
      ((Measure.measurable_coe measurableSet_ball).comp hη)
  let Q₁ := Q₀ ∩ N
  let Q := Q₁ ∩ S
  have hQ₁ : MeasurableSet Q₁ := hQ₀.inter hN
  have hQ : MeasurableSet Q := hQ₁.inter hS
  have hmass : μ.real Q₁ = μ.real Q₀ := by
    have he : Q₁ =ᵐ[μ] Q₀ := by
      filter_upwards [hnorm] with q hq
      apply propext
      change (q ∈ Q₀ ∧ η q (ball 0 r) = 1) ↔ q ∈ Q₀
      simp [hq]
    exact congrArg ENNReal.toReal (measure_congr he)
  have hsmall : μ.real Qᶜ < (1/100 : ℝ)^2 := by
    have hQ₁small : μ.real Q₁ᶜ < 1/20000 := by
      rw [measureReal_compl hQ₁,measureReal_univ_eq_one,hmass]
      linarith
    change μ.real (Q₁ ∩ S)ᶜ < _
    rw [compl_inter]
    have hu := measureReal_union_le (μ := μ) Q₁ᶜ Sᶜ
    linarith
  obtain ⟨G,hG,hGmass,hreturns⟩ := exists_uniform_paired_return_set hT hQ.compl hsmall
  refine ⟨δ,hδ,Q,G,hQ,inter_subset_right,hG,hGmass,?_⟩
  intro x hx y hy g hd hb hnc
  obtain ⟨s,t,hscales⟩ := exists_actual_shear_scales ha g hd hb hnc
  obtain ⟨k,hk,hxk,hyk,hxn,hyn⟩ := hreturns x hx y hy s t
  have hxQ : T^[k] x ∈ Q := by simpa only [mem_compl_iff,not_not] using hxk
  have hyQ : T^[k] y ∈ Q := by simpa only [mem_compl_iff,not_not] using hyk
  have hxQn : T^[shearTime s t k] x ∈ Q := by simpa only [mem_compl_iff,not_not] using hxn
  have hyQn : T^[shearTime s t k] y ∈ Q := by simpa only [mem_compl_iff,not_not] using hyn
  obtain ⟨_,hl,hq,hlq⟩ := hscales k hk
  refine ⟨s,t,k,hk,hxQ,hyQ,hxQn,hyQn,hl,hq,?_⟩
  intro D hD
  let L := linearCoefficient a g (extraTime s t k)
  let P := quadraticCoefficient a g k (extraTime s t k)
  have hbad := hbound (T^[shearTime s t k] x) hxQn.1.1 L P hl hq hlq.le
  have hnormx : η (T^[shearTime s t k] x) (ball 0 r) = 1 := hxQn.1.2
  apply Classical.byContradiction
  intro hnot
  have hnotle (v : F) (hvr : ‖v‖ < r) (hvD : v ∉ D) : ‖L*v+P*v^2‖ ≤ δ := by
    apply le_of_not_gt
    intro hh
    exact hnot ⟨v,hvr,hvD,hh⟩
  have hsub : ball (0 : F) r ⊆ D ∪ {v | ‖v‖ < r ∧ ‖L*v+P*v^2‖ ≤ δ} := by
    intro v hvball
    have hvr : ‖v‖ < r := by simpa only [mem_ball,dist_zero_right] using hvball
    by_cases hvD : v ∈ D
    · exact Or.inl hvD
    · exact Or.inr ⟨hvr,hnotle v hvr hvD⟩
  have hle : (1 : ℝ≥0∞) ≤ η (T^[shearTime s t k] x) D +
      η (T^[shearTime s t k] x) {v | ‖v‖ < r ∧ ‖L*v+P*v^2‖ ≤ δ} := by
    rw [← hnormx]
    exact (measure_mono hsub).trans (measure_union_le _ _)
  have hadd : η (T^[shearTime s t k] x) D + η (T^[shearTime s t k] x) {v | ‖v‖ < r ∧ ‖L*v+P*v^2‖ ≤ δ}
      < (1/2 : ℝ≥0∞)+(1/4 : ℝ≥0∞) :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top (by norm_num) hD) hD hbad
  have hnum : (1/2 : ℝ≥0∞)+(1/4 : ℝ≥0∞) < 1 := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mp
    norm_num [ENNReal.toReal_add,ENNReal.toReal_div]
  exact (not_lt_of_ge hle) (hadd.trans hnum)


end VV.BBEKPairedShear





