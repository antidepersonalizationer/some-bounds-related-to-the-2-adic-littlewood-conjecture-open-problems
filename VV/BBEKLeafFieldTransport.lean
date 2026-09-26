import VV.BBEKOneRootTranslation
import VV.BBEKCanonicalCovariance

/-! Equality of the actual normalized leaf field is preserved by diagonal
iteration and by equal root translations on the strong covariance set. -/
noncomputable section
open Set MeasureTheory Filter Function Metric
open scoped Topology ENNReal
namespace VV.BBEKLeafFieldTransport

section Iteration
variable {Z Y : Type*} [MeasurableSpace Z] {μ : Measure Z} {T : Z → Z}

/-- An almost-everywhere covariance identity gives a single measurable,
forward-invariant conull set on which every iterate preserves equality of
the literal field. The field transformation is fixed, not point-dependent. -/
theorem exists_invariant_conull_equal_field
    (hT : MeasurePreserving T μ μ) (f : Z → Y) (Φ : Y → Y)
    (hcov : ∀ᵐ q ∂μ, f (T q) = Φ (f q)) :
    ∃ C : Set Z, MeasurableSet C ∧ (∀ᵐ q ∂μ, q ∈ C) ∧ MapsTo T C C ∧
      (∀ q ∈ C, f (T q) = Φ (f q)) ∧
      ∀ x ∈ C, ∀ y ∈ C, f x = f y → ∀ n : ℕ, f (T^[n] x) = f (T^[n] y) := by
  obtain ⟨N,hN,hNm,hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hcov)
  let C₀ := Nᶜ
  have hC₀ : MeasurableSet C₀ := hNm.compl
  have hC₀ae : ∀ᵐ q ∂μ, q ∈ C₀ := by
    apply ae_iff.mpr
    simpa only [C₀,mem_compl_iff,not_not] using hNzero
  have hC₀cov (q : Z) (hq : q ∈ C₀) : f (T q) = Φ (f q) := by
    by_contra hn
    exact hq (hN hn)
  let C := ⋂ n : ℕ, (T^[n]) ⁻¹' C₀
  have hC : MeasurableSet C := MeasurableSet.iInter fun n => hC₀.preimage (hT.measurable.iterate n)
  have hCae : ∀ᵐ q ∂μ, q ∈ C := by
    have hall : ∀ᵐ q ∂μ, ∀ n : ℕ, T^[n] q ∈ C₀ := ae_all_iff.mpr
      (fun n => (hT.iterate n).quasiMeasurePreserving.ae hC₀ae)
    simpa only [C,mem_iInter,mem_preimage] using hall
  have hCmem (q : Z) (hq : q ∈ C) (n : ℕ) : T^[n] q ∈ C₀ := mem_iInter.mp hq n
  have hmaps : MapsTo T C C := by
    intro q hq
    apply mem_iInter.mpr
    intro n
    change T^[n] (T q) ∈ C₀
    simpa only [Function.iterate_succ_apply] using hCmem q hq (n+1)
  refine ⟨C,hC,hCae,hmaps,?_,?_⟩
  · intro q hq
    exact hC₀cov q (by simpa using hCmem q hq 0)
  · intro x hx y hy he n
    induction n with
    | zero => simpa using he
    | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply',
        hC₀cov _ (hCmem x hx n),hC₀cov _ (hCmem y hy n),ih]
end Iteration

section Translation
variable {U Z : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]
open BBEKLeafwiseStabilizer

/-- Strong same-leaf covariance transports equality for an arbitrary common
translation parameter, provided all four actual points lie in its one fixed
covariance set. This is stronger than an almost-everywhere-in-parameter claim. -/
theorem equal_field_of_common_translation
    (root : U → Z → Z) (η : Z → Measure U) {S : Set Z} (r : ℝ)
    (hcov : ∀ q ∈ S, ∀ u : U, root u q ∈ S →
      η (root u q) = ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q))
    {x y : Z} (hx : x ∈ S) (hy : y ∈ S) (he : η x = η y)
    (u : U) (hux : root u x ∈ S) (huy : root u y ∈ S) :
    η (root u x) = η (root u y) := by
  rw [hcov x hx u hux,hcov y hy u huy,he]
end Translation



section ActualLower
open BBEKDynamics BBEKQuotient BBEKRootLeafKernel BBEKOneRootCovariance
open BBEKCanonicalCovariance
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The real lower statement uses the covariance theorem of this very
canonical field, not a separately chosen family. -/
theorem real_lower_equal_field_iterates
    (μ : Measure X) [IsFiniteMeasure μ] {t r : ℝ} (ht : Real.log 2 ≤ t) (hr : 0 < r)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ)
    (η : X → Measure ℝ) (hn : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hc : IsConstructedRootFamily realSplit μ t r η) :
    ∃ C : Set X, MeasurableSet C ∧ (∀ᵐ q ∂μ, q ∈ C) ∧
      MapsTo (fun q : X => psi t 1 • q) C C ∧
      ∀ x ∈ C, ∀ y ∈ C, η x = η y → ∀ n : ℕ,
        η ((fun q : X => psi t 1 • q)^[n] x) = η ((fun q : X => psi t 1 • q)^[n] y) := by
  have hcov := canonical_real_lower_covariance μ ht hr hA η hn hc
  obtain ⟨C,hC,hCae,hmap,_,he⟩ := exists_invariant_conull_equal_field hA η
    (fun ν : Measure ℝ => (ν.map (BBEKRootLeafKernel.realLeafScaling t) (ball 0 r))⁻¹ •
      ν.map (BBEKRootLeafKernel.realLeafScaling t)) (hcov.mono fun _ h => h.1)
  exact ⟨C,hC,hCae,hmap,he⟩

/-- The 2-adic lower statement has the same actual radius-r normalization. -/
theorem padic_lower_equal_field_iterates
    (μ : Measure X) [IsFiniteMeasure μ] {t r : ℝ} (hr : 0 < r)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ)
    (η : X → Measure Q2) (hn : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hc : IsConstructedRootFamily padicSplit μ t r η) :
    ∃ C : Set X, MeasurableSet C ∧ (∀ᵐ q ∂μ, q ∈ C) ∧
      MapsTo (fun q : X => psi t 1 • q) C C ∧
      ∀ x ∈ C, ∀ y ∈ C, η x = η y → ∀ n : ℕ,
        η ((fun q : X => psi t 1 • q)^[n] x) = η ((fun q : X => psi t 1 • q)^[n] y) := by
  have hcov := canonical_padic_lower_covariance μ hr hA η hn hc
  obtain ⟨C,hC,hCae,hmap,_,he⟩ := exists_invariant_conull_equal_field hA η
    (fun ν : Measure Q2 => (ν.map (BBEKRootLeafKernel.padicLeafScaling 1) (ball 0 r))⁻¹ •
      ν.map (BBEKRootLeafKernel.padicLeafScaling 1)) (hcov.mono fun _ h => h.1)
  exact ⟨C,hC,hCae,hmap,he⟩
end ActualLower

end VV.BBEKLeafFieldTransport

