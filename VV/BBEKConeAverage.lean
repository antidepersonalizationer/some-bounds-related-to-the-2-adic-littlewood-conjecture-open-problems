import VV.BBEKConeGenerators
import VV.BBEKEntropyTrapped
import VV.Entropy.CommutingAverage

/-! Actual finite cone averages on the compact trapped quotient set. -/

noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology

namespace VV.BBEKConeAverage
open BBEKDynamics BBEKQuotient BBEKTopology BBEKConeGenerators
open BBEKEntropyTrapped BBEKDiagonalAverage ErgodicTheory.Entropy

def generatorMap (δ : ℝ) (i : Fin 3) : trappedQuotient δ → trappedQuotient δ :=
  fun q => ⟨psi (generator i).1 (generator i).2 • q.val,
    trappedQuotient_forward (generator_mem_cone i) q.property⟩

theorem continuous_generatorMap (δ : ℝ) (i : Fin 3) : Continuous (generatorMap δ i) :=
  (continuous_const.smul continuous_subtype_val).subtype_mk _

theorem generatorMap_commute (δ : ℝ) (i j : Fin 3) :
    Function.Commute (generatorMap δ i) (generatorMap δ j) := by
  intro q
  apply Subtype.ext
  change psi (generator i).1 (generator i).2 • (psi (generator j).1 (generator j).2 • q.val) =
    psi (generator j).1 (generator j).2 • (psi (generator i).1 (generator i).2 • q.val)
  rw [← mul_smul,← mul_smul,← psi_add,← psi_add]
  simp only [add_comm]

def coneAverage (δ : ℝ) (n : ℕ) (hn : 0 < n)
    (ν : ProbabilityMeasure (trappedQuotient δ)) : ProbabilityMeasure (trappedQuotient δ) :=
  tripleAverage (continuous_generatorMap δ 0).measurable
    (continuous_generatorMap δ 1).measurable (continuous_generatorMap δ 2).measurable n hn ν

def toQuotient (δ : ℝ) (μ : ProbabilityMeasure (trappedQuotient δ)) : ProbabilityMeasure X :=
  μ.map measurable_subtype_coe.aemeasurable

theorem toQuotient_K_mass (δ : ℝ) (μ : ProbabilityMeasure (trappedQuotient δ)) :
    (toQuotient δ μ : Measure X) (BBEKOrbit.K δ) = 1 := by
  change (Measure.map Subtype.val (μ:Measure (trappedQuotient δ))) (BBEKOrbit.K δ) = 1
  rw [Measure.map_apply measurable_subtype_coe (BBEKOrbit.isClosed_K δ).measurableSet]
  have he : (Subtype.val : trappedQuotient δ → X) ⁻¹' BBEKOrbit.K δ = univ := by
    ext q
    simp only [mem_preimage,mem_univ,iff_true]
    exact trappedQuotient_subset_K δ q.property
  rw [he,measure_univ]

theorem toQuotient_generator_invariant (δ : ℝ) (μ : ProbabilityMeasure (trappedQuotient δ))
    (i : Fin 3) (hi : MeasurePreserving (generatorMap δ i) (μ:Measure _) (μ:Measure _)) :
    MeasurePreserving (fun q : X => psi (generator i).1 (generator i).2 • q)
      (toQuotient δ μ : Measure X) (toQuotient δ μ : Measure X) := by
  have hg : Measurable (fun q : X => psi (generator i).1 (generator i).2 • q) :=
    (continuous_const.smul continuous_id).measurable
  refine ⟨hg,?_⟩
  change Measure.map _ (Measure.map Subtype.val (μ:Measure (trappedQuotient δ))) =
    Measure.map Subtype.val (μ:Measure (trappedQuotient δ))
  rw [Measure.map_map hg measurable_subtype_coe]
  change Measure.map (Subtype.val ∘ generatorMap δ i) (μ:Measure (trappedQuotient δ)) = _
  rw [← Measure.map_map measurable_subtype_coe hi.measurable,hi.map_eq]

theorem exists_psi_invariant_coneAverage_subseq {δ : ℝ} (hδ : 0 < δ)
    (ν : ℕ → ProbabilityMeasure (trappedQuotient δ)) :
    ∃ μ : ProbabilityMeasure (trappedQuotient δ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => coneAverage δ (φ j+1) (by omega) (ν (φ j))) atTop (𝓝 μ) ∧
      SMulInvariantMeasure H X (toQuotient δ μ : Measure X) ∧
      (toQuotient δ μ : Measure X) (BBEKOrbit.K δ) = 1 := by
  letI : CompactSpace (trappedQuotient δ) :=
    isCompact_iff_compactSpace.mp (compact_trappedQuotient hδ)
  obtain ⟨μ,φ,hφ,hlim,h0,h1,h2⟩ := exists_invariant_tripleAverage_subseq
    (continuous_generatorMap δ 0) (continuous_generatorMap δ 1) (continuous_generatorMap δ 2)
    (generatorMap_commute δ 0 1) (generatorMap_commute δ 0 2) (generatorMap_commute δ 1 2)
    (fun j : ℕ => j+1) (fun j => Nat.succ_pos j) (tendsto_add_atTop_nat 1) ν
  refine ⟨μ,φ,hφ,hlim,?_,toQuotient_K_mass δ μ⟩
  apply psi_invariant_of_generators
  intro i
  apply toQuotient_generator_invariant
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end VV.BBEKConeAverage
