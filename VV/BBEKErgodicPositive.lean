import VV.BBEKPositiveDiagonal
import VV.Entropy.EntropyExtreme

/-! Selection of an actual full-parameter ergodic positive-entropy measure
inside the compact cone-trapped model. -/

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology

namespace VV.BBEKErgodicPositive
open BBEKDynamics BBEKQuotient BBEKTopology BBEKReduction P7BoxCover
open BBEKEntropyNets BBEKEntropyTrapped BBEKEntropyExpansion BBEKDiagonalAverage
open BBEKConeAverage BBEKConeEntropy BBEKEntropySemicontinuity BBEKConeGenerators
open BBEKEntropySeed BBEKFiniteBowen
open ErgodicTheory.Entropy

theorem generator_two_eq_time (δ : ℝ) :
    generatorMap δ 2 = restrictedTimeMap (trappedTimeForward δ) := by
  funext q
  apply Subtype.ext
  rfl

/-- A nonzero box-dimensional obstruction gives a literal probability on X
which is invariant and ergodic for the full real/integer parameter group,
is supported on Kδ, and has positive KS entropy at the designated time. -/
theorem exists_trapped_psi_ergodic_pos_ksEntropy {δ : ℝ} (hδ : 0 < δ)
    (hbox : ¬ GeometricZeroUpperBox (trappedParameters δ)) :
    ∃ μ : ProbabilityMeasure (trappedQuotient δ),
      ∃ hμT : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
        (μ : Measure _) (μ : Measure _),
      0 < ksEntropy hμT ∧
      ∃ hH : SMulInvariantMeasure H X (toQuotient δ μ : Measure X),
        ErgodicSMul H X (toQuotient δ μ : Measure X) ∧
        (toQuotient δ μ : Measure X) (BBEKOrbit.K δ) = 1 := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace (trappedQuotient δ) :=
    isCompact_iff_compactSpace.mp (compact_trappedQuotient hδ)
  obtain ⟨ν,hν,hpos,havg⟩ := exists_pos_ksEntropy_coneAverages hδ hbox
  obtain ⟨c,hc,hcν⟩ := EReal.exists_between_coe_real hpos
  obtain ⟨μ,φ,hφ,hlim,h0,h1,h2⟩ := exists_invariant_tripleAverage_subseq
    (continuous_generatorMap δ 0) (continuous_generatorMap δ 1) (continuous_generatorMap δ 2)
    (generatorMap_commute δ 0 1) (generatorMap_commute δ 0 2) (generatorMap_commute δ 1 2)
    (fun j : ℕ => j+1) (fun j => Nat.succ_pos j) (tendsto_add_atTop_nat 1) (fun _ => ν)
  have hlength : Tendsto (fun j => φ j + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  have htime : 0 < time0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans time0_gt_log_two
  have hμT : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (μ : Measure (trappedQuotient δ)) (μ : Measure (trappedQuotient δ)) := by
    rw [← generator_two_eq_time]
    exact h2
  have hbound : (c : EReal) ≤ ksEntropy hμT :=
    compact_entropy_lower_bound_limit (compact_trappedQuotient hδ) htime
      (trappedTimeForward δ) hlim hμT
      (fun j => coneAverage_timeInvariant δ (φ j+1) (by omega) ν hν)
      (Filter.Eventually.of_forall (fun j => by rw [havg]; exact hcν.le))
  obtain ⟨r,hr,hcoverTime⟩ := compact_uniformBowenCover
    (compact_trappedQuotient hδ) htime (trappedTimeForward δ)
  have hcover : UniformBowenCover (generatorMap δ 2) r := by
    rw [generator_two_eq_time]
    exact hcoverTime
  have hμinv : μ ∈ invariantProbabilities (generatorMap δ) := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  obtain ⟨μe,hμe,hge,hjoint⟩ := exists_jointlyErgodic_entropy_ge
    (generatorMap δ) (continuous_generatorMap δ) 2 hr hcover μ hμinv
  have hμeT : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (μe : Measure (trappedQuotient δ)) (μe : Measure (trappedQuotient δ)) := by
    rw [← generator_two_eq_time]
    exact hμe 2
  have hposE : 0 < ksEntropy hμeT := by
    apply hc.trans_le
    apply hbound.trans
    simpa only [generator_two_eq_time] using hge
  let μX := toQuotient δ μe
  have hgen (i : Fin 3) :
      MeasurePreserving (fun q : X => psi (generator i).1 (generator i).2 • q)
        (μX : Measure X) (μX : Measure X) :=
    toQuotient_generator_invariant δ μe i (hμe i)
  have hH : SMulInvariantMeasure H X (μX : Measure X) :=
    psi_invariant_of_generators (μX : Measure X) hgen
  have hemb : MeasurableEmbedding (Subtype.val : trappedQuotient δ → X) :=
    MeasurableEmbedding.subtype_coe (compact_trappedQuotient hδ).isClosed.measurableSet
  have hErg : ErgodicSMul H X (μX : Measure X) := by
    letI : SMulInvariantMeasure H X (μX : Measure X) := hH
    constructor
    intro s hs hinv
    have hinvY : ∀ i : Fin 3,
        (generatorMap δ i) ⁻¹' (Subtype.val ⁻¹' s) =ᵐ[(μe : Measure _)]
          (Subtype.val ⁻¹' s) := by
      intro i
      have hh := hinv (Multiplicative.ofAdd (generator i))
      change (fun x : X => x ∈ (fun q : X => psi (generator i).1 (generator i).2 • q) ⁻¹' s) =ᵐ[
        Measure.map (Subtype.val : trappedQuotient δ → X) (μe : Measure _)]
          (fun x : X => x ∈ s) at hh
      have hp := hemb.ae_map_iff.mp hh
      simpa only [mem_preimage,generatorMap] using hp
    have hconst := hjoint (Subtype.val ⁻¹' s) (hs.preimage measurable_subtype_coe) hinvY
    rw [eventuallyConst_set] at hconst ⊢
    rcases hconst with hmem | hnmem
    · left
      change ∀ᵐ x ∂Measure.map (Subtype.val : trappedQuotient δ → X) (μe : Measure _), x ∈ s
      exact hemb.ae_map_iff.mpr hmem
    · right
      change ∀ᵐ x ∂Measure.map (Subtype.val : trappedQuotient δ → X) (μe : Measure _), x ∉ s
      exact hemb.ae_map_iff.mpr hnmem
  exact ⟨μe,hμeT,hposE,hH,hErg,toQuotient_K_mass δ μe⟩

theorem exists_psi_ergodic_pos_ksEntropy_supported_K {δ : ℝ} (hδ : 0 < δ)
    (hbox : ¬ GeometricZeroUpperBox (trappedParameters δ)) :
    ∃ μ : ProbabilityMeasure X,
      ∃ hH : SMulInvariantMeasure H X (μ : Measure X),
      ErgodicSMul H X (μ : Measure X) ∧
      (μ : Measure X) (BBEKOrbit.K δ) = 1 ∧
      ∃ hμT : MeasurePreserving (timeMap time0) (μ : Measure X) (μ : Measure X),
        0 < ksEntropy hμT := by
  obtain ⟨μ,hμT,hpos,hH,hErg,hK⟩ :=
    exists_trapped_psi_ergodic_pos_ksEntropy hδ hbox
  obtain ⟨hXT,hXE⟩ := toQuotient_entropy δ μ hμT
  exact ⟨toQuotient δ μ,hH,hErg,hK,hXT,hXE.symm ▸ hpos⟩

end VV.BBEKErgodicPositive
