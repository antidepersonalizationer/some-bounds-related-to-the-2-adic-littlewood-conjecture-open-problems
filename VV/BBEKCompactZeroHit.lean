import VV.BBEKGlobalLowerCovariance

/-! A countable family of continuous tests has a zero on a compact set iff
all finite blocks admit arbitrarily good points from a fixed dense sequence.
This proves measurable compact hitting for Carathéodory test families without
using a measurable-projection axiom or a compact-hit hypothesis. -/
noncomputable section
open Set Filter Topology
open scoped Topology
namespace VV.BBEKCompactZeroHit

variable {U Z : Type*} [TopologicalSpace U]

private theorem tolerance_antitone : Antitone (fun n : ℕ => (1 : ℝ)/(n+1)) := by
  intro n m hnm
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 1

theorem exists_zero_iff_dense_approx [CompactSpace U]
    (f : ℕ → U → ℝ) (hf : ∀ j, Continuous (f j))
    (d : ℕ → U) (hd : DenseRange d) :
    (∃ u : U, ∀ j : ℕ, f j u = 0) ↔
      ∀ n : ℕ, ∃ k : ℕ, ∀ j ≤ n, |f j (d k)| < 1/(n+1 : ℝ) := by
  constructor
  · rintro ⟨u,hu⟩ n
    let O := {v : U | ∀ j ∈ Finset.range (n+1), |f j v| < 1/(n+1 : ℝ)}
    have hO : IsOpen O := by
      dsimp only [O]
      simp only [setOf_forall]
      exact isOpen_biInter_finset (fun j _ => isOpen_lt (hf j).abs continuous_const)
    have huO : u ∈ O := by
      intro j _
      rw [hu j,abs_zero]
      positivity
    obtain ⟨k,hk⟩ := hd.exists_mem_open hO ⟨u,huO⟩
    exact ⟨k,fun j hj => hk j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))⟩
  · intro happ
    let S : ℕ → Set U := fun n => {u | ∀ j ≤ n, |f j u| ≤ 1/(n+1 : ℝ)}
    have hclosed (n : ℕ) : IsClosed (S n) := by
      dsimp only [S]
      simp only [setOf_forall]
      exact isClosed_iInter (fun j => isClosed_iInter (fun _ => isClosed_le (hf j).abs continuous_const))
    have hne (n : ℕ) : (S n).Nonempty := by
      obtain ⟨k,hk⟩ := happ n
      exact ⟨d k,fun j hj => (hk j hj).le⟩
    have hdec (n : ℕ) : S (n+1) ⊆ S n := by
      intro u hu j hj
      exact (hu j (hj.trans (Nat.le_succ n))).trans (tolerance_antitone (Nat.le_succ n))
    obtain ⟨u,hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hdec hne (hclosed 0).isCompact hclosed
    refine ⟨u,fun j => ?_⟩
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
    have hbound := mem_iInter.mp hu (max n j) j (le_max_right n j)
    have hb : |f j u| ≤ 1/(n+1 : ℝ) :=
      hbound.trans (tolerance_antitone (le_max_left n j))
    simpa only [zero_add] using hb.trans hn.le

/-- The zero-hit event for countably many Carathéodory tests on a compact
second-countable space is Borel in the parameter. -/
theorem measurableSet_exists_zero [MeasurableSpace Z]
    [CompactSpace U] [SecondCountableTopology U]
    (f : ℕ → Z → U → ℝ)
    (hm : ∀ j u, Measurable (fun z => f j z u))
    (hc : ∀ j z, Continuous (f j z)) :
    MeasurableSet {z : Z | ∃ u : U, ∀ j : ℕ, f j z u = 0} := by
  classical
  by_cases hu : Nonempty U
  · letI := hu
    let d : ℕ → U := TopologicalSpace.denseSeq U
    have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq U
    have he : {z : Z | ∃ u : U, ∀ j : ℕ, f j z u = 0} =
        ⋂ n : ℕ, ⋃ k : ℕ, ⋂ j : ℕ, ⋂ _ : j ≤ n,
          {z : Z | |f j z (d k)| < 1/(n+1 : ℝ)} := by
      ext z
      simp only [mem_setOf_eq,mem_iInter,mem_iUnion]
      exact exists_zero_iff_dense_approx (fun j => f j z) (fun j => hc j z) d hd
    rw [he]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun k =>
      MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
        measurableSet_lt (continuous_abs.measurable.comp (hm j (d k))) measurable_const))))
  · letI : IsEmpty U := not_nonempty_iff.mp hu
    have he : {z : Z | ∃ u : U, ∀ j : ℕ, f j z u = 0} = ∅ := by
      ext z
      constructor
      · rintro ⟨u,_⟩; exact isEmptyElim u
      · intro h; exact h.elim
    rw [he]
    exact MeasurableSet.empty

/-- Compact subsets require no separate measurable-selection hypothesis. -/
theorem measurableSet_exists_zero_on_compact [MeasurableSpace Z]
    [SecondCountableTopology U] {C : Set U} (hC : IsCompact C)
    (f : ℕ → Z → U → ℝ)
    (hm : ∀ j u, Measurable (fun z => f j z u))
    (hc : ∀ j z, Continuous (f j z)) :
    MeasurableSet {z : Z | ∃ u ∈ C, ∀ j : ℕ, f j z u = 0} := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hh := measurableSet_exists_zero (fun j z (u : C) => f j z u)
    (fun j u => hm j u) (fun j z => (hc j z).comp continuous_subtype_val)
  convert hh using 1
  ext z
  constructor
  · rintro ⟨u,hu,hf⟩; exact ⟨⟨u,hu⟩,hf⟩
  · rintro ⟨⟨u,hu⟩,hf⟩; exact ⟨u,hu,hf⟩

/-- Countable compact exhaustion gives the corresponding event on any
sigma-compact second-countable space. -/
theorem measurableSet_exists_zero_of_sigmaCompact [MeasurableSpace Z]
    [SecondCountableTopology U] [SigmaCompactSpace U]
    (f : ℕ → Z → U → ℝ)
    (hm : ∀ j u, Measurable (fun z => f j z u))
    (hc : ∀ j z, Continuous (f j z)) :
    MeasurableSet {z : Z | ∃ u : U, ∀ j : ℕ, f j z u = 0} := by
  have he : {z : Z | ∃ u : U, ∀ j : ℕ, f j z u = 0} =
      ⋃ n : ℕ, {z : Z | ∃ u ∈ compactCovering U n, ∀ j : ℕ, f j z u = 0} := by
    ext z
    simp only [mem_setOf_eq,mem_iUnion]
    constructor
    · rintro ⟨u,hu⟩
      obtain ⟨n,hn⟩ := exists_mem_compactCovering u
      exact ⟨n,u,hn,hu⟩
    · rintro ⟨n,u,_,hu⟩
      exact ⟨u,hu⟩
  rw [he]
  exact MeasurableSet.iUnion (fun n => measurableSet_exists_zero_on_compact
    (isCompact_compactCovering U n) f hm hc)

/-- In particular the hit-open event used for stabilizer fields is measurable
when membership is characterized by a countable family of continuous tests. -/
theorem measurableSet_exists_zero_on_open [MeasurableSpace Z]
    [SecondCountableTopology U] [LocallyCompactSpace U] {O : Set U} (hO : IsOpen O)
    (f : ℕ → Z → U → ℝ)
    (hm : ∀ j u, Measurable (fun z => f j z u))
    (hc : ∀ j z, Continuous (f j z)) :
    MeasurableSet {z : Z | ∃ u ∈ O, ∀ j : ℕ, f j z u = 0} := by
  letI : LocallyCompactSpace O := hO.locallyCompactSpace
  have hh := measurableSet_exists_zero_of_sigmaCompact (fun j z (u : O) => f j z u)
    (fun j u => hm j u) (fun j z => (hc j z).comp continuous_subtype_val)
  convert hh using 1
  ext z
  constructor
  · rintro ⟨u,hu,hf⟩; exact ⟨⟨u,hu⟩,hf⟩
  · rintro ⟨⟨u,hu⟩,hf⟩; exact ⟨u,hu,hf⟩

end VV.BBEKCompactZeroHit

