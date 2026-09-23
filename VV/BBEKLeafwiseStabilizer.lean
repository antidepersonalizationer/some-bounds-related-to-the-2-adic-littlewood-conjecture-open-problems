import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic

/-! Translation stabilizers of actual (possibly infinite) leaf measures.
The stabilizer is constructed from equality of pushforward measures; its
subgroup laws, closedness, and covariance are proved. -/

noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology ENNReal NNReal

namespace VV.BBEKLeafwiseStabilizer

variable {U : Type*} [AddCommGroup U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]

def translate (u : U) (η : Measure U) : Measure U := Measure.map (u + ·) η

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [BorelSpace U] [SecondCountableTopology U] in
@[simp] theorem translate_zero (η : Measure U) : translate 0 η = η := by
  simp [translate]

theorem translate_add (u v : U) (η : Measure U) :
    translate (u+v) η = translate u (translate v η) := by
  simp only [translate]
  rw [Measure.map_map (show Measurable (fun x : U => u+x) from measurable_const.add measurable_id)
    (show Measurable (fun x : U => v+x) from measurable_const.add measurable_id)]
  congr 1
  funext x
  exact add_assoc u v x

/-- The exact translation stabilizer, without postulating any subgroup. -/
def translationStabilizer (η : Measure U) : AddSubgroup U where
  carrier := {u | translate u η = η}
  zero_mem' := translate_zero η
  add_mem' := by
    intro u v hu hv
    change translate (u+v) η = η
    rw [translate_add,hv,hu]
  neg_mem' := by
    intro u hu
    have h := congrArg (translate (-u)) hu
    rw [← translate_add,neg_add_cancel,translate_zero] at h
    exact h.symm

@[simp] theorem mem_translationStabilizer (η : Measure U) (u : U) :
    u ∈ translationStabilizer η ↔ translate u η = η := Iff.rfl

theorem translate_apply (u : U) (η : Measure U) {s : Set U} (hs : MeasurableSet s) :
    translate u η s = η ((u + ·) ⁻¹' s) :=
  Measure.map_apply (measurable_const.add measurable_id) hs

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [BorelSpace U] [SecondCountableTopology U] in
theorem translate_smul (u : U) (η : Measure U) (c : ℝ≥0) :
    translate u (c • η) = c • translate u η := Measure.map_smul c η _

/-- Normalizing a nonzero leaf measure does not change its exact stabilizer. -/
theorem translationStabilizer_smul (η : Measure U) {c : ℝ≥0} (hc : c ≠ 0) :
    translationStabilizer (c • η) = translationStabilizer η := by
  ext u
  change translate u (c • η) = c • η ↔ translate u η = η
  rw [translate_smul]
  constructor
  · intro h
    simpa only [inv_smul_smul₀ hc] using congrArg (fun m : Measure U => c⁻¹ • m) h
  · exact congrArg (fun m : Measure U => c • m)

theorem translate_nsmul_of_eigen (η : Measure U) {u : U} {c : ℝ≥0}
    (h : translate u η = c • η) (n : ℕ) :
    translate (n • u) η = c^n • η := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul,translate_add,h,translate_smul,ih,smul_smul,pow_succ]
    rw [mul_comm]

theorem translate_neg_of_eigen (η : Measure U) {u : U} {c : ℝ≥0} (hc : c ≠ 0)
    (h : translate u η = c • η) : translate (-u) η = c⁻¹ • η := by
  have he := congrArg (translate (-u)) h
  rw [← translate_add,neg_add_cancel,translate_zero,translate_smul] at he
  have hh := congrArg (fun m : Measure U => c⁻¹ • m) he
  simpa only [inv_smul_smul₀ hc] using hh.symm

/-- The projective stabilizer is also constructed, rather than assumed. -/
def projectiveTranslationStabilizer (η : Measure U) : AddSubgroup U where
  carrier := {u | ∃ c : ℝ≥0, c ≠ 0 ∧ translate u η = c • η}
  zero_mem' := ⟨1,one_ne_zero,by simp⟩
  add_mem' := by
    rintro u v ⟨c,hc,hu⟩ ⟨d,hd,hv⟩
    refine ⟨d*c,mul_ne_zero hd hc,?_⟩
    rw [translate_add,hv,translate_smul,hu,smul_smul]
  neg_mem' := by
    rintro u ⟨c,hc,hu⟩
    exact ⟨c⁻¹,inv_ne_zero hc,translate_neg_of_eigen η hc hu⟩

theorem translationStabilizer_le_projective (η : Measure U) :
    translationStabilizer η ≤ projectiveTranslationStabilizer η := by
  intro u hu
  exact ⟨1,one_ne_zero,by simpa using hu⟩

/-- An elementary Fatou inequality for a sequence of translated open sets.
It works for infinite measures and does not use weak probability convergence. -/
theorem translated_open_le_of_tendsto (η : Measure U) {u : ℕ → U} {v : U}
    (hu : Tendsto u atTop (𝓝 v)) (hs : ∀ n, u n ∈ translationStabilizer η)
    {O : Set U} (hO : IsOpen O) : η ((v + ·) ⁻¹' O) ≤ η O := by
  let S (N : ℕ) : Set U := ⋂ n ≥ N, (u n + ·) ⁻¹' O
  have hmono : Monotone S := by
    intro N M hNM x hx
    simp only [S,mem_iInter,mem_preimage] at hx ⊢
    exact fun n hn => hx n (hNM.trans hn)
  have hsub : (v + ·) ⁻¹' O ⊆ ⋃ N, S N := by
    intro x hx
    have he : ∀ᶠ n in atTop, u n + x ∈ O :=
      (hu.add_const x).eventually (hO.mem_nhds hx)
    obtain ⟨N,hN⟩ := eventually_atTop.mp he
    exact mem_iUnion.mpr ⟨N,mem_iInter.mpr fun n => mem_iInter.mpr (hN n)⟩
  calc
    η ((v + ·) ⁻¹' O) ≤ η (⋃ N, S N) := measure_mono hsub
    _ = ⨆ N, η (S N) := hmono.measure_iUnion
    _ ≤ η O := iSup_le fun N => by
      have hSN : S N ⊆ (u N + ·) ⁻¹' O :=
        fun x hx => mem_iInter.mp (mem_iInter.mp hx N) le_rfl
      calc
        η (S N) ≤ η ((u N + ·) ⁻¹' O) := measure_mono hSN
        _ = translate (u N) η O := (translate_apply _ _ hO.measurableSet).symm
        _ = η O := congrArg (fun m : Measure U => m O) (hs N)

theorem translate_le_of_tendsto (η : Measure U) [η.OuterRegular]
    {u : ℕ → U} {v : U} (hu : Tendsto u atTop (𝓝 v))
    (hs : ∀ n, u n ∈ translationStabilizer η) : translate v η ≤ η := by
  apply Measure.le_iff.mpr
  intro s hsmeas
  rw [translate_apply _ _ hsmeas, s.measure_eq_iInf_isOpen η]
  apply le_iInf
  intro O
  apply le_iInf
  intro hsO
  apply le_iInf
  intro hO
  exact (measure_mono (preimage_mono hsO)).trans (translated_open_le_of_tendsto η hu hs hO)

/-- The translation stabilizer of an outer regular measure is closed.
In particular this applies to locally finite Radon measures on R and Q₂. -/
theorem isClosed_translationStabilizer [FirstCountableTopology U]
    (η : Measure U) [η.OuterRegular] : IsClosed (translationStabilizer η : Set U) := by
  apply IsSeqClosed.isClosed
  intro u v hs hu
  have h₁ := translate_le_of_tendsto η hu hs
  have h₂ := translate_le_of_tendsto η hu.neg
    (fun n => (translationStabilizer η).neg_mem (hs n))
  apply le_antisymm h₁
  have h := Measure.map_mono h₂ (measurable_const.add measurable_id : Measurable (v + ·))
  change translate v (translate (-v) η) ≤ translate v η at h
  simpa only [← translate_add,add_neg_cancel,translate_zero] using h

section Covariance
variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Translation commutes with an additive coordinate change exactly as it
should for a diagonal conjugation of a one-dimensional root group. -/
theorem translate_map_addEquiv (σ : U ≃+ V) (hσ : Measurable σ)
    (η : Measure U) (u : U) :
    translate (σ u) (Measure.map σ η) = Measure.map σ (translate u η) := by
  simp only [translate]
  rw [Measure.map_map (show Measurable (fun x : V => σ u+x) from measurable_const.add measurable_id) hσ,
    Measure.map_map hσ (show Measurable (fun x : U => u+x) from measurable_const.add measurable_id)]
  congr 1
  funext x
  exact (σ.map_add u x).symm

theorem mem_translationStabilizer_map_iff (σ : U ≃+ V)
    (hσ : Measurable σ) (hi : Measurable σ.symm) (η : Measure U) (u : U) :
    σ u ∈ translationStabilizer (Measure.map σ η) ↔ u ∈ translationStabilizer η := by
  change translate (σ u) (Measure.map σ η) = Measure.map σ η ↔ translate u η = η
  rw [translate_map_addEquiv σ hσ]
  constructor
  · intro h
    have hh := congrArg (Measure.map σ.symm) h
    simpa only [Measure.map_map hi hσ, σ.symm_comp_self, Measure.map_id] using hh
  · exact congrArg (Measure.map σ)

theorem translationStabilizer_map (σ : U ≃+ V)
    (hσ : Measurable σ) (hi : Measurable σ.symm) (η : Measure U) :
    translationStabilizer (Measure.map σ η) = (translationStabilizer η).map σ.toAddMonoidHom := by
  ext v
  obtain ⟨u,rfl⟩ := σ.surjective v
  rw [mem_translationStabilizer_map_iff σ hσ hi]
  simp only [AddSubgroup.mem_map]
  constructor
  · exact fun hu => ⟨u,hu,rfl⟩
  · rintro ⟨w,hw,he⟩
    exact σ.injective he ▸ hw

theorem translationStabilizer_projective_map (σ : U ≃+ V)
    (hσ : Measurable σ) (hi : Measurable σ.symm) (η : Measure U)
    {d : ℝ≥0} (hd : d ≠ 0) :
    translationStabilizer (d • Measure.map σ η) =
      (translationStabilizer η).map σ.toAddMonoidHom := by
  rw [translationStabilizer_smul _ hd,translationStabilizer_map σ hσ hi]

/-- The multiplier of a quasi-invariant translation is unchanged under
the projective covariance of leaf measures. -/
theorem translate_eigen_projective_map (σ : U ≃+ V) (hσ : Measurable σ)
    (η : Measure U) {u : U} {c : ℝ≥0} (h : translate u η = c • η) (d : ℝ≥0) :
    translate (σ u) (d • Measure.map σ η) = c • (d • Measure.map σ η) := by
  rw [translate_smul,translate_map_addEquiv σ hσ,h,Measure.map_smul]
  simp only [smul_smul,mul_comm]

end Covariance
end VV.BBEKLeafwiseStabilizer
