import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Ergodic promotion of a nontrivial leaf stabilizer

Leafwise recurrence first gives a nontrivial stabilizer on a positive-measure
set.  Covariance under the full diagonal action makes that event invariant;
full diagonal ergodicity then makes it conull.  Combined with the already
proved one-dimensional `bot`/`top` dichotomies, this promotes the local
conclusion to full root invariance almost everywhere.
-/

noncomputable section
open Set Filter MeasureTheory

namespace VV.BBEKStabilizerErgodic

variable {A X U : Type*} [Group A] [AddCommGroup U] [MeasurableSpace X]
  [MulAction A X] {μ : Measure X}

def nontrivialEvent (S : X → AddSubgroup U) : Set X := {x | S x ≠ ⊥}

/-- Hit-open measurability of a closed-subgroup field already makes the
nontriviality event measurable: it is the event of hitting the open complement
of zero. -/
theorem measurableSet_nontrivialEvent_of_hit
    [TopologicalSpace U] [T1Space U] (S : X → AddSubgroup U)
    (hhit : ∀ O : Set U, IsOpen O →
      MeasurableSet {x | ∃ u ∈ S x, u ∈ O}) :
    MeasurableSet (nontrivialEvent S) := by
  have he : nontrivialEvent S = {x | ∃ u ∈ S x, u ∈ ({0} : Set U)ᶜ} := by
    ext x
    change (S x ≠ ⊥) ↔ ∃ u, u ∈ S x ∧ u ≠ 0
    constructor
    · intro hx
      by_contra hn
      push_neg at hn
      apply hx
      apply bot_unique
      intro u hu
      simpa only [AddSubgroup.mem_bot] using hn u hu
    · rintro ⟨u, hu, hu0⟩ hx
      rw [hx] at hu
      exact hu0 (by simpa only [AddSubgroup.mem_bot] using hu)
  rw [he]
  exact hhit _ isClosed_singleton.isOpen_compl

/-- An additive equivalence preserves nontriviality of a subgroup. -/
theorem map_ne_bot_iff (e : U ≃+ U) (S : AddSubgroup U) :
    S.map e.toAddMonoidHom ≠ ⊥ ↔ S ≠ ⊥ := by
  constructor
  · contrapose!
    rintro rfl
    simp
  · intro hS hmap
    apply hS
    apply le_bot_iff.mp
    intro u hu
    have heu : e u ∈ S.map e.toAddMonoidHom := ⟨u, hu, rfl⟩
    rw [hmap] at heu
    simp only [AddSubgroup.mem_bot] at heu
    apply e.injective
    simpa using heu

/-- Covariance of a subgroup field makes its nontriviality event invariant
modulo the base measure. -/
theorem nontrivialEvent_preimage_ae_eq
    (S : X → AddSubgroup U) (σ : A → U ≃+ U)
    (hcov : ∀ a : A, ∀ᵐ x ∂μ,
      S (a • x) = (S x).map (σ a).toAddMonoidHom) (a : A) :
    (a • ·) ⁻¹' nontrivialEvent S =ᵐ[μ] nontrivialEvent S := by
  filter_upwards [hcov a] with x hx
  change (S (a • x) ≠ ⊥) = (S x ≠ ⊥)
  rw [hx, propext (map_ne_bot_iff (σ a) (S x))]

/-- If a covariant subgroup field is nontrivial on a set of positive measure,
full-action ergodicity makes it nontrivial almost everywhere. -/
theorem ae_ne_bot_of_ergodic_of_pos
    [ErgodicSMul A X μ] (S : X → AddSubgroup U) (σ : A → U ≃+ U)
    (hmeas : MeasurableSet (nontrivialEvent S))
    (hcov : ∀ a : A, ∀ᵐ x ∂μ,
      S (a • x) = (S x).map (σ a).toAddMonoidHom)
    (hpos : μ (nontrivialEvent S) ≠ 0) :
    ∀ᵐ x ∂μ, S x ≠ ⊥ := by
  have hc := aeconst_of_forall_preimage_smul_ae_eq A hmeas.nullMeasurableSet
    (nontrivialEvent_preimage_ae_eq S σ hcov)
  rcases eventuallyConst_set.mp hc with hfull | hzero
  · exact hfull
  · exfalso
    apply hpos
    apply ae_eq_empty.mp
    filter_upwards [hzero] with x hx
    apply propext
    constructor
    · exact fun h => (hx h).elim
    · exact fun h => h.elim

/-- The form consumed by the root-invariance reconstruction: the fibrewise
`bot`/`top` dichotomy plus one positive-measure nontriviality statement gives
`top` almost everywhere. -/
theorem ae_eq_top_of_ergodic_of_pos
    [ErgodicSMul A X μ] (S : X → AddSubgroup U) (σ : A → U ≃+ U)
    (hmeas : MeasurableSet (nontrivialEvent S))
    (hcov : ∀ a : A, ∀ᵐ x ∂μ,
      S (a • x) = (S x).map (σ a).toAddMonoidHom)
    (hdichotomy : ∀ᵐ x ∂μ, S x = ⊥ ∨ S x = ⊤)
    (hpos : μ (nontrivialEvent S) ≠ 0) :
    ∀ᵐ x ∂μ, S x = ⊤ := by
  filter_upwards [ae_ne_bot_of_ergodic_of_pos S σ hmeas hcov hpos,
    hdichotomy] with x hne hd
  exact hd.resolve_left hne

end VV.BBEKStabilizerErgodic
