import VV.Problem4
import VV.TailEquivalence
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Problem 4 on actual continued-fraction classes

This module defines the original objects using `partialQuotient` and literal
equality of eventual tails, and isolates the counting step from the encoding.
`VV.P4Encoding` constructs that encoding from the actual Hurwitz transducer
and proves the unconditional final bound. Finiteness is a conclusion.
-/

namespace VV.Problem4

/-- A period of the eventual positive-index partial-quotient sequence. -/
def EventualPeriod (x : ℝ) (ℓ : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, partialQuotient x (n + ℓ + 1) = partialQuotient x (n + 1)

/-- The least positive eventual period length, without assuming periodicity. -/
def ExactEventualPeriod (x : ℝ) (ℓ : ℕ) : Prop :=
  0 < ℓ ∧ EventualPeriod x ℓ ∧ ∀ k : ℕ, 0 < k → k < ℓ → ¬EventualPeriod x k

theorem eventualPeriod_iff_of_tailEquivalent {x y : ℝ}
    (h : TailEquivalent x y) (ℓ : ℕ) : EventualPeriod x ℓ ↔ EventualPeriod y ℓ := by
  have oneWay {x y : ℝ} (h : TailEquivalent x y) :
      EventualPeriod x ℓ → EventualPeriod y ℓ := by
    obtain ⟨m, n, h⟩ := h
    rintro ⟨N, hN⟩
    refine ⟨n + N, fun i hi => ?_⟩
    have heq₁ := h (i - n)
    have heq₂ := h (i - n + ℓ)
    have hni : n + (i - n) = i := by omega
    have hniℓ : n + (i - n + ℓ) = i + ℓ := by omega
    rw [hni] at heq₁
    rw [hniℓ] at heq₂
    rw [← heq₁, ← heq₂]
    simpa only [Nat.add_assoc] using hN (m + (i - n)) (by omega)
  exact ⟨oneWay h, oneWay h.symm⟩

theorem exactEventualPeriod_iff_of_tailEquivalent {x y : ℝ}
    (h : TailEquivalent x y) (ℓ : ℕ) : ExactEventualPeriod x ℓ ↔ ExactEventualPeriod y ℓ := by
  unfold ExactEventualPeriod
  simp_rw [eventualPeriod_iff_of_tailEquivalent h]

/-- A real representative that itself meets the triple-tail requirement and
has the specified least eventual period. -/
def Representative (ℓ : ℕ) :=
  {x : ℝ // Problem3Triple x ∧ ExactEventualPeriod x ℓ}

def representativeSetoid (ℓ : ℕ) : Setoid (Representative ℓ) where
  r x y := TailEquivalent x.val y.val
  iseqv := {
    refl := fun x => TailEquivalent.refl x.val
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂ }

/-- The actual classes requested in Problem 4, with cyclic shifts and finite
prefixes identified through their infinite continued-fraction tails. -/
def Class (ℓ : ℕ) := Quotient (representativeSetoid ℓ)

def toClass {ℓ : ℕ} (x : Representative ℓ) : Class ℓ := Quotient.mk _ x

theorem toClass_eq_iff {ℓ : ℕ} (x y : Representative ℓ) :
    toClass x = toClass y ↔ TailEquivalent x.val y.val := Quotient.eq

/-- The encoding interface constructed in `VV.P4Encoding.hasRootedEncoding`.
The `Fin ℓ` factor records all possible roots of a least-period class. -/
def HasRootedEncoding (ℓ : ℕ) : Prop :=
  ∃ encode : Class ℓ × Fin ℓ → Template ℓ, Function.Injective encode

theorem finite_class_of_rooted_encoding {ℓ : ℕ} (hℓ : 0 < ℓ)
    (henc : HasRootedEncoding ℓ) : Finite (Class ℓ) := by
  obtain ⟨encode, hinj⟩ := henc
  apply Finite.of_injective (fun x : Class ℓ => encode (x, ⟨0, hℓ⟩))
  intro a b hab
  exact congrArg Prod.fst (hinj hab)

/-- This is the precise conditional bound for the actual continued-fraction
classes. No pre-existing finiteness of the class space is assumed. -/
theorem actual_class_count_le {ℓ : ℕ} (hℓ : 0 < ℓ)
    (henc : HasRootedEncoding ℓ) : Nat.card (Class ℓ) ≤ 3 * ℓ * 4 ^ ℓ := by
  letI : Finite (Class ℓ) := finite_class_of_rooted_encoding hℓ henc
  letI : Fintype (Class ℓ) := Fintype.ofFinite _
  obtain ⟨encode, hinj⟩ := henc
  simpa only [Nat.card_eq_fintype_card] using class_count_le hℓ encode hinj

theorem actual_finiteness_and_bound {ℓ : ℕ} (hℓ : 0 < ℓ)
    (henc : HasRootedEncoding ℓ) :
    Finite (Class ℓ) ∧ Nat.card (Class ℓ) ≤ 3 * ℓ * 4 ^ ℓ :=
  ⟨finite_class_of_rooted_encoding hℓ henc, actual_class_count_le hℓ henc⟩

end VV.Problem4
