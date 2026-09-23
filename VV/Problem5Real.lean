import VV.Semantics
import VV.QuadraticScaling

/-!
# The real-number Problem 5 conclusion from the finite-window theorem

This module derives the conclusion from a real-CF window classification.
The classification is now proved in `P5FiniteCheck` from one explicitly
admitted finite graph check; all transducer/tail soundness and infinite
path arguments have been proved in the intervening modules.
-/

namespace VV.Problem5Real

open QuadraticScaling

/-- One finite set of primitive
discriminants covers the middle of every low 31-layer window. This is a
mathematical classification theorem, not just a finite graph check. -/
def WindowClassification : Prop :=
  ∃ S : Finset ℕ, ∀ x : ℝ, Irrational x →
    (∀ k : ℕ, k ≤ 30 → VV.EventualBound ((2 : ℝ) ^ k * x) 10) →
    ∃ Q : Quadratic,
      Q.eval ((2 : ℝ) ^ 15 * x) = 0 ∧
      VV.Problem3.PrimitiveTriple Q.A Q.B Q.C ∧ Q.disc.natAbs ∈ S

/-- Full specialization to actual real numbers and actual continued
fraction digits, conditional only on `WindowClassification`. -/
theorem problem5_of_window_classification
    (classification : WindowClassification) : VV.Problem5Statement := by
  apply VV.problem5_iff_no_bound_ten.mpr
  intro x hx allLow
  obtain ⟨S, classify⟩ := classification
  obtain ⟨Q, hQ, pQ, _⟩ := classify x hx (fun k _ => allLow k)
  let β : ℝ := (2 : ℝ) ^ 15 * x
  have hβ : Irrational β := VV.irrational_dyadic_mul hx 15
  have hA : Q.A ≠ 0 := A_ne_zero_of_primitive_irrational_root Q hβ hQ pQ
  have unbounded := normalizedScale_discriminants_unbounded Q hA hβ hQ
  apply VV.Problem5.unbounded_sequence_not_in_finite_set
    (fun j => (Q.normalizedScale j).disc.natAbs) unbounded S
  intro j
  have hxj := VV.irrational_dyadic_mul hx j
  have lowj := VV.bOrbitBound_shift allLow j
  obtain ⟨R, hR, pR, hmem⟩ := classify ((2 : ℝ) ^ j * x) hxj (fun k _ => lowj k)
  have hroot : (Q.normalizedScale j).eval ((2 : ℝ) ^ j * β) = 0 :=
    normalizedScale_root Q hA hQ j
  have hR' : R.eval ((2 : ℝ) ^ j * β) = 0 := by
    have harg : (2 : ℝ) ^ j * β = (2 : ℝ) ^ 15 * ((2 : ℝ) ^ j * x) := by
      dsimp [β]
      ring
    rw [harg]
    exact hR
  have hdisc := primitive_same_root_disc (Q.normalizedScale j) R
    (VV.irrational_dyadic_mul hβ j) hroot hR'
    (normalizedScale_primitive Q hA j) pR
  simpa only [hdisc] using hmem

/-- The same theorem in the source paper's extended-natural limsup notation. -/
theorem problem5_limsup_of_window_classification
    (classification : WindowClassification) :
    ∀ x : ℝ, Irrational x → ∃ k : ℕ, (11 : ℕ∞) ≤ VV.B ((2 : ℝ) ^ k * x) :=
  VV.problem5_limsup_iff.mp (problem5_of_window_classification classification)

/-- The stronger consequence in the source: after a finite initial
segment, every consecutive 31 layers includes a fixed layer with
arbitrarily late partial quotients at least 11. -/
theorem eventual_every_31_real_layers
    (classification : WindowClassification) (x : ℝ) (hx : Irrational x) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ k : ℕ, k ≤ 30 ∧
      VV.DigitsFrequentlyAtLeast ((2 : ℝ) ^ (j + k) * x) 11 := by
  classical
  obtain ⟨S, classify⟩ := classification
  let low : ℕ → Prop := fun j =>
    ∀ k : ℕ, k ≤ 30 → VV.EventualBound ((2 : ℝ) ^ (j + k) * x) 10
  have finish (j : ℕ) (h : ¬ low j) : ∃ k : ℕ, k ≤ 30 ∧
      VV.DigitsFrequentlyAtLeast ((2 : ℝ) ^ (j + k) * x) 11 := by
    by_contra h'
    apply h
    intro k hk
    by_contra hb
    exact h' ⟨k, hk, (VV.not_eventualBound_iff _ 10).mp hb⟩
  by_cases anyLow : ∃ j, low j
  · obtain ⟨j₀, hj₀⟩ := anyLow
    have hbase : Irrational ((2 : ℝ) ^ j₀ * x) := VV.irrational_dyadic_mul hx j₀
    obtain ⟨Q, hQ, pQ, _⟩ := classify ((2 : ℝ) ^ j₀ * x) hbase (by
      intro k hk
      simpa only [pow_add, mul_assoc, mul_left_comm] using hj₀ k hk)
    let β : ℝ := (2 : ℝ) ^ 15 * ((2 : ℝ) ^ j₀ * x)
    have hβ : Irrational β := VV.irrational_dyadic_mul hbase 15
    have hA := A_ne_zero_of_primitive_irrational_root Q hβ hQ pQ
    let M := S.sup id
    refine ⟨j₀ + Q.A.natAbs ^ 2 * M, ?_⟩
    intro j hj
    apply finish j
    intro hjlow
    have hshift : j₀ + (j - j₀) = j := by omega
    have hlarge := VV.Problem5.reduced_discriminants_eventually_above
      Q.A.natAbs Q.disc.natAbs
      (VV.Problem5.scaledContent Q.A.natAbs Q.B.natAbs Q.C.natAbs)
      (fun t => (Q.normalizedScale t).disc.natAbs)
      (Int.natAbs_pos.mpr (disc_ne_zero_of_irrational_root Q hA hβ hQ))
      (VV.Problem5.scaledContent_le (Int.natAbs_pos.mpr hA) Q.B.natAbs Q.C.natAbs)
      (normalizedScale_abs_discriminant Q) M (j - j₀) (by omega)
    obtain ⟨R, hR, pR, hmem⟩ := classify ((2 : ℝ) ^ j * x)
      (VV.irrational_dyadic_mul hx j) (by
        intro k hk
        simpa only [pow_add, mul_assoc, mul_left_comm] using hjlow k hk)
    have harg : (2 : ℝ) ^ (j - j₀) * β = (2 : ℝ) ^ 15 * ((2 : ℝ) ^ j * x) := by
      calc
        (2 : ℝ) ^ (j - j₀) * β =
            (2 : ℝ) ^ 15 * ((2 : ℝ) ^ (j₀ + (j - j₀)) * x) := by
          dsimp [β]
          rw [pow_add]
          ring
        _ = (2 : ℝ) ^ 15 * ((2 : ℝ) ^ j * x) := by rw [hshift]
    have hroot := normalizedScale_root Q hA hQ (j - j₀)
    have hR' : R.eval ((2 : ℝ) ^ (j - j₀) * β) = 0 := by rwa [harg]
    have hdisc := primitive_same_root_disc (Q.normalizedScale (j - j₀)) R
      (VV.irrational_dyadic_mul hβ (j - j₀)) hroot hR'
      (normalizedScale_primitive Q hA (j - j₀)) pR
    have hm : (Q.normalizedScale (j - j₀)).disc.natAbs ≤ M := by
      have := Finset.le_sup (f := id) hmem
      simpa only [hdisc] using this
    exact (not_lt_of_ge hm) hlarge
  · exact ⟨0, fun j _ => finish j (fun hj => anyLow ⟨j, hj⟩)⟩

end VV.Problem5Real
