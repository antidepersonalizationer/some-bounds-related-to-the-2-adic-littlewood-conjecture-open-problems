import VV.Semantics

/-!
The literal equality-of-infinite-tails relation, as distinct from the
unimodular Möbius relation in `Problem3`. Tail deletion invariance of the
limsup is proved here; Serret's theorem is not assumed in this module.
-/
namespace VV

def TailEquivalent (x y : ℝ) : Prop :=
  ∃ m n : ℕ, ∀ k : ℕ,
    partialQuotient x (m + k + 1) = partialQuotient y (n + k + 1)

theorem TailEquivalent.refl (x : ℝ) : TailEquivalent x x :=
  ⟨0, 0, fun _ => rfl⟩

theorem TailEquivalent.symm {x y : ℝ} (h : TailEquivalent x y) :
    TailEquivalent y x := by
  obtain ⟨m, n, h⟩ := h
  exact ⟨n, m, fun k => (h k).symm⟩

theorem TailEquivalent.trans {x y z : ℝ}
    (hxy : TailEquivalent x y) (hyz : TailEquivalent y z) :
    TailEquivalent x z := by
  obtain ⟨m, n, hxy⟩ := hxy
  obtain ⟨p, q, hyz⟩ := hyz
  refine ⟨m + p, q + n, fun k => ?_⟩
  calc
    partialQuotient x (m + p + k + 1) = partialQuotient y (n + (p + k) + 1) := by
      simpa only [Nat.add_assoc] using hxy (p + k)
    _ = partialQuotient z (q + n + k + 1) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hyz (n + k)

theorem TailEquivalent.eventualBound_iff {x y : ℝ}
    (h : TailEquivalent x y) (C : ℕ) : EventualBound x C ↔ EventualBound y C := by
  have oneWay {x y : ℝ} (h : TailEquivalent x y) :
      EventualBound x C → EventualBound y C := by
    obtain ⟨m, n, h⟩ := h
    rintro ⟨N, hN⟩
    refine ⟨n + N, fun i hi => ?_⟩
    have heq := h (i - n)
    have hni : n + (i - n) = i := by omega
    rw [hni] at heq
    rw [← heq]
    exact hN _ (by omega)
  exact ⟨oneWay h, oneWay h.symm⟩

theorem TailEquivalent.B_eq {x y : ℝ} (h : TailEquivalent x y) : B x = B y := by
  apply le_antisymm
  · by_cases hy : B y = ⊤
    · simp [hy]
    · obtain ⟨C, hC⟩ := ENat.ne_top_iff_exists.mp hy
      rw [← hC, B_le_iff]
      apply (h.eventualBound_iff C).mpr
      rw [← B_le_iff, ← hC]
  · by_cases hx : B x = ⊤
    · simp [hx]
    · obtain ⟨C, hC⟩ := ENat.ne_top_iff_exists.mp hx
      rw [← hC, B_le_iff]
      apply (h.eventualBound_iff C).mp
      rw [← B_le_iff, ← hC]

theorem completeQuotient_add (x : ℝ) (m n : ℕ) :
    completeQuotient (completeQuotient x m) n = completeQuotient x (m + n) := by
  induction n with
  | zero => simp only [completeQuotient, Nat.add_zero]
  | succ n ih => simp only [completeQuotient, Nat.add_succ, ih]; rfl

theorem tailEquivalent_completeQuotient (x : ℝ) (m : ℕ) :
    TailEquivalent x (completeQuotient x m) := by
  refine ⟨m, 0, fun k => ?_⟩
  simp only [partialQuotient, Nat.zero_add, completeQuotient_add, Nat.add_assoc]

theorem tailEquivalent_of_completeQuotient_eq {x y : ℝ} {m n : ℕ}
    (h : completeQuotient x m = completeQuotient y n) : TailEquivalent x y :=
  (tailEquivalent_completeQuotient x m).trans
    (h ▸ (tailEquivalent_completeQuotient y n).symm)

def Problem3Triple (x : ℝ) : Prop :=
  Irrational x ∧ TailEquivalent x (x / 2) ∧ TailEquivalent x ((x + 1) / 2)

end VV
