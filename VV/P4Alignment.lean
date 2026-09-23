import VV.P4Period

namespace VV.Hurwitz

/-- Two purely periodic actual CF streams with the same positive period
and the same eventual tail differ by a cyclic phase less than that period. -/
theorem digit_alignment_of_tailEquivalent {x y : ℝ} {p : ℕ}
    (hx : DigitPeriod x p) (hy : DigitPeriod y p) (hp : 0 < p)
    (hxy : TailEquivalent x y) :
    ∃ r : ℕ, r < p ∧ ∀ k : ℕ,
      partialQuotient y k = partialQuotient x (r + k) := by
  obtain ⟨m,n,h⟩ := hxy
  let K := p * (n + 2)
  have hK : n + 1 ≤ K := by dsimp [K]; nlinarith
  let j := K - (n + 1)
  let t := m + j + 1
  have halign : ∀ k : ℕ, partialQuotient y k = partialQuotient x (t + k) := by
    intro k
    have he := h (j + k)
    have hi : n + (j + k) + 1 = k + p * (n + 2) := by dsimp [j,K] at *; omega
    have hi' : m + (j + k) + 1 = t + k := by dsimp [t]; omega
    rw [hi,hi',nat_period_mul hy] at he
    exact he.symm
  refine ⟨t % p,Nat.mod_lt t hp,fun k => ?_⟩
  have he := nat_period_mul hx (t % p + k) (t / p)
  have hi : t % p + k + p * (t / p) = t + k := by
    calc
      _ = (t % p + p * (t / p)) + k := by omega
      _ = _ := by rw [Nat.mod_add_div]
  rw [hi] at he
  exact (halign k).trans he

/-- A same-length positive output cycle is a cyclic block of the input,
with an explicit bounded phase. This is the phase stored in the finite
Problem 4 templates. -/
theorem cycle_block_alignment {x y : ℝ} {w v : List ℤ}
    (hx : CycleModel x w) (hy : CycleModel y v)
    (hw : ∀ a ∈ w, 1 ≤ a) (hv : ∀ a ∈ v, 1 ≤ a)
    (hlen : v.length = w.length) (hpos : 0 < w.length)
    (hxy : TailEquivalent x y) :
    ∃ r : ℕ, r < w.length ∧ v = P5Period.digitBlock x r w.length := by
  have hyp : DigitPeriod y w.length := hlen ▸ hy.digitPeriod hv
  obtain ⟨r,hr,hd⟩ := digit_alignment_of_tailEquivalent (hx.digitPeriod hw) hyp hpos hxy
  refine ⟨r,hr,?_⟩
  rw [← hy.digitBlock hv,hlen]
  apply digitBlock_eq_of_digits_eq
  simpa only [Nat.zero_add] using hd

end VV.Hurwitz
