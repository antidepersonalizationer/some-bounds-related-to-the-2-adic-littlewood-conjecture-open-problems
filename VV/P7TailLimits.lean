import VV.P7Convergents
import VV.CylinderSeparation
import Mathlib.Topology.Algebra.Order.Floor

/-! Actual continued-fraction digits persist under irrational tail limits. -/

open Filter Set
open scoped Topology

namespace VV.P7TailLimits
open CylinderGeometry P7Convergents P7AdicLimits

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem tendsto_completeQuotient {z : ℕ → ℝ} {x : ℝ}
    (hz : Tendsto z atTop (𝓝 x)) (hx : Irrational x) (k : ℕ) :
    Tendsto (fun n => completeQuotient (z n) k) atTop (𝓝 (completeQuotient x k)) := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    exact ((continuousAt_fract ((completeQuotient_irrational hx k).ne_int _)).tendsto.comp ih).inv₀
      (completeQuotient_fract_ne_zero hx k)

theorem eventually_partialQuotient_eq {z : ℕ → ℝ} {x : ℝ}
    (hz : Tendsto z atTop (𝓝 x)) (hx : Irrational x) (k : ℕ) :
    ∀ᶠ n in atTop, partialQuotient (z n) k = partialQuotient x k := by
  have hlow : (⌊completeQuotient x k⌋ : ℝ) < completeQuotient x k :=
    (Int.floor_le _).lt_of_ne ((completeQuotient_irrational hx k).ne_int _).symm
  have hhigh := Int.lt_floor_add_one (completeQuotient x k)
  have hnear := (tendsto_completeQuotient hz hx k).eventually (Ioo_mem_nhds hlow hhigh)
  filter_upwards [hnear] with n hn
  exact Int.floor_eq_iff.mpr ⟨hn.1.le, hn.2⟩

theorem tail_irrational {x : ℝ} (hx : Irrational x) (n : ℕ) : Irrational (tail x n) := by
  exact (completeQuotient_irrational hx n).sub_intCast ⌊completeQuotient x n⌋

theorem tail_completeQuotient (x : ℝ) (n k : ℕ) :
    completeQuotient (tail x n) (k + 1) = completeQuotient x (n + k + 1) := by
  induction k with
  | zero => simp only [completeQuotient, tail, Int.fract_fract, Nat.add_zero]
  | succ k ih =>
    change (Int.fract (completeQuotient (tail x n) (k + 1)))⁻¹ =
      (Int.fract (completeQuotient x (n + (k + 1))))⁻¹
    rw [ih, Nat.add_assoc]

theorem tail_partialQuotient (x : ℝ) (n k : ℕ) :
    partialQuotient (tail x n) (k + 1) = partialQuotient x (n + k + 1) := by
  simp only [partialQuotient, tail_completeQuotient]

/-- The original eventual bound becomes a full bound at every irrational
limit of tails escaping along the continued fraction. -/
theorem bounded_digits_of_tail_limit {x y : ℝ} {C : ℕ}
    (hC : EventualBound x C) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (hy : Irrational y) (ht : Tendsto (fun n => tail x (φ n)) atTop (𝓝 y)) :
    ∀ k : ℕ, partialQuotient y (k + 1) ≤ (C : ℤ) := by
  obtain ⟨N, hN⟩ := hC
  intro k
  have hlarge := hφ.eventually (eventually_ge_atTop N)
  obtain ⟨n, hn, heq⟩ := (hlarge.and (eventually_partialQuotient_eq ht hy (k + 1))).exists
  rw [← heq, tail_partialQuotient]
  exact hN (φ n + k) (by omega)

/-- A recurrent finite word is preserved in any irrational limit along
occurrences of that word. Thus covering the genuine real limit set covers
all recurrent words without a symbolic-limit assumption. -/
theorem word_eq_of_occurrence_limit {x y : ℝ} (L : ℕ) (w : Fin L → ℤ)
    (φ : ℕ → ℕ) (hy : Irrational y)
    (ht : Tendsto (fun n => tail x (φ n)) atTop (𝓝 y))
    (hw : ∀ n, Problem7.wordAt (fun j => partialQuotient x (j + 1)) L (φ n) = w) :
    ∀ k : Fin L, partialQuotient y (k.val + 1) = w k := by
  intro k
  obtain ⟨n, hn⟩ := (eventually_partialQuotient_eq ht hy (k.val + 1)).exists
  rw [← hn, tail_partialQuotient]
  exact congrFun (hw n) k

def realRigiditySet (C : ℕ) : Set ℝ :=
  {y | ∃ v : ℤ_[2], (y, v) ∈ JointBadlyApproximable ((1 / ((C : ℝ) + 3)) / 2)}

/-- Both denominator parity classes are included: an even previous
denominator is transferred forward by one Gauss step. -/
def tailRigiditySet (C : ℕ) : Set ℝ :=
  {y | y ∈ realRigiditySet C ∨ ∃ a : ℤ, 1 ≤ a ∧ a ≤ (C : ℤ) ∧
    ∃ z ∈ realRigiditySet C, y = branch a z}

theorem exists_subsequence_joint_limit {x : ℝ} (hx : Irrational x)
    (C : ℕ) (hC : BOrbitBound x C) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hodd : ∀ n, ¬ (2 : ℤ) ∣ (prefixMatrix x (φ n)).d) :
    ∃ w ∈ JointBadlyApproximable ((1 / ((C : ℝ) + 3)) / 2),
      ∃ θ : ℕ → ℕ, StrictMono θ ∧
        Tendsto (fun n => tail x (φ (θ n))) atTop (𝓝 w.1) := by
  obtain ⟨w, _, θ, hθ, ht⟩ := joint_compact_subsequence
    (fun n => tail x (φ n))
    (fun n => unitRatio (prefixMatrix x (φ n)).c.toNat (prefixMatrix x (φ n)).d.toNat)
    (fun n => ⟨tail_nonneg x _, (tail_lt_one x _).le⟩)
  refine ⟨w, cf_joint_limit_mem hx C hC (φ ∘ θ) (hφ.comp hθ)
    (fun n => hodd (θ n)) ht, θ, hθ, ?_⟩
  exact (continuous_fst.tendsto w).comp ht

/-- Every recurrent word is realized by an actual bounded-alphabet
irrational in the zero-entropy candidate set. Both parity cases are
proved; no recurrence-to-limit or parity-transfer premise remains. -/
theorem recurrent_word_representative {x : ℝ} (hx : Irrational x)
    (C L : ℕ) (hC : BOrbitBound x C) (hL : 0 < L) (w : Fin L → ℤ)
    (hw : Problem7.RecurrentValue
      (Problem7.wordAt (fun j => partialQuotient x (j + 1)) L) w) :
    ∃ y ∈ tailRigiditySet C, Irrational y ∧ partialQuotient y 0 = 0 ∧
      (∀ k : ℕ, partialQuotient y (k + 1) ≤ (C : ℤ)) ∧
      ∀ k : Fin L, partialQuotient y (k.val + 1) = w k := by
  have hbound : EventualBound x C := by simpa using hC 0
  obtain ⟨φ, hφ, hword⟩ := extraction_of_frequently_atTop
    (P := fun j => Problem7.wordAt (fun k => partialQuotient x (k + 1)) L j = w)
    (frequently_atTop.mpr hw)
  have finish (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
      (hwords : ∀ n, Problem7.wordAt (fun j => partialQuotient x (j + 1)) L (ψ n) = w)
      (y : ℝ) (hyr : y ∈ tailRigiditySet C) (hyi : Irrational y)
      (ht : Tendsto (fun n => tail x (ψ n)) atTop (𝓝 y)) :
      ∃ y ∈ tailRigiditySet C, Irrational y ∧ partialQuotient y 0 = 0 ∧
        (∀ k : ℕ, partialQuotient y (k + 1) ≤ (C : ℤ)) ∧
        ∀ k : Fin L, partialQuotient y (k.val + 1) = w k := by
    refine ⟨y, hyr, hyi, ?_, bounded_digits_of_tail_limit hbound ψ hψ.tendsto_atTop hyi ht,
      word_eq_of_occurrence_limit L w ψ hyi ht hwords⟩
    obtain ⟨n, hn⟩ := (eventually_partialQuotient_eq ht hyi 0).exists
    rw [← hn]
    exact Int.floor_eq_iff.mpr ⟨by simpa using tail_nonneg x (ψ n), by simpa using tail_lt_one x (ψ n)⟩
  by_cases hodd : ∃ᶠ n in atTop, ¬ (2 : ℤ) ∣ (prefixMatrix x (φ n)).d
  · obtain ⟨η, hη, hηodd⟩ := extraction_of_frequently_atTop hodd
    obtain ⟨z, hz, θ, hθ, ht⟩ := exists_subsequence_joint_limit hx C hC
      (φ ∘ η) (hφ.comp hη) hηodd
    exact finish (φ ∘ η ∘ θ) (hφ.comp (hη.comp hθ)) (fun n => hword _)
      z.1 (Or.inl ⟨z.2, hz⟩)
      (jointBadlyApproximable_real_irrational (by positivity) hz) ht
  · have heven : ∀ᶠ n in atTop, (2 : ℤ) ∣ (prefixMatrix x (φ n)).d := by
      simpa only [not_not] using not_frequently.mp hodd
    obtain ⟨η, hη, hηeven⟩ := extraction_of_eventually_atTop heven
    let ψ := φ ∘ η
    have hψ : StrictMono ψ := hφ.comp hη
    have hnext : StrictMono (fun n => ψ n + 1) := fun i j hij => by exact Nat.add_lt_add_right (hψ hij) 1
    have hnextodd : ∀ n, ¬ (2 : ℤ) ∣ (prefixMatrix x (ψ n + 1)).d := by
      intro n
      have hc := (prefix_one_den_odd x (ψ n)).resolve_right (not_not_intro (hηeven n))
      simpa only [prefix_succ] using hc
    obtain ⟨z, hz, θ, hθ, ht⟩ := exists_subsequence_joint_limit hx C hC
      (fun n => ψ n + 1) hnext hnextodd
    let a : ℤ := w ⟨0, hL⟩
    have ha : ∀ n, partialQuotient x (ψ (θ n) + 1) = a := fun n =>
      congrFun (hword (η (θ n))) ⟨0, hL⟩
    have ha1 : 1 ≤ a := (ha 0) ▸ one_le_partialQuotient_succ hx (ψ (θ 0))
    have haC : a ≤ (C : ℤ) := by
      obtain ⟨N, hN⟩ := hbound
      obtain ⟨n, hn⟩ := ((hψ.comp hθ).tendsto_atTop.eventually (eventually_ge_atTop N)).exists
      rw [← ha n]
      exact hN _ hn
    have hzi : Irrational z.1 := jointBadlyApproximable_real_irrational (by positivity) hz
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hden : (a : ℝ) + z.1 ≠ 0 := (by linarith [hz.1.1] : 0 < (a : ℝ) + z.1).ne'
    have ht' : Tendsto (fun n => tail x (ψ (θ n))) atTop (𝓝 (branch a z.1)) := by
      have hh := (ht.const_add (a : ℝ)).inv₀ hden
      convert hh using 1
      funext n
      rw [tail_rec, ha]
      rfl
    have hyi : Irrational (branch a z.1) := (hzi.intCast_add a).inv
    exact finish (ψ ∘ θ) (hψ.comp hθ) (fun n => hword _)
      (branch a z.1) (Or.inr ⟨a, ha1, haC, z.1, ⟨z.2, hz⟩, rfl⟩) hyi ht'

end VV.P7TailLimits
