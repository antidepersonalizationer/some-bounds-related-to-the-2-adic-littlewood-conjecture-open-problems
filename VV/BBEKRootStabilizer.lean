import VV.BBEKLeafwiseRecurrence
import Mathlib.Topology.Order.IntermediateValue

/-! Elementary one-dimensional root subgroup consequences.  These do not
identify the stabilizers of different leaves; that is a separate recurrence
step. -/

noncomputable section
open Set Filter
open scoped Topology

namespace VV.BBEKLeafwiseStabilizer

theorem real_subgroup_pos_of_ne_bot (S : AddSubgroup ℝ) (hS : S ≠ ⊥) :
    ∃ u : ℝ, u ∈ S ∧ 0 < u := by
  have hex : ∃ u : ℝ, u ∈ S ∧ u ≠ 0 := by
    by_contra h
    push_neg at h
    apply hS
    apply bot_unique
    intro u hu
    exact h u hu
  obtain ⟨u,hu,hne⟩ := hex
  rcases lt_or_gt_of_ne hne with hn | hp
  · exact ⟨-u,S.neg_mem hu,neg_pos.mpr hn⟩
  · exact ⟨u,hu,hp⟩

/-- A nonzero closed additive subgroup of R stable under one strict positive
contraction is the entire one-dimensional root group. -/
theorem real_closed_subgroup_eq_top_of_contraction (S : AddSubgroup ℝ)
    (hclosed : IsClosed (S : Set ℝ)) (hS : S ≠ ⊥)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hscale : ∀ u ∈ S, a*u ∈ S) : S = ⊤ := by
  obtain ⟨u,hu,hupos⟩ := real_subgroup_pos_of_ne_bot S hS
  have hdense : Dense (S : Set ℝ) := S.dense_of_not_isolated_zero (by
    intro ε hε
    have ht : Tendsto (fun n : ℕ => a^n*u) atTop (𝓝 0) := by
      simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one ha.le ha1).mul_const u
    obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
    have hmem (n : ℕ) : a^n*u ∈ S := by
      induction n with
      | zero => simpa using hu
      | succ n ih => simpa only [pow_succ',mul_assoc] using hscale _ ih
    exact ⟨a^n*u,hmem n,mul_pos (pow_pos ha n) hupos,hn⟩)
  apply SetLike.coe_injective
  exact hclosed.closure_eq ▸ hdense.closure_eq

/-- In the real root group, a nontrivial connected closed additive subgroup
is already the full root group. -/
theorem real_connected_closed_subgroup_eq_top (S : AddSubgroup ℝ)
    (hclosed : IsClosed (S : Set ℝ)) (hconn : IsPreconnected (S : Set ℝ))
    (hS : S ≠ ⊥) : S = ⊤ := by
  apply real_closed_subgroup_eq_top_of_contraction S hclosed hS
    (a := 1/2) (by norm_num) (by norm_num)
  intro u hu
  by_cases hpos : 0 ≤ u
  · exact hconn.Icc_subset S.zero_mem hu ⟨by linarith,by linarith⟩
  · exact hconn.Icc_subset hu S.zero_mem ⟨by linarith,by linarith⟩

end VV.BBEKLeafwiseStabilizer
