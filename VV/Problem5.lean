import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Problem 5: the non-computational core of the lower bound 11

Source: GPT Work, `完成11下界证明`, first turn, 2026-09-15.
The retrieved source says that a 31-layer low-digit window forces the
middle layer into a finite list of 103 periodic continued-fraction tails.

This file does **not** pretend that this statement is a finite computation:
the finite graph checks and their semantic connection to real continued
fractions are different obligations.  All theorems below are kernel proofs,
with the missing semantic/classification inputs visible as arguments.
There are no `sorry`s in this file.
-/

namespace VV.Problem5

/-- `B ≤ C`, expressed without any convention for infinite limsup. -/
def TailBound (a : ℕ → ℕ) (C : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → a n ≤ C

/-- `B ≥ L` for the integer threshold `L`: arbitrarily late digits are ≥ L. -/
def RecurrentLarge (a : ℕ → ℕ) (L : ℕ) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ L ≤ a n

theorem not_tailBound_iff_recurrentLarge (a : ℕ → ℕ) (C : ℕ) :
    ¬ TailBound a C ↔ RecurrentLarge a (C + 1) := by
  simp only [TailBound, RecurrentLarge, not_exists, not_forall, not_le]
  constructor
  · intro h N
    obtain ⟨n, hn, hn'⟩ := h N
    exact ⟨n, hn, by omega⟩
  · intro h N
    obtain ⟨n, hn, hn'⟩ := h N
    exact ⟨n, hn, by omega⟩

theorem not_recurrentLarge_iff_tailBound (a : ℕ → ℕ) (C : ℕ) :
    ¬ RecurrentLarge a (C + 1) ↔ TailBound a C := by
  rw [← not_tailBound_iff_recurrentLarge]
  exact not_not

/-- This is eventual periodicity, not merely recurrence of a finite block. -/
def TailPeriodic {α : Type*} (a : ℕ → α) : Prop :=
  ∃ N p, 0 < p ∧ ∀ n, N ≤ n → a (n + p) = a n

theorem deterministic_path_repeat {V : Type*} (next : V → V)
    (s : ℕ → V) (step : ∀ n, s (n + 1) = next (s n))
    {i j : ℕ} (h : s i = s j) :
    ∀ t, s (i + t) = s (j + t) := by
  intro t
  induction t with
  | zero => simpa using h
  | succ t ih =>
      simpa only [Nat.add_succ, step, ih]

/-- The graph-to-infinite-path argument is proved, rather than included in
the admitted finite outdegree check. -/
theorem finite_deterministic_path_periodic {V α : Type*} [Finite V]
    (next : V → V) (label : V → α) (s : ℕ → V)
    (step : ∀ n, s (n + 1) = next (s n)) :
    TailPeriodic (fun n => label (s n)) := by
  obtain ⟨i, j, hij, hs⟩ := Finite.exists_ne_map_eq_of_infinite s
  have pair : ∃ i j, i < j ∧ s i = s j := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, hs⟩
    · exact ⟨j, i, h, hs.symm⟩
  obtain ⟨i, j, hij, hs⟩ := pair
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  have h := deterministic_path_repeat next s step hs (n - i)
  have hn₁ : i + (n - i) = n := by omega
  have hn₂ : j + (n - i) = n + (j - i) := by omega
  rw [hn₁, hn₂] at h
  exact congrArg label h.symm

/-- A relation with a unique outgoing edge supplies a deterministic path.
For a concrete finite graph, `uniqueNext` is a genuinely finite obligation. -/
theorem finite_unique_edge_path_periodic {V α : Type*} [Finite V]
    (edge : V → V → Prop) (label : V → α)
    (uniqueNext : ∀ v, ∃! w, edge v w)
    (s : ℕ → V) (path : ∀ n, edge (s n) (s (n + 1))) :
    TailPeriodic (fun n => label (s n)) := by
  classical
  let next : V → V := fun v => Classical.choose (uniqueNext v)
  apply finite_deterministic_path_periodic next label s
  intro n
  exact (Classical.choose_spec (uniqueNext (s n))).2 _ (path n)

/-- One-way switching between two choices: after the first `true`, the
choice can never return to `false`.  This proves the infinite part of the
short `UV`-forbidden argument in the later source turns. -/
theorem no_true_false_eventually_constant (a : ℕ → Bool)
    (noBack : ∀ n, a n = true → a (n + 1) = true) :
    ∃ N b, ∀ n, N ≤ n → a n = b := by
  by_cases h : ∃ N, a N = true
  · obtain ⟨N, hN⟩ := h
    refine ⟨N, true, ?_⟩
    intro n hn
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction t with
    | zero => simpa using hN
    | succ t ih =>
        simpa only [Nat.add_succ] using noBack (N + t) (ih (by omega))
  · refine ⟨0, false, ?_⟩
    intro n _
    cases hn : a n with
    | false => rfl
    | true => exact False.elim (h ⟨n, hn⟩)

/-- If a primitive quadratic is scaled by `2^j`, its content divides `A`.
Here `b,c` may be the absolute values of the signed coefficients. -/
def scaledContent (A b c j : ℕ) : ℕ :=
  Nat.gcd A (Nat.gcd (2 ^ j * b) (4 ^ j * c))

theorem scaledContent_dvd (A b c j : ℕ) : scaledContent A b c j ∣ A :=
  Nat.gcd_dvd_left _ _

theorem scaledContent_le {A : ℕ} (hA : 0 < A) (b c j : ℕ) :
    scaledContent A b c j ≤ A :=
  Nat.le_of_dvd hA (scaledContent_dvd A b c j)

/-- The discriminant of a binary quadratic form after a linear change of
variables. This is the algebraic part of CF-equivalence invariance. -/
theorem discriminant_change_of_variables (A B C a b c d : ℤ) :
    (2 * A * a * b + B * (a * d + b * c) + 2 * C * c * d) ^ 2 -
      4 * (A * a ^ 2 + B * a * c + C * c ^ 2) *
        (A * b ^ 2 + B * b * d + C * d ^ 2) =
      (a * d - b * c) ^ 2 * (B ^ 2 - 4 * A * C) := by
  ring

theorem unimodular_discriminant_invariant (A B C a b c d : ℤ)
    (det : (a * d - b * c) ^ 2 = 1) :
    (2 * A * a * b + B * (a * d + b * c) + 2 * C * c * d) ^ 2 -
      4 * (A * a ^ 2 + B * a * c + C * c ^ 2) *
        (A * b ^ 2 + B * b * d + C * d ^ 2) = B ^ 2 - 4 * A * C := by
  rw [discriminant_change_of_variables, det, one_mul]

/-- Exact discriminant normalization. The coefficient identities are
ordinary integer equalities, so no unsafe integer-division cancellation
or unproved primitive-polynomial assertion is used. -/
theorem normalized_discriminant_identity
    (A B C A' B' C' g : ℤ) (j : ℕ)
    (hA : g * A' = A) (hB : g * B' = 2 ^ j * B)
    (hC : g * C' = 4 ^ j * C) :
    g ^ 2 * (B' ^ 2 - 4 * A' * C') = 4 ^ j * (B ^ 2 - 4 * A * C) := by
  have hpow : ((2 : ℤ) ^ j) ^ 2 = 4 ^ j := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    g ^ 2 * (B' ^ 2 - 4 * A' * C') =
        (g * B') ^ 2 - 4 * (g * A') * (g * C') := by ring
    _ = (2 ^ j * B) ^ 2 - 4 * A * (4 ^ j * C) := by rw [hA, hB, hC]
    _ = 4 ^ j * (B ^ 2 - 4 * A * C) := by rw [mul_pow, hpow]; ring

/-- A positive leading coefficient prevents the normalization content
from vanishing; this does not require a finite check. -/
theorem scaledContent_pos {A : ℕ} (hA : 0 < A) (b c j : ℕ) :
    0 < scaledContent A b c j := by
  exact Nat.gcd_pos_of_pos_left _ hA

/-- The discriminant growth argument only needs the exact normalization
identity and a bound on content. It does not enumerate periodic words. -/
theorem reduced_discriminants_unbounded (A Δ : ℕ) (g D : ℕ → ℕ)
    (hΔ : 0 < Δ) (hg : ∀ j, g j ≤ A)
    (identity : ∀ j, g j ^ 2 * D j = 4 ^ j * Δ) :
    ∀ M, ∃ j, M < D j := by
  intro M
  let j := A ^ 2 * M
  refine ⟨j, ?_⟩
  by_contra h
  have hD : D j ≤ M := by omega
  have hpow : 2 ^ j ≤ 4 ^ j := Nat.pow_le_pow_left (by omega) j
  have hsmall : j < 4 ^ j := lt_of_lt_of_le (Nat.lt_two_pow_self) hpow
  have hΔ' : 4 ^ j ≤ 4 ^ j * Δ := by
    simpa using Nat.mul_le_mul_left (4 ^ j) hΔ
  have hsq : g j ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left (hg j) 2
  have hbig : 4 ^ j * Δ ≤ A ^ 2 * M := by
    rw [← identity j]
    exact Nat.mul_le_mul hsq hD
  have : j < A ^ 2 * M := lt_of_lt_of_le hsmall (hΔ'.trans hbig)
  exact (Nat.lt_irrefl j) this

theorem quadratic_content_discriminants_unbounded {A : ℕ} (hA : 0 < A)
    (b c Δ : ℕ) (D : ℕ → ℕ) (hΔ : 0 < Δ)
    (identity : ∀ j, scaledContent A b c j ^ 2 * D j = 4 ^ j * Δ) :
    ∀ M, ∃ j, M < D j :=
  reduced_discriminants_unbounded A Δ (scaledContent A b c) D hΔ
    (scaledContent_le hA b c) identity

/-- A deliberately coarse, fully explicit escape threshold. No analytic
limit theorem is needed: `j < 2^j ≤ 4^j` suffices. -/
theorem reduced_discriminants_eventually_above (A Δ : ℕ) (g D : ℕ → ℕ)
    (hΔ : 0 < Δ) (hg : ∀ j, g j ≤ A)
    (identity : ∀ j, g j ^ 2 * D j = 4 ^ j * Δ)
    (M j : ℕ) (hj : A ^ 2 * M ≤ j) : M < D j := by
  by_contra h
  have hD : D j ≤ M := by omega
  have hpow : 2 ^ j ≤ 4 ^ j := Nat.pow_le_pow_left (by omega) j
  have hsmall : j < 4 ^ j := lt_of_lt_of_le (Nat.lt_two_pow_self) hpow
  have hΔ' : 4 ^ j ≤ 4 ^ j * Δ := by
    simpa using Nat.mul_le_mul_left (4 ^ j) hΔ
  have hsq : g j ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left (hg j) 2
  have hbig : 4 ^ j * Δ ≤ A ^ 2 * M := by
    rw [← identity j]
    exact Nat.mul_le_mul hsq hD
  have : j < j := hsmall.trans_le (hΔ'.trans (hbig.trans hj))
  exact (Nat.lt_irrefl j) this

theorem unbounded_sequence_not_in_finite_set (D : ℕ → ℕ)
    (unbounded : ∀ M, ∃ j, M < D j) (S : Finset ℕ) :
    ¬ ∀ j, D j ∈ S := by
  intro h
  obtain ⟨j, hj⟩ := unbounded (S.sup id)
  have := Finset.le_sup (f := id) (h j)
  exact (not_lt_of_ge this) hj

/-- The arithmetic final contradiction, with no analytic or finite-graph
theorem hidden in an admitted statement. -/
theorem discriminant_contradiction {A : ℕ} (hA : 0 < A)
    (b c Δ : ℕ) (D : ℕ → ℕ) (hΔ : 0 < Δ)
    (identity : ∀ j, scaledContent A b c j ^ 2 * D j = 4 ^ j * Δ)
    (S : Finset ℕ) (membership : ∀ j, D j ∈ S) : False := by
  exact unbounded_sequence_not_in_finite_set D
    (quadratic_content_discriminants_unbounded hA b c Δ D hΔ identity) S membership

/-- A low 31-layer window beginning at `j`. Its middle layer is `j+15`. -/
def LowWindow (digits : ℕ → ℕ → ℕ) (j : ℕ) : Prop :=
  ∀ k, k ≤ 30 → TailBound (digits (j + k)) 10

theorem all_low_gives_windows (digits : ℕ → ℕ → ℕ)
    (allLow : ∀ k, TailBound (digits k) 10) :
    ∀ j, LowWindow digits j := by
  intro j k _
  exact allLow (j + k)

/-- Conditional assembly of the original 11-bound proof.

`classification` is deliberately an explicit *theoretical interface*, not
a finite `sorry`: it must follow from a concrete graph certificate PLUS
the proved transducer soundness, tail coverage, and CF equivalence lemmas.
`identity` similarly requires the primitive-minimal-polynomial scaling
theorem.  The arithmetic and moving-window deductions here are complete.

`D j` denotes the primitive discriminant of the middle layer `2^(j+15) α`.
-/
theorem lower_bound_eleven_of_window_classification
    (digits : ℕ → ℕ → ℕ) (D : ℕ → ℕ) (S : Finset ℕ)
    (classification : ∀ j, LowWindow digits j → D j ∈ S)
    {A : ℕ} (hA : 0 < A) (b c Δ : ℕ) (hΔ : 0 < Δ)
    (identity : ∀ j, scaledContent A b c j ^ 2 * D j = 4 ^ j * Δ) :
    ∃ k, RecurrentLarge (digits k) 11 := by
  by_contra h
  have allLow : ∀ k, TailBound (digits k) 10 := by
    intro k
    apply (not_recurrentLarge_iff_tailBound (digits k) 10).mp
    intro hk
    exact h ⟨k, hk⟩
  have membership : ∀ j, D j ∈ S := fun j =>
    classification j (all_low_gives_windows digits allLow j)
  exact discriminant_contradiction hA b c Δ D hΔ identity S membership

/-- General logical form of the 31-layer theorem.  If a low window puts
the middle layer in a finite exceptional set, and the invariant eventually
escapes that set, then every sufficiently late window contains a large
digit infinitely often at one fixed layer. -/
theorem eventual_every_31_layers
    (digits : ℕ → ℕ → ℕ) (D : ℕ → ℕ) (S : Finset ℕ)
    (classification : ∀ j, LowWindow digits j → D j ∈ S)
    (escape : ∃ J, ∀ j, J ≤ j → D j ∉ S) :
    ∃ J, ∀ j, J ≤ j →
      ∃ k, k ≤ 30 ∧ RecurrentLarge (digits (j + k)) 11 := by
  obtain ⟨J, hJ⟩ := escape
  refine ⟨J, ?_⟩
  intro j hj
  by_contra h
  apply hJ j hj
  apply classification j
  intro k hk
  apply (not_recurrentLarge_iff_tailBound (digits (j + k)) 10).mp
  intro large
  exact h ⟨k, hk, large⟩

/-- The quantitative moving-window corollary of the same arithmetic core.
The threshold is a coarse replacement for the logarithmic threshold in
the source, chosen to keep this proof entirely elementary. -/
theorem every_31_layers_of_discriminant_identity
    (digits : ℕ → ℕ → ℕ) (D : ℕ → ℕ) (S : Finset ℕ)
    (classification : ∀ j, LowWindow digits j → D j ∈ S)
    {A : ℕ} (hA : 0 < A) (b c Δ : ℕ) (hΔ : 0 < Δ)
    (identity : ∀ j, scaledContent A b c j ^ 2 * D j = 4 ^ j * Δ) :
    ∀ j, A ^ 2 * S.sup id ≤ j →
      ∃ k, k ≤ 30 ∧ RecurrentLarge (digits (j + k)) 11 := by
  intro j hj
  have hlarge := reduced_discriminants_eventually_above A Δ
    (scaledContent A b c) D hΔ (scaledContent_le hA b c) identity (S.sup id) j hj
  by_contra h
  have low : LowWindow digits j := by
    intro k hk
    apply (not_recurrentLarge_iff_tailBound (digits (j + k)) 10).mp
    intro large
    exact h ⟨k, hk, large⟩
  have := Finset.le_sup (f := id) (classification j low)
  exact (not_lt_of_ge this) hlarge

/-- The counting content of lower asymptotic density at least `1/31`.
The `t` disjoint blocks beginning at `J` contain at least `t` distinct
good layers. This avoids exchanging the layer and tail quantifiers. -/
theorem count_good_layers (P : ℕ → Prop) [DecidablePred P] (J : ℕ)
    (hit : ∀ j, J ≤ j → ∃ k, k ≤ 30 ∧ P (j + k)) (t : ℕ) :
    t ≤ ((Finset.range (J + 31 * t)).filter P).card := by
  classical
  have exists_hit (i : Fin t) : ∃ k, k ≤ 30 ∧ P (J + 31 * i.val + k) :=
    hit (J + 31 * i.val) (by omega)
  choose k hk using exists_hit
  let f : Fin t → ℕ := fun i => J + 31 * i.val + k i
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hi := (hk i).1
    have hj := (hk j).1
    dsimp [f] at hij
    omega
  have sub : Finset.univ.image f ⊆ (Finset.range (J + 31 * t)).filter P := by
    intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hi := i.isLt
      have hk' := (hk i).1
      dsimp [f]
      omega
    · exact (hk i).2
  have hcard := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard

end VV.Problem5
