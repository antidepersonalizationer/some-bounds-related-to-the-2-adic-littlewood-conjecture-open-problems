import VV.BBEKParameter
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
Discreteness of the actual diagonal dyadic subgroup and of the arithmetic
subgroup Gamma in SL₂(R) × SL₂(Q₂). The diagonal dyadic range has the subspace
topology from R × Q₂; this is not the topology inherited from Q alone.

The argument is elementary: a dyadic number which is 2-adically integral is
an ordinary integer, and an integer of real absolute value less than one is
zero. Applying this to every matrix entry isolates the identity in Gamma.
No finite-covolume or Mahler compactness result is asserted here.
-/

noncomputable section
open Matrix Metric Set
open scoped MatrixGroups Topology

namespace VV.BBEKDiscrete
open BBEKDyadic BBEKDynamics BBEKQuotient

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem dyadic_eq_zero_of_small {q : ℚ} (hq : q ∈ dyadic)
    (hreal : |(q : ℝ)| < 1) (hpadic : ‖(q : Q2)‖ ≤ 1) : q = 0 := by
  obtain ⟨m, rfl⟩ := dyadic_integral_of_norm_le_one hq hpadic
  have hm : |m| < (1 : ℤ) := by exact_mod_cast hreal
  have hz : m = 0 := by
    obtain ⟨_, _⟩ := abs_lt.mp hm
    omega
  simp [hz]

theorem one_le_abs_of_nonzero_dyadic {q : ℚ} (hq : q ∈ dyadic) (hne : q ≠ 0)
    (hpadic : ‖(q : Q2)‖ ≤ 1) : 1 ≤ |(q : ℝ)| := by
  exact le_of_not_gt fun hreal => hne (dyadic_eq_zero_of_small hq hreal hpadic)

theorem dyadic_subtype_eq_zero_of_small (q : dyadic)
    (hreal : |dyadicToReal q| < 1) (hpadic : ‖dyadicToQ2 q‖ ≤ 1) : q = 0 := by
  apply Subtype.ext
  exact dyadic_eq_zero_of_small q.property hreal hpadic

def diagonalAddEmbedding : dyadic →+ ℝ × Q2 :=
  dyadicToReal.toAddMonoidHom.prod dyadicToQ2.toAddMonoidHom

def Delta : AddSubgroup (ℝ × Q2) := diagonalAddEmbedding.range

theorem delta_eq_zero_of_dist_lt_one {z : ℝ × Q2} (hz : z ∈ Delta)
    (hdist : dist z 0 < 1) : z = 0 := by
  obtain ⟨q, rfl⟩ := hz
  have hd : max |dyadicToReal q| ‖dyadicToQ2 q‖ < 1 := by
    simpa only [diagonalAddEmbedding, AddMonoidHom.prod_apply, AddMonoidHom.coe_coe,
      Prod.dist_eq, Prod.fst_zero, Prod.snd_zero, dist_zero_right, Real.norm_eq_abs] using hdist
  have hq : q = 0 := dyadic_subtype_eq_zero_of_small q
    ((le_max_left _ _).trans_lt hd) ((le_max_right _ _).trans_lt hd).le
  simp [hq]

theorem delta_inter_ball_zero : (Delta : Set (ℝ × Q2)) ∩ ball 0 1 = {0} := by
  ext z
  constructor
  · intro hz
    exact delta_eq_zero_of_dist_lt_one hz.1 hz.2
  · intro hz
    subst z
    exact ⟨Delta.zero_mem, by simp⟩

theorem isOpen_singleton_zero_delta : IsOpen ({0} : Set Delta) := by
  have he : ((↑) : Delta → ℝ × Q2) ⁻¹' ball 0 1 = {0} := by
    ext z
    constructor
    · intro hz
      apply Subtype.ext
      exact delta_eq_zero_of_dist_lt_one z.property hz
    · intro hz
      subst z
      simp
  rw [← he]
  exact isOpen_ball.preimage continuous_subtype_val

instance delta_discreteTopology : DiscreteTopology Delta :=
  discreteTopology_of_isOpen_singleton_zero isOpen_singleton_zero_delta

theorem delta_isClosed : IsClosed (Delta : Set (ℝ × Q2)) :=
  AddSubgroup.isClosed_of_discrete

theorem sl_entry_dist_le {K : Type*} [CommRing K] [MetricSpace K]
    (A B : SL(2, K)) (i j : Fin 2) : dist (A i j) (B i j) ≤ dist A B := by
  exact (dist_le_pi_dist (A i) (B i) j).trans
    (dist_le_pi_dist (A : Matrix (Fin 2) (Fin 2) K) B i)

theorem gamma_eq_one_of_dist_lt_one {g : G} (hg : g ∈ Gamma)
    (hdist : dist g 1 < 1) : g = 1 := by
  obtain ⟨A, rfl⟩ := hg
  have hdR : dist (SpecialLinearGroup.map dyadicToReal A) 1 < 1 :=
    (le_max_left _ _).trans_lt hdist
  have hdP : dist (SpecialLinearGroup.map dyadicToQ2 A) 1 < 1 :=
    (le_max_right _ _).trans_lt hdist
  have hA : A = 1 := by
    apply SpecialLinearGroup.ext
    intro i j
    have hRone : dyadicToReal ((1 : SL(2, dyadic)) i j) = (1 : SL(2, ℝ)) i j :=
      congrArg (fun M : SL(2, ℝ) => M i j) (map_one (SpecialLinearGroup.map dyadicToReal))
    have hPone : dyadicToQ2 ((1 : SL(2, dyadic)) i j) = (1 : SL(2, Q2)) i j :=
      congrArg (fun M : SL(2, Q2) => M i j) (map_one (SpecialLinearGroup.map dyadicToQ2))
    apply sub_eq_zero.mp
    apply dyadic_subtype_eq_zero_of_small
    · rw [map_sub, hRone, ← Real.dist_eq]
      exact (sl_entry_dist_le (SpecialLinearGroup.map dyadicToReal A) 1 i j).trans_lt hdR
    · rw [map_sub, hPone, ← dist_eq_norm]
      exact ((sl_entry_dist_le (SpecialLinearGroup.map dyadicToQ2 A) 1 i j).trans_lt hdP).le
  simp [hA]

/-- An explicit ambient open neighborhood which isolates the identity. -/
theorem gamma_inter_ball_one : (Gamma : Set G) ∩ ball 1 1 = {1} := by
  ext g
  constructor
  · intro hg
    exact gamma_eq_one_of_dist_lt_one hg.1 hg.2
  · intro hg
    subst g
    exact ⟨Gamma.one_mem, by simp⟩

theorem isOpen_singleton_one_gamma : IsOpen ({1} : Set Gamma) := by
  have he : ((↑) : Gamma → G) ⁻¹' ball 1 1 = {1} := by
    ext g
    constructor
    · intro hg
      apply Subtype.ext
      exact gamma_eq_one_of_dist_lt_one g.property hg
    · intro hg
      subst g
      simp
  rw [← he]
  exact isOpen_ball.preimage continuous_subtype_val

instance gamma_discreteTopology : DiscreteTopology Gamma :=
  discreteTopology_of_isOpen_singleton_one isOpen_singleton_one_gamma

theorem gamma_isClosed : IsClosed (Gamma : Set G) :=
  Subgroup.isClosed_of_discrete

/-- Closed determinant-one matrices inherit local compactness from the
finite-dimensional matrix space. -/
instance sl2_locallyCompactSpace {K : Type*} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [LocallyCompactSpace K] :
    LocallyCompactSpace SL(2, K) := by
  letI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → K))
  have hclosed : IsClosed {M : Matrix (Fin 2) (Fin 2) K | M.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  exact hclosed.locallyCompactSpace

instance group_locallyCompactSpace : LocallyCompactSpace G := inferInstance

/-- The right Gamma action is properly discontinuous; this is the action
whose orbit relation defines the left-coset space G/Gamma. -/
instance gamma_properlyDiscontinuousSMul : ProperlyDiscontinuousSMul Gamma.op G :=
  Gamma.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite
    (Gamma.tendsto_coe_cofinite_of_discrete)

instance quotient_t2Space : T2Space X :=
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel Gamma.op G)))

instance quotient_locallyCompactSpace : LocallyCompactSpace X :=
  inferInstanceAs (LocallyCompactSpace (G ⧸ Gamma))

end VV.BBEKDiscrete
