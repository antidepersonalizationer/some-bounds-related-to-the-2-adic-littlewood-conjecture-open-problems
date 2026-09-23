import VV.BBEKProjectiveGlue
import VV.BBEKSelectedPlaques

/-! Explicit measurable countable gluing on expanding root balls. -/
noncomputable section
open Set MeasureTheory Filter Metric Topology
open scoped ENNReal
namespace VV.BBEKGrowingGlue
open BBEKDynamics BBEKLeafwiseKernel BBEKMeasureGlue BBEKProjectiveGlue

def growingBall (r : ℝ) (n : ℕ) : Set Leaf := ball 0 ((4 : ℝ)^n*r)

theorem growingBall_open (r : ℝ) (n : ℕ) : IsOpen (growingBall r n) := isOpen_ball

theorem growingBall_cover {r : ℝ} (hr : 0 < r) : ⋃ n, growingBall r n = univ := by
  apply eq_univ_of_forall
  intro u
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (‖u‖/r) (by norm_num : (1 : ℝ) < 4)
  apply mem_iUnion.mpr
  refine ⟨n,?_⟩
  change dist u 0 < (4 : ℝ)^n*r
  rw [dist_zero_right]
  exact (div_lt_iff₀ hr).mp hn

theorem growingBall_mono {r : ℝ} (hr : 0 ≤ r) : Monotone (growingBall r) := by
  intro n m hnm
  apply ball_subset_ball
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hnm) hr

theorem growingBall_inter {r : ℝ} (hr : 0 ≤ r) (n m : ℕ) :
    growingBall r n ∩ growingBall r m = growingBall r (min n m) := by
  rcases le_total n m with h | h
  · rw [min_eq_left h,inter_eq_self_of_subset_left (growingBall_mono hr h)]
  · rw [min_eq_right h,inter_eq_self_of_subset_right (growingBall_mono hr h)]

/-- The explicit candidate uses disjoint annuli, and is measurable even before
the compatibility identities have been proved on a conull set. -/
def normalizedGlue {Z : Type*} (r : ℝ) (η : ℕ → Z → Measure Leaf) (z : Z) : Measure Leaf :=
  glue (growingBall r) (fun n => BBEKProjectiveGlue.normalize (η n z) (ball 0 r))

theorem measurable_normalizedGlue {Z : Type*} [MeasurableSpace Z]
    (r : ℝ) (η : ℕ → Z → Measure Leaf) (hη : ∀ n, Measurable (η n)) :
    Measurable (normalizedGlue r η) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [normalizedGlue,glue,Measure.sum_apply _ hE,
    Measure.restrict_apply hE,BBEKProjectiveGlue.normalize,Measure.smul_apply,smul_eq_mul]
  apply Measurable.ennreal_tsum
  intro n
  exact ((Measure.measurable_coe isOpen_ball.measurableSet).comp (hη n)).inv.mul
    ((Measure.measurable_coe (hE.inter (MeasurableSet.disjointed
      (fun k => (growingBall_open r k).measurableSet) n))).comp (hη n))

/-- The explicit sum, rather than an unspecified extension, is Radon and
normalized once the already-derived projective identities are supplied. -/
theorem normalizedGlue_properties {Z : Type*} {r : ℝ} (hr : 0 < r)
    (η : ℕ → Z → Measure Leaf) [∀ n z, IsFiniteMeasure (η n z)] (z : Z)
    (hpos : ∀ n, 0 < η n z (ball 0 r))
    (hprojective : ∀ n m, ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
      (η n z).restrict (growingBall r n ∩ growingBall r m) =
        a • (η m z).restrict (growingBall r n ∩ growingBall r m)) :
    IsLocallyFiniteMeasure (normalizedGlue r η z) ∧ (normalizedGlue r η z).Regular ∧
      normalizedGlue r η z (ball 0 r) = 1 ∧
      ∀ n, (normalizedGlue r η z).restrict (growingBall r n) =
        (η n z (ball 0 r))⁻¹ • (η n z).restrict (growingBall r n) := by
  let θ : ℕ → Measure Leaf := fun n => BBEKProjectiveGlue.normalize (η n z) (ball 0 r)
  letI : ∀ n, IsFiniteMeasure (θ n) := fun n => normalize_finite _ _ (hpos n)
  have hbase (n : ℕ) : ball (0 : Leaf) r ⊆ growingBall r n := by
    simpa only [growingBall,pow_zero,one_mul] using
      growingBall_mono hr.le (Nat.zero_le n)
  have hagree (n m : ℕ) : (θ n).restrict (growingBall r n ∩ growingBall r m) =
      (θ m).restrict (growingBall r n ∩ growingBall r m) := by
    obtain ⟨a,ha,haf,he⟩ := hprojective n m
    exact normalize_restrict_of_projective _ _ isOpen_ball.measurableSet
      (fun _ hu => ⟨hbase n hu,hbase m hu⟩) ha haf he
  have hres (n : ℕ) : (normalizedGlue r η z).restrict (growingBall r n) =
      (θ n).restrict (growingBall r n) :=
    glue_restrict _ (fun n => (growingBall_open r n).measurableSet)
      (growingBall_cover hr) θ hagree n
  refine ⟨glue_locallyFinite _ (growingBall_open r) (growingBall_cover hr) θ hagree,
    glue_regular _ (growingBall_open r) (growingBall_cover hr) θ hagree,?_,?_⟩
  · have hh := congrArg (fun m : Measure Leaf => m (ball 0 r)) (hres 0)
    simp only [Measure.restrict_apply isOpen_ball.measurableSet,
      inter_eq_self_of_subset_left (hbase 0)] at hh
    exact hh.trans (normalize_apply _ _ (hpos 0))
  · intro n
    exact (hres n).trans (Measure.restrict_smul _ _ _)

end VV.BBEKGrowingGlue


