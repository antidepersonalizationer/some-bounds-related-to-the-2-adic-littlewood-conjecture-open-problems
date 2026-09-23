import VV.BBEKFuturePlaques
import VV.BBEKMautner
import VV.Entropy.SmallPositivePartition

/-! Opposite-time future conditionals are supported on actual lower
center-stable plaques.  The transpose comparison proves the opposite
matrix constraint from the literal inverse group dynamics. -/

noncomputable section
open Set Metric MeasureTheory ProbabilityTheory Function Matrix
open scoped Topology Uniformity ENNReal MatrixGroups

namespace VV.BBEKInverseFuturePlaques
open BBEKDynamics BBEKQuotient BBEKTopology BBEKStandardBorel
open BBEKEntropyExpansive BBEKBowenLift BBEKMautner ErgodicTheory.Entropy
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem transposeG_dist_one_le (g : G) : dist (transposeG g) 1 ≤ dist g 1 := by
  rw [Prod.dist_eq]
  apply max_le
  · change dist (g.1.transpose : Matrix (Fin 2) (Fin 2) ℝ) 1 ≤ dist g 1
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro j
    have he := entry_dist_le g.1 1 j i
    have hp : dist g.1 (1 : G).1 ≤ dist g 1 := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    simpa only [SpecialLinearGroup.coe_transpose,Matrix.transpose_apply,
      SpecialLinearGroup.coe_one,Matrix.one_apply,eq_comm] using he.trans hp
  · change dist (g.2.transpose : Matrix (Fin 2) (Fin 2) Q2) 1 ≤ dist g 1
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro j
    have he := entry_dist_le g.2 1 j i
    have hp : dist g.2 (1 : G).2 ≤ dist g 1 := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    simpa only [SpecialLinearGroup.coe_transpose,Matrix.transpose_apply,
      SpecialLinearGroup.coe_one,Matrix.one_apply,eq_comm] using he.trans hp

theorem upper_zero_of_inverse_bounded {t : ℝ} (ht : 0 < t) (g : G) (R : ℝ)
    (hbnd : ∀ n : ℕ, dist ((psi t 1)⁻¹^n*g*(psi t 1)^n) 1 ≤ R) :
    g.1 0 1 = 0 ∧ g.2 0 1 = 0 := by
  have hb (n : ℕ) : dist (forwardConjugate t n (transposeG g)) 1 ≤ R := by
    have he : forwardConjugate t n (transposeG g) =
        transposeG ((psi t 1)⁻¹^n*g*(psi t 1)^n) := by
      simp only [forwardConjugate,transposeG_mul,transposeG_pow,
        transposeG_psi,transposeG_psi_inv,mul_assoc]
    rw [he]
    exact (transposeG_dist_one_le _).trans (hbnd n)
  exact lower_zero_of_forward_bounded ht (transposeG g) R hb

def restrictedInverseTime {Y : Set X} {t : ℝ}
    (hf : MapsTo (fun q : X => (psi t 1)⁻¹ • q) Y Y) : Y → Y :=
  fun q => ⟨(psi t 1)⁻¹ • q,hf q.property⟩

theorem restrictedInverseTime_iterate_pow {Y : Set X} {t : ℝ}
    (hf : MapsTo (fun q : X => (psi t 1)⁻¹ • q) Y Y) (q : Y) (n : ℕ) :
    ((restrictedInverseTime hf)^[n] q : X) = ((psi t 1)⁻¹)^n • (q : X) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (psi t 1)⁻¹ • ((restrictedInverseTime hf)^[n] q : X) = _
    rw [ih,← MulAction.mul_smul,← pow_succ']

theorem compact_small_inverse_future_same_plaque {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : 0 < t) (hf : MapsTo (fun q : X => (psi t 1)⁻¹ • q) Y Y) :
    letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x y : Y,
      (∀ n : ℕ, dist ((restrictedInverseTime hf)^[n+1] x)
        ((restrictedInverseTime hf)^[n+1] y) < ρ) →
      ∃ g : G, g.1 0 1 = 0 ∧ g.2 0 1 = 0 ∧
        (restrictedInverseTime hf y : X) = g • (restrictedInverseTime hf x : X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  obtain ⟨r,hr,ho,hd,hlift⟩ := compact_forward_lift hY (psi t 1)⁻¹
  let V : Set (Y × Y) := (fun p : Y × Y => ((p.1 : X),(p.2 : X))) ⁻¹' displacementRelation r
  have hV : IsOpen V := ho.preimage (continuous_subtype_val.prodMap continuous_subtype_val)
  have hu : V ∈ 𝓤 Y := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    apply hV.mem_nhdsSet.mpr
    rintro ⟨a,b⟩ (hab : a=b)
    subst b
    exact hd a
  obtain ⟨ρ,hρ,hρV⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨ρ,hρ,?_⟩
  intro x y hxy
  have he (z : Y) (n : ℕ) :
      (psi t 1)⁻¹^n • (restrictedInverseTime hf z : X) =
        ((restrictedInverseTime hf)^[n+1] z : X) := by
    rw [← restrictedInverseTime_iterate_pow hf (restrictedInverseTime hf z) n,
      Function.iterate_succ_apply]
  obtain ⟨g,hg,hgn⟩ := hlift (restrictedInverseTime hf x) (restrictedInverseTime hf y)
    (fun n => by rw [he]; exact ((restrictedInverseTime hf)^[n+1] x).property)
    (fun n => by simpa only [he] using hρV (hxy n))
  have hzero := upper_zero_of_inverse_bounded ht g r
    (fun n => by simpa only [inv_inv] using (hgn n).1.le)
  exact ⟨g,hzero.1,hzero.2,by simpa using (hgn 0).2⟩

theorem positive_inverse_futureKernel_on_actual_plaques {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : 0 < t) (hf : MapsTo (fun q : X => (psi t 1)⁻¹ • q) Y Y)
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (restrictedInverseTime hf) μ μ) (hpos : 0 < ksEntropy hT) :
    letI : StandardBorelSpace Y := hY.measurableSet.standardBorel
    ∃ m : ℕ, ∃ P : MeasurePartition μ (Fin m),
      0 < condEntropy μ (entireFutureSigma hT P) P.cells ∧
      ¬ (∀ᵐ x ∂μ, ∃ y, condExpKernel μ (entireFutureSigma hT P) x = Measure.dirac y) ∧
      ∀ᵐ x ∂μ, ∀ᵐ y ∂condExpKernel μ (entireFutureSigma hT P) x,
        ∃ g : G, g.1 0 1 = 0 ∧ g.2 0 1 = 0 ∧
          (restrictedInverseTime hf y : X) = g • (restrictedInverseTime hf x : X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  letI : StandardBorelSpace Y := hY.measurableSet.standardBorel
  obtain ⟨ρ,hρ,hplaque⟩ := compact_small_inverse_future_same_plaque hY ht hf
  obtain ⟨m,P,hp,hmesh⟩ := exists_pos_small_partition hT hpos hρ
  have hm : m ≠ 0 := by
    intro he
    subst m
    have hc := congrArg μ P.cover
    have hz : (0 : ℝ≥0∞) = 1 := by
      simpa only [iUnion_of_empty,measure_empty,measure_univ] using hc
    exact zero_ne_one hz
  letI : NeZero m := ⟨hm⟩
  have hc : 0 < condEntropy μ (entireFutureSigma hT P) P.cells := by
    rwa [← ksEntropyPartition_eq_condEntropy_entireFuture hT P]
  refine ⟨m,P,hc,not_ae_dirac_of_pos_condEntropy μ _ P.cells hc,?_⟩
  filter_upwards [futureKernel_ae_same_cell hT P] with x hx
  filter_upwards [hx] with y hy
  apply hplaque x y
  intro n
  obtain ⟨i,hix,hiy⟩ := hy n
  exact hmesh i _ hix _ hiy

end VV.BBEKInverseFuturePlaques
