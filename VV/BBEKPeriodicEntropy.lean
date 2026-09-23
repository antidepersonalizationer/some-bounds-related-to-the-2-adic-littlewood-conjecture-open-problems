import VV.BBEKPeriodicOrbit
import VV.Entropy.BowenGenerator

noncomputable section
open Set Metric MeasureTheory
open scoped Topology MatrixGroups
namespace VV.BBEKPeriodicOrbit
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKGaussChart
open ErgodicTheory.Entropy

section Abelian
variable {H Z : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SigmaCompactSpace H] [MetricSpace Z] [CompactSpace Z] [Nonempty Z]
  [MulAction H Z] [ContinuousSMul H Z] [MulAction.IsPretransitive H Z]
  [MeasurableSpace Z] [BorelSpace Z]

def oneCellPartition : FixedPartition Z (Fin 1) where
  cells _ := univ
  measurable _ := MeasurableSet.univ
  disjoint := by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _))
  cover := by
    ext z
    simp only [mem_iUnion,mem_univ,iff_true]
    exact ⟨0,trivial⟩

/-- Every measure-preserving translation on an actual compact transitive
abelian homogeneous space has zero Kolmogorov--Sinai entropy. -/
theorem ksEntropy_smul_eq_zero (a : H) (μ : Measure Z) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (fun z : Z => a • z) μ μ) : ksEntropy hT = 0 := by
  obtain ⟨R,hR⟩ := Metric.isBounded_iff.mp (isCompact_univ : IsCompact (univ : Set Z)).isBounded
  let P := oneCellPartition (Z:=Z)
  have he := ksEntropy_eq_of_uniformBowenCover hT P (uniformBowenCover_smul a (R+1))
    (fun i x _ y _ => (hR (mem_univ x) (mem_univ y)).trans_lt (by linarith))
  have hz : entropy μ (P.toMeasurePartition μ).cells = 0 := by
    simp [P,oneCellPartition,FixedPartition.toMeasurePartition,entropy]
  have hpart : ksEntropyPartition hT (P.toMeasurePartition μ) = 0 :=
    le_antisymm (hz ▸ ksEntropyPartition_le_entropy hT (P.toMeasurePartition μ))
      (ksEntropyPartition_nonneg hT _)
  simpa only [hpart,EReal.coe_zero] using he

end Abelian

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

instance A_commGroup : CommGroup A :=
  { inferInstanceAs (Group A) with
    mul_comm := fun a b => Subtype.ext (A_commute a.property b.property).eq }

theorem diagonalGroup_isClosed {F : Type*} [NormedField F] :
    IsClosed (diagonalGroup F : Set SL(2,F)) := by
  have hentry (i j : Fin 2) : Continuous (fun M : SL(2,F) => M i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  have he : (diagonalGroup F : Set SL(2,F)) =
      {M | M 0 1=0} ∩ {M | M 1 0=0} := by
    ext M
    exact mem_diagonalGroup_iff M
  rw [he]
  exact (isClosed_eq (hentry 0 1) continuous_const).inter (isClosed_eq (hentry 1 0) continuous_const)

theorem A_isClosed : IsClosed (A : Set G) :=
  diagonalGroup_isClosed.prod diagonalGroup_isClosed

instance A_properSpace : ProperSpace A := ProperSpace.of_isClosed A_isClosed

instance orbit_continuousSMul (q : X) : ContinuousSMul A (MulAction.orbit A q) where
  continuous_smul :=
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The literal time map on a diagonal orbit in G/Gamma. -/
def orbitTimeMap (q : X) (t : ℝ) (n : ℤ) : MulAction.orbit A q → MulAction.orbit A q :=
  fun y => (⟨psi t n,psi_mem_A t n⟩ : A) • y

@[simp] theorem orbitTimeMap_coe (q : X) (t : ℝ) (n : ℤ) (y : MulAction.orbit A q) :
    (orbitTimeMap q t n y : X) = psi t n • (y : X) := rfl

/-- The actual compact diagonal-orbit branch of BBEK's entropy exclusion.
Compactness is asserted of the literal orbit, not of an abstract model. -/
theorem compact_A_orbit_ksEntropy_zero (q : X) (hq : IsCompact (MulAction.orbit A q))
    (t : ℝ) (n : ℤ) (μ : Measure (MulAction.orbit A q)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (orbitTimeMap q t n) μ μ) : ksEntropy hT = 0 := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace (MulAction.orbit A q) := isCompact_iff_compactSpace.mp hq
  letI : Nonempty (MulAction.orbit A q) := ⟨⟨q,MulAction.mem_orbit_self q⟩⟩
  exact ksEntropy_smul_eq_zero (⟨psi t n,psi_mem_A t n⟩ : A) μ hT

end VV.BBEKPeriodicOrbit

