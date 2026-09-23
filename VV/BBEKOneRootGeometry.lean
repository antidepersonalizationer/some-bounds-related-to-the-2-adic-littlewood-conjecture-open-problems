import VV.BBEKOneRootLocal
import VV.BBEKActualKernelOverlap

/-! Arithmetic branch coordinates adapted to one actual root at a time.
The other complete Gauss factor is included in the transverse variable. -/
noncomputable section
open Set Matrix MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixGroups ENNReal ProbabilityTheory
namespace VV.BBEKOneRootGeometry
open BBEKDynamics BBEKGaussChart BBEKGaussTransition BBEKRootLeafKernel
  BBEKLeafwiseKernel BBEKLeafwiseOverlap BBEKChartMeasureOverlap

section OneFactor
variable {F : Type*} [NormedField F]

/-- The full Gauss change in the factor that is transverse to the chosen
root, including its lower parameter. -/
def fullRightHomeomorph (M : SL(2,F)) :
    rightDomain M × F ≃ₜ F × rightDomain M⁻¹ where
  toFun p := (p.2+rightLeafShift M p.1.val,rightTransverseHomeomorph M p.1)
  invFun p := ((rightTransverseHomeomorph M).symm p.2,
    p.1-rightLeafShift M ((rightTransverseHomeomorph M).symm p.2).val)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun :=
    (continuous_snd.add ((continuous_rightLeafShift M).comp continuous_fst)).prodMk
      ((rightTransverseHomeomorph M).continuous.comp continuous_fst)
  continuous_invFun :=
    ((rightTransverseHomeomorph M).symm.continuous.comp continuous_snd).prodMk
      (continuous_fst.sub ((continuous_rightLeafShift M).comp
        ((rightTransverseHomeomorph M).symm.continuous.comp continuous_snd)))

theorem fullRight_isOpenEmbedding (M : SL(2,F)) :
    IsOpenEmbedding (fun p : rightDomain M × F => rightParams M p.1 p.2) :=
  (IsOpenEmbedding.id.prodMap (isOpen_rightDomain M⁻¹).isOpenEmbedding_subtypeVal).comp
    (fullRightHomeomorph M).isOpenEmbedding

theorem fullSource_isOpenEmbedding (M : SL(2,F)) :
    IsOpenEmbedding (fun p : rightDomain M × F => (p.2,p.1.val)) :=
  (IsOpenEmbedding.id.prodMap (isOpen_rightDomain M).isOpenEmbedding_subtypeVal).comp
    (Homeomorph.prodComm _ _).isOpenEmbedding

theorem transverseRight_isOpenEmbedding (M : SL(2,F)) :
    IsOpenEmbedding (rightTransverse M) :=
  (isOpen_rightDomain M⁻¹).isOpenEmbedding_subtypeVal.comp
    (rightTransverseHomeomorph M).isOpenEmbedding
end OneFactor

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev RealBranchBase (g : G) := rightDomain g.1 × (rightDomain g.2 × Q2)
abbrev PadicBranchBase (g : G) := rightDomain g.2 × (rightDomain g.1 × ℝ)

def realBranchSplit (g : G) : GroupRightDomain g × Leaf ≃ₜ RealBranchBase g × ℝ where
  toFun p := ((p.1.1,(p.1.2,p.2.2)),p.2.1)
  invFun p := ((p.1.1,p.1.2.1),(p.2,p.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def padicBranchSplit (g : G) : GroupRightDomain g × Leaf ≃ₜ PadicBranchBase g × Q2 where
  toFun p := ((p.1.2,(p.1.1,p.2.1)),p.2.2)
  invFun p := ((p.1.2.1,p.1.1),(p.1.2.2,p.2))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def realBaseSource (g : G) (b : RealBranchBase g) : RealTransverse :=
  (b.1.val,(b.2.2,b.2.1.val))
def realBaseTarget (g : G) (b : RealBranchBase g) : RealTransverse :=
  (rightTransverse g.1 b.1,rightParams g.2 b.2.1 b.2.2)
def realBranchShift (g : G) (b : RealBranchBase g) : ℝ := rightLeafShift g.1 b.1.val

def padicBaseSource (g : G) (b : PadicBranchBase g) : PadicTransverse :=
  ((b.2.2,b.2.1.val),b.1.val)
def padicBaseTarget (g : G) (b : PadicBranchBase g) : PadicTransverse :=
  (rightParams g.1 b.2.1 b.2.2,rightTransverse g.2 b.1)
def padicBranchShift (g : G) (b : PadicBranchBase g) : Q2 := rightLeafShift g.2 b.1.val

theorem realBaseSource_embedding (g : G) : MeasurableEmbedding (realBaseSource g) :=
  ((isOpen_rightDomain g.1).isOpenEmbedding_subtypeVal.prodMap
    (fullSource_isOpenEmbedding g.2)).measurableEmbedding

theorem realBaseTarget_embedding (g : G) : MeasurableEmbedding (realBaseTarget g) :=
  ((transverseRight_isOpenEmbedding g.1).prodMap
    (fullRight_isOpenEmbedding g.2)).measurableEmbedding

theorem padicBaseSource_embedding (g : G) : MeasurableEmbedding (padicBaseSource g) :=
  (Homeomorph.prodComm _ _).measurableEmbedding.comp
    (((isOpen_rightDomain g.2).isOpenEmbedding_subtypeVal.prodMap
      (fullSource_isOpenEmbedding g.1)).measurableEmbedding)

theorem padicBaseTarget_embedding (g : G) : MeasurableEmbedding (padicBaseTarget g) :=
  (Homeomorph.prodComm _ _).measurableEmbedding.comp
    (((transverseRight_isOpenEmbedding g.2).prodMap
      (fullRight_isOpenEmbedding g.1)).measurableEmbedding)

theorem measurable_realBranchShift (g : G) : Measurable (realBranchShift g) :=
  ((continuous_rightLeafShift g.1).comp continuous_fst).measurable

theorem measurable_padicBranchShift (g : G) : Measurable (padicBranchShift g) :=
  ((continuous_rightLeafShift g.2).comp continuous_fst).measurable

def realTransition (g : G) (p : RealBranchBase g × ℝ) : RealTransverse × ℝ :=
  (realBaseTarget g p.1,p.2+realBranchShift g p.1)
def padicTransition (g : G) (p : PadicBranchBase g × Q2) : PadicTransverse × Q2 :=
  (padicBaseTarget g p.1,p.2+padicBranchShift g p.1)

theorem measurable_realTransition (g : G) : Measurable (realTransition g) :=
  ((realBaseTarget_embedding g).measurable.comp measurable_fst).prodMk
    (measurable_snd.add ((measurable_realBranchShift g).comp measurable_fst))

theorem measurable_padicTransition (g : G) : Measurable (padicTransition g) :=
  ((padicBaseTarget_embedding g).measurable.comp measurable_fst).prodMk
    (measurable_snd.add ((measurable_padicBranchShift g).comp measurable_fst))

theorem real_source_identity (g : G) (p : GroupRightDomain g × Leaf) :
    realSplit (sourceParams g p)=
      Prod.map (realBaseSource g) id (realBranchSplit g p) := rfl

theorem padic_source_identity (g : G) (p : GroupRightDomain g × Leaf) :
    padicSplit (sourceParams g p)=
      Prod.map (padicBaseSource g) id (padicBranchSplit g p) := rfl

theorem real_target_identity (g : G) (p : GroupRightDomain g × Leaf) :
    realSplit (targetParams g p)=realTransition g (realBranchSplit g p) := rfl

theorem padic_target_identity (g : G) (p : GroupRightDomain g × Leaf) :
    padicSplit (targetParams g p)=padicTransition g (padicBranchSplit g p) := rfl

/-- Actual one-root kernel transport in each arithmetic branch. -/
theorem condKernel_realTransition (g : G) (ρ : Measure (RealBranchBase g × ℝ))
    [IsFiniteMeasure ρ] :
    ∀ᵐ b ∂ρ.fst, (ρ.map (realTransition g)).condKernel (realBaseTarget g b)=
      (ρ.condKernel b).map (fun u => u+realBranchShift g b) :=
  condKernel_map_skew_embedding ρ (realBaseTarget_embedding g)
    (fun p => p.2+realBranchShift g p.1)
    (measurable_snd.add ((measurable_realBranchShift g).comp measurable_fst))

theorem condKernel_padicTransition (g : G) (ρ : Measure (PadicBranchBase g × Q2))
    [IsFiniteMeasure ρ] :
    ∀ᵐ b ∂ρ.fst, (ρ.map (padicTransition g)).condKernel (padicBaseTarget g b)=
      (ρ.condKernel b).map (fun u => u+padicBranchShift g b) :=
  condKernel_map_skew_embedding ρ (padicBaseTarget_embedding g)
    (fun p => p.2+padicBranchShift g p.1)
    (measurable_snd.add ((measurable_padicBranchShift g).comp measurable_fst))

end VV.BBEKOneRootGeometry

