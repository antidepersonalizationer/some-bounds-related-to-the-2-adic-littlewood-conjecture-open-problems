import VV.BBEKGaussChart
import VV.BBEKTopology
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
Actual finite conditional kernels in Gauss coordinates.  The covariance theorem
is proved from disintegration and its a.e. uniqueness; no rigidity hypothesis is used.
These are local probability kernels, not yet globally glued Radon leafwise measures.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafwiseKernel

section Transport
variable {B C U V : Type*} [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace U] [MeasurableSpace V]

/-- Change transverse coordinates by an isomorphism and leaf coordinates by a measurable map. -/
def transportKernel (f : B ≃ᵐ C) (g : U → V) (κ : Kernel B U) : Kernel C V :=
  (κ.map g).comap f.symm f.symm.measurable

instance transportKernel_sfinite (f : B ≃ᵐ C) (g : U → V) (κ : Kernel B U)
    [IsSFiniteKernel κ] : IsSFiniteKernel (transportKernel f g κ) := by
  unfold transportKernel
  infer_instance

instance transportKernel_finite (f : B ≃ᵐ C) (g : U → V) (κ : Kernel B U)
    [IsFiniteKernel κ] : IsFiniteKernel (transportKernel f g κ) := by
  unfold transportKernel
  infer_instance

theorem transportKernel_apply (f : B ≃ᵐ C) {g : U → V} (hg : Measurable g)
    (κ : Kernel B U) (b : B) : transportKernel f g κ (f b) = (κ b).map g := by
  simp only [transportKernel, Kernel.comap_apply, f.symm_apply_apply, Kernel.map_apply _ hg]

theorem fst_map_prod (ρ : Measure (B × U)) (f : B ≃ᵐ C)
    {g : U → V} (hg : Measurable g) :
    (ρ.map (Prod.map f g)).fst = ρ.fst.map f := by
  simp only [Measure.fst, Measure.map_map measurable_fst (f.measurable.prodMap hg),
    Measure.map_map f.measurable measurable_fst]
  rfl

/-- Explicit change of variables for the composition product of a measure and a kernel. -/
theorem compProd_transport (μ : Measure B) [SFinite μ] (κ : Kernel B U) [IsSFiniteKernel κ]
    (f : B ≃ᵐ C) {g : U → V} (hg : Measurable g) :
    (μ.map f) ⊗ₘ transportKernel f g κ = (μ ⊗ₘ κ).map (Prod.map f g) := by
  apply Measure.ext
  intro s hs
  rw [Measure.compProd_apply hs, f.measurableEmbedding.lintegral_map,
    Measure.map_apply (f.measurable.prodMap hg) hs,
    Measure.compProd_apply ((f.measurable.prodMap hg) hs)]
  apply lintegral_congr
  intro b
  rw [transportKernel_apply f hg, Measure.map_apply hg (measurable_prodMk_left hs)]
  rfl

variable [StandardBorelSpace U] [Nonempty U] [StandardBorelSpace V] [Nonempty V]

theorem condKernel_congr {ρ σ : Measure (B × U)} [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (h : ρ = σ) : ρ.condKernel = σ.condKernel := by
  subst σ
  rfl

/-- The transported kernel actually disintegrates the transported finite measure. -/
theorem disintegrate_transport (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    (f : B ≃ᵐ C) {g : U → V} (hg : Measurable g) :
    (ρ.map (Prod.map f g)).fst ⊗ₘ transportKernel f g ρ.condKernel =
      ρ.map (Prod.map f g) := by
  rw [fst_map_prod ρ f hg, compProd_transport _ _ f hg, Measure.disintegrate]

/-- Covariance of the actual canonical conditional kernels, with one common a.e. set
for the equality of measures (rather than a null set depending on a test set). -/
theorem condKernel_map_prod (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    (f : B ≃ᵐ C) {g : U → V} (hg : Measurable g) :
    ∀ᵐ b ∂ρ.fst, (ρ.map (Prod.map f g)).condKernel (f b) = (ρ.condKernel b).map g := by
  have hh := eq_condKernel_of_measure_eq_compProd (transportKernel f g ρ.condKernel)
    (disintegrate_transport ρ f hg).symm
  rw [fst_map_prod ρ f hg] at hh
  have hh' := ae_of_ae_map f.measurable.aemeasurable hh
  filter_upwards [hh'] with b hb
  exact hb.symm.trans (transportKernel_apply f hg ρ.condKernel b)

end Transport

open BBEKDynamics BBEKGaussChart BBEKTopology
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

instance q2MeasurableSpace : MeasurableSpace Q2 := borel Q2
instance q2BorelSpace : BorelSpace Q2 := ⟨rfl⟩
instance nonzeroRealBorelSpace : BorelSpace {a : ℝ // a ≠ 0} :=
  Subtype.borelSpace {a : ℝ | a ≠ 0}
instance nonzeroQ2BorelSpace : BorelSpace {a : Q2 // a ≠ 0} :=
  Subtype.borelSpace {a : Q2 | a ≠ 0}
instance nonzeroRealSecondCountable : SecondCountableTopology {a : ℝ // a ≠ 0} :=
  TopologicalSpace.Subtype.secondCountableTopology {a : ℝ | a ≠ 0}
instance nonzeroQ2SecondCountable : SecondCountableTopology {a : Q2 // a ≠ 0} :=
  TopologicalSpace.Subtype.secondCountableTopology {a : Q2 | a ≠ 0}

abbrev Leaf := ℝ × Q2
abbrev Transverse := ({a : ℝ // a ≠ 0} × ℝ) × ({a : Q2 // a ≠ 0} × Q2)

/-- The lower-unipotent coordinates are the leaf variables; the diagonal and upper
coordinates are the transverse variables. -/
def splitCoordinates : GroupParams ≃ₜ Transverse × Leaf where
  toFun p := ((p.1.2,p.2.2),(p.1.1,p.2.1))
  invFun q := ((q.2.1,q.1.1),(q.2.2,q.1.2))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def leafScaling (t : ℝ) (n : ℤ) : Leaf ≃ₜ Leaf :=
  (Homeomorph.smulOfNeZero (Real.exp (2*t)) (Real.exp_ne_zero _)).prodCongr
    (Homeomorph.smulOfNeZero ((2 : Q2)^(-2*n)) (zpow_ne_zero _ (by norm_num)))

def transverseScaling (t : ℝ) (n : ℤ) : Transverse ≃ₜ Transverse :=
  ((Homeomorph.refl _).prodCongr
    (Homeomorph.smulOfNeZero (Real.exp (-2*t)) (Real.exp_ne_zero _))).prodCongr
  ((Homeomorph.refl _).prodCongr
    (Homeomorph.smulOfNeZero ((2 : Q2)^(2*n)) (zpow_ne_zero _ (by norm_num))))

/-- The split-coordinate change is exactly the previously proved matrix conjugation formula. -/
theorem splitCoordinates_psiParams (t : ℝ) (n : ℤ) (p : GroupParams) :
    splitCoordinates (psiParams t n p) =
      Prod.map (transverseScaling t n) (leafScaling t n) (splitCoordinates p) := rfl

theorem measurable_psiParams (t : ℝ) (n : ℤ) : Measurable (psiParams t n) := by
  have he : psiParams t n = splitCoordinates.symm ∘
      (Prod.map (transverseScaling t n) (leafScaling t n)) ∘ splitCoordinates := rfl
  rw [he]
  exact splitCoordinates.symm.measurable.comp
    (((transverseScaling t n).measurable.prodMap (leafScaling t n).measurable).comp
      splitCoordinates.measurable)

def coordinateMeasure (μ : Measure GroupParams) : Measure (Transverse × Leaf) :=
  μ.map splitCoordinates

instance coordinateMeasure_finite (μ : Measure GroupParams) [IsFiniteMeasure μ] :
    IsFiniteMeasure (coordinateMeasure μ) := by unfold coordinateMeasure; infer_instance

/-- The actual canonical local conditional probability on the two lower-unipotent coordinates. -/
def leafKernel (μ : Measure GroupParams) [IsFiniteMeasure μ] : Kernel Transverse Leaf :=
  (coordinateMeasure μ).condKernel

theorem coordinateMeasure_scaling (μ : Measure GroupParams) (t : ℝ) (n : ℤ) :
    coordinateMeasure (μ.map (psiParams t n)) =
      (coordinateMeasure μ).map (Prod.map (transverseScaling t n) (leafScaling t n)) := by
  unfold coordinateMeasure
  rw [Measure.map_map splitCoordinates.measurable (measurable_psiParams t n),
    Measure.map_map ((transverseScaling t n).measurable.prodMap (leafScaling t n).measurable)
      splitCoordinates.measurable]
  rfl

/-- Concrete diagonal covariance of the local conditional kernels in actual Gauss coordinates. -/
theorem leafKernel_diagonal_covariance (μ : Measure GroupParams) [IsFiniteMeasure μ]
    (t : ℝ) (n : ℤ) :
    ∀ᵐ b ∂(coordinateMeasure μ).fst,
      leafKernel (μ.map (psiParams t n)) (transverseScaling t n b) =
        (leafKernel μ b).map (leafScaling t n) := by
  unfold leafKernel
  rw [condKernel_congr (coordinateMeasure_scaling μ t n)]
  exact condKernel_map_prod (coordinateMeasure μ)
    (transverseScaling t n).toMeasurableEquiv (leafScaling t n).measurable

/-- A fixed transverse coordinate parametrizes an actual lower-unipotent plaque. -/
theorem groupMatrix_leaf_add (b : Transverse) (u v : Leaf) :
    groupMatrixOf (splitCoordinates.symm (b, v + u)) =
      x v.1 v.2 * groupMatrixOf (splitCoordinates.symm (b, u)) := by
  apply Prod.ext
  · change lower (v.1 + u.1) * _ * _ = lower v.1 * (lower u.1 * _ * _)
    rw [lower_add]
    simp only [mul_assoc]
    rfl
  · change lower (v.2 + u.2) * _ * _ = lower v.2 * (lower u.2 * _ * _)
    rw [lower_add]
    simp only [mul_assoc]
    rfl

def plaquePoint (q : BBEKQuotient.X) (b : Transverse) (u : Leaf) : BBEKQuotient.X :=
  groupMatrixOf (splitCoordinates.symm (b,u)) • q

theorem plaquePoint_add (q : BBEKQuotient.X) (b : Transverse) (u v : Leaf) :
    plaquePoint q b (v+u) = x v.1 v.2 • plaquePoint q b u := by
  unfold plaquePoint
  rw [groupMatrix_leaf_add, mul_smul]

/-- This is the actual quotient action: the base point moves, the lower leaf scales,
and the transverse Gauss coordinates transform by the displayed diagonal factors. -/
theorem diagonal_plaquePoint (q : BBEKQuotient.X) (b : Transverse) (u : Leaf)
    (t : ℝ) (n : ℤ) :
    psi t n • plaquePoint q b u =
      plaquePoint (psi t n • q) (transverseScaling t n b) (leafScaling t n u) := by
  have hp : splitCoordinates.symm (transverseScaling t n b, leafScaling t n u) =
      psiParams t n (splitCoordinates.symm (b,u)) := rfl
  unfold plaquePoint
  rw [hp, ← psi_conjugate_coordinates]
  simp only [mul_smul, inv_smul_smul]

end VV.BBEKLeafwiseKernel
