import VV.BBEKLeafwiseOverlap
import Mathlib.Topology.Compactness.Lindelof

/-! An actual countable family of injective Gauss charts covering the arithmetic
quotient. This makes simultaneous almost-everywhere local leaf statements possible. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixGroups ENNReal ProbabilityTheory
namespace VV.BBEKLeafwiseAtlas
open BBEKDynamics BBEKGaussChart BBEKLeafwiseKernel BBEKLeafwiseChart BBEKQuotient

structure Chart where
  base : G
  domain : Set GroupParams
  isOpen_domain : IsOpen domain
  embedding : IsOpenEmbedding (domain.restrict (quotientCoordinates base))

def Chart.image (c : Chart) : Set X := quotientCoordinates c.base '' c.domain

theorem Chart.isOpen_image (c : Chart) : IsOpen c.image :=
  quotientCoordinates_isOpenMap c.base c.domain c.isOpen_domain

theorem exists_chart (q : X) : ∃ c : Chart, q ∈ c.image := by
  obtain ⟨g,hg⟩ := Quotient.exists_rep q
  change mk g = q at hg
  let p := groupCoordinates ⟨(1 : G),one_mem_domain,one_mem_domain⟩
  have hp : groupMatrixOf p = 1 :=
    congrArg Subtype.val (groupMatrix_coordinates ⟨1,one_mem_domain,one_mem_domain⟩)
  obtain ⟨V,hV,hpV,he⟩ := exists_open_quotientCoordinates g p
  refine ⟨⟨g,V,hV,he⟩,p,hpV,?_⟩
  change mk (groupMatrixOf p*g) = q
  rwa [hp,one_mul]

theorem exists_countable_atlas : ∃ c : ℕ → Chart, ⋃ n, (c n).image = univ := by
  letI : Nonempty X := ⟨mk 1⟩
  let C : X → Chart := fun q => (exists_chart q).choose
  have hC (q : X) : q ∈ (C q).image := (exists_chart q).choose_spec
  have hcov : (univ : Set X) ⊆ ⋃ q, (C q).image := by
    intro q _
    exact mem_iUnion.mpr ⟨q,hC q⟩
  obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
    (fun q => (C q).image) (fun q => (C q).isOpen_image) hcov
  exact ⟨C ∘ f,subset_antisymm (subset_univ _) hf⟩

def atlas : ℕ → Chart := exists_countable_atlas.choose

theorem atlas_covers : ⋃ n, (atlas n).image = univ := exists_countable_atlas.choose_spec

theorem point_in_atlas (q : X) : ∃ n, q ∈ (atlas n).image := by
  have hq : q ∈ ⋃ n, (atlas n).image := by rw [atlas_covers]; trivial
  exact mem_iUnion.mp hq

/-- Literal finite coordinate measures of the given quotient measure in every chart. -/
def chartMeasure (μ : Measure X) (n : ℕ) : Measure GroupParams :=
  localCoordinateMeasure μ (atlas n).base (atlas n).domain

instance chartMeasure_finite (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) :
    IsFiniteMeasure (chartMeasure μ n) :=
  localCoordinateMeasure_finite μ (atlas n).base (atlas n).isOpen_domain (atlas n).embedding

def chartKernel (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) : Kernel Transverse Leaf :=
  leafKernel (chartMeasure μ n)

theorem chartMeasure_reconstructs (μ : Measure X) (n : ℕ) :
    (chartMeasure μ n).map (quotientCoordinates (atlas n).base) =
      μ.restrict (atlas n).image :=
  map_localCoordinateMeasure μ (atlas n).base (atlas n).isOpen_domain (atlas n).embedding

theorem atlas_ae_iff (μ : Measure X) (P : X → Prop) :
    (∀ᵐ q ∂μ, P q) ↔ ∀ n, ∀ᵐ q ∂μ.restrict (atlas n).image, P q := by
  have hh := ae_restrict_iUnion_iff (μ := μ) (fun n : ℕ => (atlas n).image) P
  rwa [atlas_covers, Measure.restrict_univ] at hh

end VV.BBEKLeafwiseAtlas
