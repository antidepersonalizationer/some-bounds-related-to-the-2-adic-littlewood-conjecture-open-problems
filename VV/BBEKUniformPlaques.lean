import VV.BBEKChartMeasureOverlap

/-! A compact set admits finitely many actual Gauss charts with a common
positive centered lower-root plaque radius. The safe chart is chosen from a
finite family; the assertion concerns the plaque, not only quotient injectivity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped Topology ENNReal
namespace VV.BBEKUniformPlaques
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas

def leafShift (p : GroupParams) (u : Leaf) : GroupParams :=
  splitCoordinates.symm ((splitCoordinates p).1, u + (splitCoordinates p).2)

@[simp] theorem leafShift_zero (p : GroupParams) : leafShift p 0 = p := by
  simp [leafShift]

theorem continuous_leafShift : Continuous (fun z : GroupParams × Leaf => leafShift z.1 z.2) := by
  unfold leafShift
  fun_prop

theorem quotient_leafShift (g : G) (p : GroupParams) (u : Leaf) :
    quotientCoordinates g (leafShift p u) = x u.1 u.2 • quotientCoordinates g p := by
  conv_rhs => rw [← splitCoordinates.symm_apply_apply p]
  exact plaquePoint_add (mk g) (splitCoordinates p).1 (splitCoordinates p).2 u

theorem exists_safe_chart_near (q : X) :
    ∃ c : Chart, ∃ V : Set X, ∃ W : Set Leaf,
      IsOpen V ∧ q ∈ V ∧ IsOpen W ∧ (0 : Leaf) ∈ W ∧
      ∀ z ∈ V, ∃ p : GroupParams, quotientCoordinates c.base p = z ∧
        ∀ u ∈ W, leafShift p u ∈ c.domain := by
  obtain ⟨c,p,hp,hpq⟩ := exists_chart q
  have hopen : IsOpen {z : GroupParams × Leaf | leafShift z.1 z.2 ∈ c.domain} :=
    c.isOpen_domain.preimage continuous_leafShift
  have hzero : (p,(0 : Leaf)) ∈ {z : GroupParams × Leaf | leafShift z.1 z.2 ∈ c.domain} := by
    simpa only [mem_setOf_eq,leafShift_zero] using hp
  obtain ⟨P,W,hP,hW,hpP,h0W,hPW⟩ := isOpen_prod_iff.mp hopen p 0 hzero
  refine ⟨c,quotientCoordinates c.base '' P,W,
    quotientCoordinates_isOpenMap c.base P hP,⟨p,hpP,hpq⟩,hW,h0W,?_⟩
  rintro z ⟨p,hpP,rfl⟩
  exact ⟨p,rfl,fun u hu => hPW (show (p,u) ∈ P ×ˢ W from ⟨hpP,hu⟩)⟩

theorem compact_uniform_safe_plaques {K : Set X} (hK : IsCompact K) :
    ∃ C : Finset Chart, ∃ ε : ℝ, 0 < ε ∧
      ∀ q ∈ K, ∃ c ∈ C, ∃ p : GroupParams,
        quotientCoordinates c.base p = q ∧
          ∀ u : Leaf, ‖u‖ < ε → leafShift p u ∈ c.domain := by
  classical
  choose c V W hV hq hW h0 hsafe using exists_safe_chart_near
  have hcover : K ⊆ ⋃ q : X, V q := fun q _ => mem_iUnion.mpr ⟨q,hq q⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hV hcover
  let U : Set Leaf := ⋂ q ∈ s, W q
  have hU : IsOpen U := isOpen_biInter_finset (fun q _ => hW q)
  have h0U : (0 : Leaf) ∈ U := by
    simp only [U,mem_iInter]
    exact fun q _ => h0 q
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  refine ⟨s.image c,ε,hε,?_⟩
  intro q hqK
  obtain ⟨z,hzs,hqV⟩ := mem_iUnion₂.mp (hs hqK)
  obtain ⟨p,hpq,hp⟩ := hsafe z q hqV
  refine ⟨c z,Finset.mem_image.mpr ⟨z,hzs,rfl⟩,p,hpq,?_⟩
  intro u hu
  have huU : u ∈ U := hεU (by simpa only [mem_ball,dist_zero_right] using hu)
  exact hp u (mem_iInter.mp (mem_iInter.mp huU z) hzs)

/-- Actual measurable coordinates on each chart, extended arbitrarily outside
its image. The extension is constructed, not postulated. -/
theorem exists_measurable_chartCoordinates (c : Chart) :
    ∃ f : X → GroupParams, Measurable f ∧
      ∀ p : c.domain, f (quotientCoordinates c.base p.val) = p.val := by
  haveI : Nonempty GroupParams := ⟨((0,(⟨1,one_ne_zero⟩,0)),(0,(⟨1,one_ne_zero⟩,0)))⟩
  obtain ⟨f,hf,hfe⟩ := c.embedding.measurableEmbedding.exists_measurable_extend
    (measurable_subtype_coe : Measurable (fun p : c.domain => p.val)) (fun _ => inferInstance)
  exact ⟨f,hf,fun p => congrFun hfe p⟩

def chartCoordinates (c : Chart) : X → GroupParams := (exists_measurable_chartCoordinates c).choose

theorem measurable_chartCoordinates (c : Chart) : Measurable (chartCoordinates c) :=
  (exists_measurable_chartCoordinates c).choose_spec.1

theorem chartCoordinates_apply (c : Chart) (p : c.domain) :
    chartCoordinates c (quotientCoordinates c.base p.val) = p.val :=
  (exists_measurable_chartCoordinates c).choose_spec.2 p

end VV.BBEKUniformPlaques
