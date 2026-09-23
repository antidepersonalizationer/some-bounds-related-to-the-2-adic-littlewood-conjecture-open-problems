import VV.BBEKUniformPlaques

/-! Borel selection of actual uniformly safe leaf charts over a compact set. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped Topology ENNReal
namespace VV.BBEKPlaqueSelection
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques

def safeParameters (c : Chart) (r : ℝ) : Set GroupParams :=
  {p | ∀ u ∈ closedBall (0 : Leaf) r, leafShift p u ∈ c.domain}
def safeImage (c : Chart) (r : ℝ) : Set X :=
  quotientCoordinates c.base '' safeParameters c r

theorem isOpen_safeParameters (c : Chart) (r : ℝ) : IsOpen (safeParameters c r) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have ho : IsOpen {z : GroupParams × Leaf | leafShift z.1 z.2 ∈ c.domain} :=
    c.isOpen_domain.preimage continuous_leafShift
  have hs : ({p} : Set GroupParams) ×ˢ closedBall (0 : Leaf) r ⊆
      {z : GroupParams × Leaf | leafShift z.1 z.2 ∈ c.domain} := by
    rintro ⟨q,u⟩ ⟨hq,hu⟩
    rw [mem_singleton_iff] at hq
    change q = p at hq
    subst q
    exact hp u hu
  obtain ⟨V,W,hV,_,hpV,hBW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedBall (0 : Leaf) r) ho hs
  apply Filter.mem_of_superset (hV.mem_nhds (hpV (mem_singleton p)))
  intro q hq u hu
  exact hVW (show (q,u) ∈ V ×ˢ W from ⟨hq,hBW hu⟩)

theorem isOpen_safeImage (c : Chart) (r : ℝ) : IsOpen (safeImage c r) :=
  quotientCoordinates_isOpenMap c.base _ (isOpen_safeParameters c r)

theorem chartCoordinates_safe {c : Chart} {r : ℝ} (hr : 0 ≤ r) {q : X}
    (hq : q ∈ safeImage c r) :
    quotientCoordinates c.base (chartCoordinates c q) = q ∧
      ∀ u : Leaf, ‖u‖ ≤ r → leafShift (chartCoordinates c q) u ∈ c.domain := by
  obtain ⟨p,hp,hpq⟩ := hq
  have hpdom : p ∈ c.domain := by
    simpa only [leafShift_zero] using hp 0 (by simpa only [mem_closedBall,dist_self] using hr)
  have hc : chartCoordinates c q = p := by rw [← hpq]; exact chartCoordinates_apply c ⟨p,hpdom⟩
  rw [hc]
  exact ⟨hpq,fun u hu => hp u (by simpa only [mem_closedBall,dist_zero_right] using hu)⟩

/-- A measurable index and measurable chart-coordinate map are actually
constructed. No measurable selection premise is required. -/
theorem compact_measurable_safe_selection {K : Set X} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : ℕ → Chart, ∃ index : X → ℕ,
      Measurable index ∧ Measurable (fun q => chartCoordinates (c (index q)) q) ∧
      ∀ q ∈ K, quotientCoordinates (c (index q)).base (chartCoordinates (c (index q)) q) = q ∧
        ∀ u : Leaf, ‖u‖ ≤ r → leafShift (chartCoordinates (c (index q)) q) u ∈ (c (index q)).domain := by
  classical
  obtain ⟨C,ε,hε,hC⟩ := compact_uniform_safe_plaques hK
  let D := insert (atlas 0) C
  letI : Nonempty D := ⟨⟨atlas 0,Finset.mem_insert_self _ _⟩⟩
  letI : Encodable D := Encodable.ofCountable D
  let e : ℕ → D := fun n => (Encodable.decode (α := D) n).getD (Classical.choice inferInstance)
  have he (d : D) : e (Encodable.encode d) = d := by simp [e]
  let c : ℕ → Chart := fun n => (e n).val
  have hcov (q : X) (hq : q ∈ K) : ∃ n, q ∈ safeImage (c n) (ε/2) := by
    obtain ⟨d,hd,p,hpq,hp⟩ := hC q hq
    let d' : D := ⟨d,Finset.mem_insert_of_mem hd⟩
    refine ⟨Encodable.encode d',?_⟩
    change q ∈ safeImage (e (Encodable.encode d')).val (ε/2)
    rw [he]
    change q ∈ safeImage d (ε/2)
    refine ⟨p,?_,hpq⟩
    intro u hu
    apply hp u
    have hu' : ‖u‖ ≤ ε/2 := by simpa only [mem_closedBall,dist_zero_right] using hu
    linarith
  let P : X → ℕ → Prop := fun q n => (q ∉ K ∧ n=0) ∨ q ∈ safeImage (c n) (ε/2)
  have hex (q : X) : ∃ n, P q n := by
    by_cases hq : q ∈ K
    · obtain ⟨n,hn⟩ := hcov q hq
      exact ⟨n,Or.inr hn⟩
    · exact ⟨0,Or.inl ⟨hq,rfl⟩⟩
  have hm (n : ℕ) : MeasurableSet {q : X | P q n} := by
    change MeasurableSet ({q : X | q ∉ K ∧ n=0} ∪ safeImage (c n) (ε/2))
    apply MeasurableSet.union _ (isOpen_safeImage _ _).measurableSet
    by_cases hn : n=0
    · simpa only [hn,and_true] using hK.measurableSet.compl
    · simp only [hn,and_false,setOf_false,MeasurableSet.empty]
  let index : X → ℕ := fun q => Nat.find (hex q)
  refine ⟨ε/2,half_pos hε,c,index,measurable_find hex hm,?_,?_⟩
  · exact Measurable.find (fun n => measurable_chartCoordinates (c n)) hm hex
  · intro q hq
    have hp := Nat.find_spec (hex q)
    have hs : q ∈ safeImage (c (index q)) (ε/2) := hp.resolve_left (fun hh => hh.1 hq)
    exact chartCoordinates_safe (half_pos hε).le hs

end VV.BBEKPlaqueSelection
