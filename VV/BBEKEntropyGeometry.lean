import VV.BBEKLocalChart

/-! Compact-uniform local injectivity for the concrete arithmetic quotient.
These are geometric ingredients for the first-exit entropy argument. -/

noncomputable section
open Set Metric Topology
open scoped Topology

namespace VV.BBEKEntropyGeometry
open BBEKDynamics BBEKQuotient BBEKLocalChart

/-- A single identity neighborhood acts injectively at every point in some
open neighborhood of a prescribed quotient point. -/
theorem exists_open_action_inj_near (q : X) :
    ∃ V : Set X, ∃ W : Set G, IsOpen V ∧ q ∈ V ∧ IsOpen W ∧ (1 : G) ∈ W ∧
      ∀ z ∈ V, Set.InjOn (fun h : G => h • z) W := by
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨U,hU,hg,hi⟩ := exists_open_injOn_mk g
  have hopen : IsOpen {p : G × G | p.1 * p.2 ∈ U} :=
    hU.preimage continuous_mul
  have hone : ((1 : G),g) ∈ {p : G × G | p.1 * p.2 ∈ U} := by simpa using hg
  obtain ⟨W,V,hW,hV,h1,hgV,hWV⟩ := isOpen_prod_iff.mp hopen 1 g hone
  refine ⟨mk '' V,W,isOpenMap_mk V hV,⟨g,hgV,rfl⟩,hW,h1,?_⟩
  rintro z ⟨k,hk,rfl⟩ a ha b hb hab
  have haU : a * k ∈ U := hWV (show (a,k) ∈ W ×ˢ V from ⟨ha,hk⟩)
  have hbU : b * k ∈ U := hWV (show (b,k) ∈ W ×ˢ V from ⟨hb,hk⟩)
  have he : mk (a * k) = mk (b * k) := by simpa only [smul_mk] using hab
  exact mul_right_cancel (hi haU hbU he)

/-- Compactness upgrades the pointwise local chart to one common identity
neighborhood for every base point in the compact set. -/
theorem compact_uniform_action_inj {Y : Set X} (hY : IsCompact Y) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧
      ∀ q ∈ Y, Set.InjOn (fun h : G => h • q) W := by
  classical
  choose V W hV hq hW h1 hi using exists_open_action_inj_near
  have hcover : Y ⊆ ⋃ q : X, V q := by
    intro q _
    exact mem_iUnion.mpr ⟨q,hq q⟩
  obtain ⟨s,hs⟩ := hY.elim_finite_subcover V hV hcover
  refine ⟨⋂ q ∈ s, W q, isOpen_biInter_finset (fun q _ => hW q), ?_, ?_⟩
  · simp only [mem_iInter]
    exact fun q _ => h1 q
  · intro q hqY
    obtain ⟨p,hps,hqp⟩ := mem_iUnion₂.mp (hs hqY)
    apply (hi p q hqp).mono
    intro a ha
    exact mem_iInter.mp (mem_iInter.mp ha p) hps

/-- A quantitative common injectivity radius in the actual entrywise
maximum metric on the matrix group. -/
theorem compact_uniform_action_inj_ball {Y : Set X} (hY : IsCompact Y) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Y,
      Set.InjOn (fun h : G => h • q) (ball (1 : G) r) := by
  obtain ⟨W,hW,h1,hi⟩ := compact_uniform_action_inj hY
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h1)
  exact ⟨r,hr,fun q hq => (hi q hq).mono hrW⟩

/-- Uniform local injectivity excludes all nonidentity stabilizers inside
the same positive radius, simultaneously over the compact set. -/
theorem compact_uniform_no_small_stabilizer {Y : Set X} (hY : IsCompact Y) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Y, ∀ h : G,
      dist h 1 < r → h • q = q → h = 1 := by
  obtain ⟨r,hr,hi⟩ := compact_uniform_action_inj_ball hY
  refine ⟨r,hr,?_⟩
  intro q hq h hsmall hfix
  apply hi q hq hsmall (by simpa using hr)
  simpa using hfix

theorem parameter_dist_one (z : ℝ × Q2) : dist (x z.1 z.2) 1 = ‖z‖ := by
  have h := isometry_x.dist_eq z 0
  simpa only [Prod.fst_zero,Prod.snd_zero,x_zero,dist_zero_right] using h

/-- An annulus of nontrivial small unstable displacements remains uniformly
away from the diagonal over a compact set of quotient base points. The
separation is expressed by an open diagonal neighborhood, so it is valid
without introducing an unjustified formula for a quotient metric. -/
theorem compact_parameter_annulus_separation {Y : Set X} (hY : IsCompact Y) :
    ∃ R : ℝ, 0 < R ∧ ∀ ε : ℝ, 0 < ε →
      ∃ E : Set (X × X), IsOpen E ∧ (∀ q : X, (q,q) ∈ E) ∧
        ∀ q ∈ Y, ∀ z : ℝ × Q2, ε ≤ ‖z‖ → ‖z‖ ≤ R →
          (q,x z.1 z.2 • q) ∉ E := by
  obtain ⟨r,hr,hfree⟩ := compact_uniform_no_small_stabilizer hY
  refine ⟨r/2,by positivity,?_⟩
  intro ε hε
  let A : Set (ℝ × Q2) := closedBall 0 (r/2) \ ball 0 ε
  have hA : IsCompact A := (isCompact_closedBall 0 (r/2)).diff isOpen_ball
  let F : (ℝ × Q2) × X → X × X := fun p => (p.2,x p.1.1 p.1.2 • p.2)
  have hF : Continuous F :=
    continuous_snd.prodMk ((continuous_x.comp continuous_fst).smul continuous_snd)
  let S : Set (X × X) := F '' (A ×ˢ Y)
  have hS : IsCompact S := (hA.prod hY).image hF
  refine ⟨Sᶜ,hS.isClosed.isOpen_compl,?_,?_⟩
  · intro q hq
    obtain ⟨⟨z,y⟩,⟨hz,hy⟩,he⟩ := hq
    have hzR : ‖z‖ ≤ r/2 := by simpa only [mem_closedBall,dist_zero_right] using hz.1
    have hzε : ε ≤ ‖z‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hz.2
    have hfix : x z.1 z.2 • y = y :=
      (congrArg Prod.snd he).trans (congrArg Prod.fst he).symm
    have heq : x z.1 z.2 = 1 := hfree y hy _
      (by rw [parameter_dist_one]; linarith) hfix
    have hzero : ‖z‖ = 0 := by rw [← parameter_dist_one,heq,dist_self]
    linarith
  · intro q hq z hzε hzR
    apply not_not.mpr
    refine ⟨(z,q),⟨?_,hq⟩,rfl⟩
    exact ⟨by simpa only [mem_closedBall,dist_zero_right] using hzR,
      by simpa only [mem_ball,dist_zero_right,not_lt] using hzε⟩

end VV.BBEKEntropyGeometry
