import VV.BBEKEntropyGeometry

/-! Genuine small-displacement lifts for nearby pairs in the arithmetic
quotient. The relation is open without choosing a quotient metric. -/

noncomputable section
open Set Metric Topology
open scoped Topology

namespace VV.BBEKBowenLift
open BBEKDynamics BBEKQuotient BBEKLocalChart BBEKEntropyGeometry

def displacementRelation (r : ℝ) : Set (X × X) :=
  {p | ∃ g : G, dist g 1 < r ∧ p.2 = g • p.1}

def groupPairRelation (r : ℝ) : Set (G × G) :=
  {p | dist (p.2*p.1⁻¹) 1 < r}

theorem displacementRelation_eq_image (r : ℝ) :
    displacementRelation r = Prod.map mk mk '' groupPairRelation r := by
  ext p
  constructor
  · rintro ⟨g,hg,he⟩
    obtain ⟨h,hh⟩ := QuotientGroup.mk_surjective p.1
    change mk h = p.1 at hh
    refine ⟨(h,g*h), ?_, ?_⟩
    · change dist ((g*h)*h⁻¹) 1 < r
      simpa only [mul_inv_cancel_right] using hg
    · apply Prod.ext
      · exact hh
      · change mk (g*h) = p.2
        rw [← smul_mk,hh,he]
  · rintro ⟨⟨h,k⟩,hsmall,he⟩
    refine ⟨k*h⁻¹,hsmall,?_⟩
    rw [← he]
    change mk k = (k*h⁻¹) • mk h
    rw [smul_mk,inv_mul_cancel_right]

/-- The image of an open relation under the open quotient map on each
coordinate is open. In particular, existence of a small lift is uniform
over all base points, and does not require an auxiliary metric on X. -/
theorem isOpen_displacementRelation (r : ℝ) : IsOpen (displacementRelation r) := by
  rw [displacementRelation_eq_image]
  apply (isOpenMap_mk.prodMap isOpenMap_mk)
  apply isOpen_lt _ continuous_const
  exact (continuous_snd.mul continuous_fst.inv).dist continuous_const

theorem diagonal_mem_displacementRelation {r : ℝ} (hr : 0 < r) (q : X) :
    (q,q) ∈ displacementRelation r := by
  exact ⟨1,by simpa using hr,by simp⟩

theorem displacementRelation_mono {r R : ℝ} (h : r ≤ R) :
    displacementRelation r ⊆ displacementRelation R := by
  rintro p ⟨g,hg,he⟩
  exact ⟨g,hg.trans_le h,he⟩

/-- Every pair in the actual open relation has a small group displacement. -/
theorem exists_small_lift {r : ℝ} {q q' : X}
    (h : (q,q') ∈ displacementRelation r) :
    ∃ g ∈ ball (1 : G) r, q' = g • q := h

theorem compact_exists_unique_small_lift {Y : Set X} (hY : IsCompact Y) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      IsOpen (displacementRelation r) ∧ (∀ q : X, (q,q) ∈ displacementRelation r) ∧
      ∀ q ∈ Y, ∀ q' : X, (q,q') ∈ displacementRelation r →
        ∃! g : G, dist g 1 < r ∧ q' = g • q := by
  obtain ⟨R,hR,hinj⟩ := compact_uniform_action_inj_ball hY
  refine ⟨R,hR,?_⟩
  intro r hr hrR
  refine ⟨isOpen_displacementRelation r,diagonal_mem_displacementRelation hr,?_⟩
  intro q hq q' hp
  obtain ⟨g,hg,hgq⟩ := hp
  refine ⟨g,⟨hg,hgq⟩,?_⟩
  rintro k ⟨hk,hkq⟩
  exact hinj q hq (hk.trans_le hrR) (hg.trans_le hrR) (hkq.symm.trans hgq)

/-- Whenever both successive lifts lie in the common injectivity ball,
their relation is the exact conjugation identity. No lift consistency
is assumed: it follows from uniqueness in the actual quotient action. -/
theorem lift_conjugation_of_small {Y : Set X} {R : ℝ}
    (hinj : ∀ q ∈ Y, Set.InjOn (fun h : G => h • q) (ball (1:G) R))
    (a g h : G) (q q' : X) (haq : a • q ∈ Y)
    (hg : q' = g • q) (hh : a • q' = h • (a • q))
    (hsmall : dist h 1 < R) (hcsmall : dist (a*g*a⁻¹) 1 < R) :
    h = a*g*a⁻¹ := by
  apply hinj (a • q) haq hsmall hcsmall
  change h • (a • q) = (a*g*a⁻¹) • (a • q)
  rw [← hh,hg]
  simp only [MulAction.mul_smul,inv_smul_smul]

/-- Shrinking the common lift radius makes the conjugated lift stay in
the injectivity ball. Thus the one-step cocycle identity holds for every
pair of successive small lifts, with no extra smallness hypothesis. -/
theorem compact_small_lifts_conjugate {Y : Set X} (hY : IsCompact Y) (a : G) :
    ∃ r : ℝ, 0 < r ∧ IsOpen (displacementRelation r) ∧
      (∀ q : X, (q,q) ∈ displacementRelation r) ∧
      (∀ q ∈ Y, ∀ q' : X, (q,q') ∈ displacementRelation r →
        ∃! g : G, dist g 1 < r ∧ q' = g • q) ∧
      (∀ q q' : X, ∀ g h : G, a • q ∈ Y →
        dist g 1 < r → dist h 1 < r → q' = g • q → a • q' = h • (a • q) →
        h = a*g*a⁻¹) := by
  obtain ⟨R,hR,hinj⟩ := compact_uniform_action_inj_ball hY
  have hopen : IsOpen {g : G | dist (a*g*a⁻¹) 1 < R} := by
    apply isOpen_lt _ continuous_const
    exact ((continuous_const.mul continuous_id).mul continuous_const).dist continuous_const
  have hone : (1 : G) ∈ {g : G | dist (a*g*a⁻¹) 1 < R} := by simpa using hR
  obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hone)
  let r := min R s
  have hr : 0 < r := lt_min hR hs
  refine ⟨r,hr,isOpen_displacementRelation r,diagonal_mem_displacementRelation hr,?_,?_⟩
  · intro q hq q' hp
    obtain ⟨g,hg,hgq⟩ := hp
    refine ⟨g,⟨hg,hgq⟩,?_⟩
    rintro k ⟨hk,hkq⟩
    exact hinj q hq (hk.trans_le (min_le_left _ _))
      (hg.trans_le (min_le_left _ _)) (hkq.symm.trans hgq)
  · intro q q' g h haq hg hh he he'
    exact lift_conjugation_of_small hinj a g h q q' haq he he'
      (hh.trans_le (min_le_left _ _)) (hsub (hg.trans_le (min_le_right _ _)))

/-- Two forward orbits that remain in the small open relation have one
initial displacement whose exact conjugates give all later displacements.
This is a concrete lift of the whole forward Bowen relation. -/
theorem compact_forward_lift {Y : Set X} (hY : IsCompact Y) (a : G) :
    ∃ r : ℝ, 0 < r ∧ IsOpen (displacementRelation r) ∧
      (∀ q : X, (q,q) ∈ displacementRelation r) ∧
      ∀ q q' : X, (∀ n : ℕ, a^n • q ∈ Y) →
        (∀ n : ℕ, (a^n • q,a^n • q') ∈ displacementRelation r) →
        ∃ g : G, dist g 1 < r ∧ ∀ n : ℕ,
          dist (a^n*g*(a⁻¹)^n) 1 < r ∧
          a^n • q' = (a^n*g*(a⁻¹)^n) • (a^n • q) := by
  obtain ⟨r,hr,ho,hd,_,hc⟩ := compact_small_lifts_conjugate hY a
  refine ⟨r,hr,ho,hd,?_⟩
  intro q q' hq hrel
  change ∀ n : ℕ, ∃ g : G, dist g 1 < r ∧ a^n • q' = g • (a^n • q) at hrel
  choose lift hsmall hact using hrel
  have hrec (n : ℕ) : lift (n+1) = a*lift n*a⁻¹ := by
    have hpow (x : X) : a • (a^n • x) = a^(n+1) • x := by
      rw [← MulAction.mul_smul,← pow_succ']
    apply hc (a^n • q) (a^n • q') (lift n) (lift (n+1))
    · rw [hpow]
      exact hq (n+1)
    · exact hsmall n
    · exact hsmall (n+1)
    · exact hact n
    · simpa only [hpow] using hact (n+1)
  have he (n : ℕ) : lift n = a^n*lift 0*(a⁻¹)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hrec,ih,pow_succ' a,pow_succ a⁻¹]
      group
  refine ⟨lift 0,hsmall 0,?_⟩
  intro n
  rw [← he n]
  exact ⟨hsmall n,hact n⟩

end VV.BBEKBowenLift
