import VV.BBEKQuadraticScale
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-! Uniform nonconcentration of a finite nonatomic root measure near zeros
of normalized one-dimensional quadratic shearing polynomials. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace VV.BBEKShearNonconcentration
variable {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]

/-- The nonconstant part of the actual rank-one shearing polynomial. -/
def shearPolynomial (p : F × F) (v : F) : F := p.1 * v + p.2 * v^2

theorem continuous_shearPolynomial (p : F × F) : Continuous (shearPolynomial p) := by
  exact (continuous_const.mul continuous_id).add (continuous_const.mul (continuous_id.pow 2))

theorem finite_zero_set {p : F × F} (hp : p ≠ 0) :
    {v | shearPolynomial p v = 0}.Finite := by
  by_cases hb : p.2 = 0
  · have ha : p.1 ≠ 0 := by intro ha; exact hp (Prod.ext ha hb)
    apply (finite_singleton (0 : F)).subset
    intro v hv
    simpa [shearPolynomial,hb,ha] using hv
  · apply ((finite_singleton (-p.1 / p.2)).insert (0 : F)).subset
    intro v hv
    have hmul : v * (p.1 + p.2*v) = 0 := by
      change shearPolynomial p v = 0 at hv
      dsimp [shearPolynomial] at hv
      linear_combination hv
    rcases mul_eq_zero.mp hmul with h | h
    · simp [h]
    · have he : v = -p.1 / p.2 := by
        apply (eq_div_iff hb).2
        linear_combination h
      simp [he]

theorem zero_set_measure_zero (ν : Measure F) [NoAtoms ν] {p : F × F} (hp : p ≠ 0) :
    ν {v | shearPolynomial p v = 0} = 0 := (finite_zero_set hp).measure_zero ν

/-- At each nonzero coefficient vector, sufficiently small sublevel sets have
arbitrarily small mass. This uses only finiteness and absence of atoms. -/
theorem exists_small_sublevel (ν : Measure F) [IsFiniteMeasure ν] [NoAtoms ν]
    {p : F × F} (hp : p ≠ 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ν {v | ‖shearPolynomial p v‖ ≤ δ} < ε := by
  let E : ℕ → Set F := fun n => {v | ‖shearPolynomial p v‖ ≤ 1 / ((n:ℝ)+1)}
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_le (continuous_shearPolynomial p).norm.measurable measurable_const
  have hanti : Antitone E := by
    intro n m hnm v hv
    change ‖shearPolynomial p v‖ ≤ 1 / ((m:ℝ)+1) at hv
    change ‖shearPolynomial p v‖ ≤ 1 / ((n:ℝ)+1)
    exact hv.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have heq : ⋂ n, E n = {v | shearPolynomial p v = 0} := by
    ext v
    simp only [mem_iInter, E, mem_setOf_eq]
    constructor
    · intro h
      exact norm_eq_zero.mp (le_antisymm
        (ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat h) (norm_nonneg _))
    · intro h n
      simp only [h,norm_zero]
      positivity
  have hlim := tendsto_measure_iInter_atTop (fun n => (hEm n).nullMeasurableSet)
    hanti ⟨0,measure_ne_top ν _⟩
  rw [heq,zero_set_measure_zero ν hp] at hlim
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨1/((n:ℝ)+1),by positivity,hn⟩

/-- Uniform Lipschitz control in the two coefficient variables on a bounded
root ball. This estimate applies to both real and 2-adic root coordinates. -/
theorem polynomial_difference_le (p q : F × F) {v : F} {R : ℝ}
    (hv : ‖v‖ ≤ R) :
    ‖shearPolynomial p v - shearPolynomial q v‖ ≤ dist p q * (R + R^2) := by
  have hR : 0 ≤ R := (norm_nonneg v).trans hv
  have ha : ‖p.1-q.1‖ ≤ dist p q := by
    simpa only [dist_eq_norm,Prod.fst_sub] using norm_fst_le (p-q)
  have hb : ‖p.2-q.2‖ ≤ dist p q := by
    simpa only [dist_eq_norm,Prod.snd_sub] using norm_snd_le (p-q)
  have he : shearPolynomial p v - shearPolynomial q v =
      (p.1-q.1)*v + (p.2-q.2)*v^2 := by dsimp [shearPolynomial]; ring
  rw [he]
  apply le_trans (norm_add_le _ _)
  rw [norm_mul,norm_mul,norm_pow]
  have h1 := mul_le_mul ha hv (norm_nonneg v) (dist_nonneg (x := p) (y := q))
  have h2 := mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg v) hv 2)
    (sq_nonneg ‖v‖) (dist_nonneg (x := p) (y := q))
  nlinarith



/-- The sublevel estimate is uniform on any compact coefficient set that
avoids the zero polynomial. No doubling or absolute continuity is assumed. -/
theorem uniform_small_sublevels (ν : Measure F) [IsFiniteMeasure ν] [NoAtoms ν]
    {C : Set (F × F)} (hC : IsCompact C) (hC0 : ∀ p ∈ C, p ≠ 0)
    {R : ℝ} (hR : 0 ≤ R) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ C,
      ν {v | ‖v‖ ≤ R ∧ ‖shearPolynomial p v‖ ≤ δ} < ε := by
  classical
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1,by norm_num,fun p hp => (hne ⟨p,hp⟩).elim⟩
  choose d hdpos hdμ using fun p : C => exists_small_sublevel ν (hC0 p p.property) hε
  let L := R + R^2 + 1
  have hL : 0 < L := by dsimp [L]; nlinarith
  let U : C → Set (F × F) := fun p => ball p.val (d p / (2*L))
  have hcover : C ⊆ ⋃ p : C, U p := by
    intro p hp
    refine mem_iUnion.mpr ⟨⟨p,hp⟩,?_⟩
    exact mem_ball_self (div_pos (hdpos _) (by positivity))
  obtain ⟨S,hS⟩ := hC.elim_finite_subcover U (fun _ => isOpen_ball) hcover
  have hSne : S.Nonempty := by
    obtain ⟨p,hp⟩ := hne
    obtain ⟨q,hq,_⟩ := mem_iUnion₂.mp (hS hp)
    exact ⟨q,hq⟩
  let δ := S.inf' hSne (fun p => d p / 2)
  have hδ : 0 < δ := (Finset.lt_inf'_iff hSne).2 (fun p _ => half_pos (hdpos p))
  refine ⟨δ,hδ,?_⟩
  intro p hp
  obtain ⟨q,hq,hpq⟩ := mem_iUnion₂.mp (hS hp)
  have hδq : δ ≤ d q / 2 := Finset.inf'_le _ hq
  apply lt_of_le_of_lt (measure_mono ?_) (hdμ q)
  intro v hv
  have hdist : dist q.val p * L < d q / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2*L)).1
      (show dist p q.val < d q / (2*L) from hpq)
    rw [dist_comm] at h
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc dist q.val p * L * 2 = dist q.val p * (2*L) := by ring
         _ < d q := h
  have hdiff : ‖shearPolynomial q.val v - shearPolynomial p v‖ ≤ d q / 2 := by
    apply (polynomial_difference_le q.val p hv.1).trans
    have hnonneg : 0 ≤ dist q.val p := dist_nonneg
    dsimp [L] at hdist
    nlinarith
  have he : ‖shearPolynomial q.val v‖ ≤
      ‖shearPolynomial q.val v - shearPolynomial p v‖ + ‖shearPolynomial p v‖ :=
    by simpa only [sub_add_cancel] using (norm_add_le
      (shearPolynomial q.val v - shearPolynomial p v) (shearPolynomial p v))
  exact (he.trans (add_le_add hdiff hv.2)).trans (by linarith)

/-- The compact annulus of normalized two-coefficient polynomials. -/
def coefficientAnnulus (F : Type*) [NormedField F] (c : ℝ) : Set (F × F) :=
  {p | c ≤ ‖p‖ ∧ ‖p‖ ≤ 1}

theorem isCompact_coefficientAnnulus [ProperSpace F] (c : ℝ) :
    IsCompact (coefficientAnnulus F c) := by
  apply (isCompact_closedBall (0 : F × F) 1).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
  intro p hp
  simpa only [mem_closedBall,dist_zero_right] using hp.2

/-- Uniform small sublevel mass for all normalized real or 2-adic shear
coefficients. In the preceding scale theorem one can take `c=1/16`. -/
theorem uniform_normalized_sublevels [ProperSpace F]
    (ν : Measure F) [IsFiniteMeasure ν] [NoAtoms ν]
    {c R : ℝ} (hc : 0 < c) (hR : 0 ≤ R) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : F,
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → c ≤ max ‖a‖ ‖b‖ →
      ν {v | ‖v‖ ≤ R ∧ ‖a*v+b*v^2‖ ≤ δ} < ε := by
  have hzero : ∀ p ∈ coefficientAnnulus F c, p ≠ 0 := by
    intro p hp h0
    have := hp.1
    rw [h0,norm_zero] at this
    exact (not_le_of_gt hc) this
  obtain ⟨δ,hδ,hu⟩ := uniform_small_sublevels ν (isCompact_coefficientAnnulus c)
    hzero hR hε
  refine ⟨δ,hδ,?_⟩
  intro a b ha hb hc'
  apply hu (a,b)
  exact ⟨hc',max_le ha hb⟩

end VV.BBEKShearNonconcentration




