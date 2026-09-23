import VV.BBEKEntropyExpansive
import VV.BBEKTopology

set_option maxHeartbeats 800000
noncomputable section
open Matrix Set Filter Metric
open scoped MatrixGroups Topology Uniformity
namespace VV.BBEKFiniteBowen
open BBEKDynamics BBEKQuotient BBEKBowenLift BBEKEntropyExpansive
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem diagConjugate_dist_interpolate {F : Type*} [NormedField F]
    (b : F) (hb : b ≠ 0) (hbn : ‖b‖ ≤ 1) (M N : SL(2,F))
    {j k : ℕ} (hjk : j ≤ k) :
    dist (diagConjugate (b^j) (pow_ne_zero _ hb) M)
      (diagConjugate (b^j) (pow_ne_zero _ hb) N) ≤
    max (dist M N) (dist (diagConjugate (b^k) (pow_ne_zero _ hb) M)
      (diagConjugate (b^k) (pow_ne_zero _ hb) N)) := by
  let R := max (dist M N) (dist (diagConjugate (b^k) (pow_ne_zero _ hb) M)
      (diagConjugate (b^k) (pow_ne_zero _ hb) N))
  have hR : 0 ≤ R := le_trans dist_nonneg (le_max_left _ _)
  change dist (diagConjugate (b^j) (pow_ne_zero _ hb) M).val
    (diagConjugate (b^j) (pow_ne_zero _ hb) N).val ≤ R
  apply (dist_pi_le_iff hR).mpr
  intro i
  apply (dist_pi_le_iff hR).mpr
  intro l
  have hMe := diagConjugate_entries (b^j) (pow_ne_zero _ hb) M
  have hNe := diagConjugate_entries (b^j) (pow_ne_zero _ hb) N
  fin_cases i <;> fin_cases l
  · change dist (diagConjugate (b^j) (pow_ne_zero _ hb) M 0 0) (diagConjugate (b^j) (pow_ne_zero _ hb) N 0 0) ≤ R
    rw [hMe.1,hNe.1]
    exact (entry_dist_le M N 0 0).trans (le_max_left _ _)
  · change dist (diagConjugate (b^j) (pow_ne_zero _ hb) M 0 1) (diagConjugate (b^j) (pow_ne_zero _ hb) N 0 1) ≤ R
    rw [hMe.2.1,hNe.2.1,dist_eq_norm,← mul_sub,norm_mul]
    calc
      _ ≤ ‖M 0 1-N 0 1‖ := by
        apply mul_le_of_le_one_left (norm_nonneg _)
        rw [norm_pow,norm_pow]
        exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) hbn)
      _ ≤ R := by simpa only [dist_eq_norm] using (entry_dist_le M N 0 1).trans (le_max_left (dist M N) (dist (diagConjugate (b^k) (pow_ne_zero _ hb) M) (diagConjugate (b^k) (pow_ne_zero _ hb) N)))
  · change dist (diagConjugate (b^j) (pow_ne_zero _ hb) M 1 0) (diagConjugate (b^j) (pow_ne_zero _ hb) N 1 0) ≤ R
    have he : dist (diagConjugate (b^j) (pow_ne_zero _ hb) M 1 0) (diagConjugate (b^j) (pow_ne_zero _ hb) N 1 0) ≤
        dist (diagConjugate (b^k) (pow_ne_zero _ hb) M 1 0) (diagConjugate (b^k) (pow_ne_zero _ hb) N 1 0) := by
      rw [hMe.2.2.1,hNe.2.2.1,(diagConjugate_entries _ _ M).2.2.1,
        (diagConjugate_entries _ _ N).2.2.1]
      simp only [dist_eq_norm,← mul_sub,norm_mul,norm_pow,norm_inv,← inv_pow]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply pow_le_pow_left₀ (by positivity)
      exact pow_le_pow_right₀ ((one_le_inv₀ (norm_pos_iff.mpr hb)).mpr hbn) hjk
    exact he.trans ((entry_dist_le _ _ 1 0).trans (le_max_right _ _))
  · change dist (diagConjugate (b^j) (pow_ne_zero _ hb) M 1 1) (diagConjugate (b^j) (pow_ne_zero _ hb) N 1 1) ≤ R
    rw [hMe.2.2.2,hNe.2.2.2]
    exact (entry_dist_le M N 1 1).trans (le_max_left _ _)

theorem forwardConjugate_dist_interpolate {t : ℝ} (ht : 0 < t) (g h : G)
    {j k : ℕ} (hjk : j ≤ k) :
    dist (forwardConjugate t j g) (forwardConjugate t j h) ≤
      max (dist g h) (dist (forwardConjugate t k g) (forwardConjugate t k h)) := by
  have hR := diagConjugate_dist_interpolate (Real.exp (-t)) (Real.exp_ne_zero _) (by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_le_one_iff]; linarith) g.1 h.1 hjk
  have hP := diagConjugate_dist_interpolate ((2:Q2)^(1:ℤ))
    (zpow_ne_zero _ (by norm_num)) (by
      rw [show ‖(2:Q2)^(1:ℤ)‖ = (2:ℝ)^(-(1:ℤ)) from padicNormE.norm_p_zpow (p:=2) 1]
      norm_num) g.2 h.2 hjk
  have hcompR (z : G) (n : ℕ) : (forwardConjugate t n z).1 =
      diagConjugate ((Real.exp (-t))^n) (pow_ne_zero _ (Real.exp_ne_zero _)) z.1 :=
    power_diagConjugate (Real.exp (-t)) (Real.exp_ne_zero (-t)) z.1 n
  have hcompP (z : G) (n : ℕ) : (forwardConjugate t n z).2 =
      diagConjugate (((2:Q2)^(1:ℤ))^n) (pow_ne_zero _ (zpow_ne_zero _ (by norm_num))) z.2 :=
    power_diagConjugate ((2:Q2)^(1:ℤ)) (zpow_ne_zero _ (by norm_num)) z.2 n
  rw [Prod.dist_eq,Prod.dist_eq,Prod.dist_eq]
  simp only [hcompR,hcompP]
  exact max_le (hR.trans (max_le_max (le_max_left _ _) (le_max_left _ _)))
    (hP.trans (max_le_max (le_max_right _ _) (le_max_right _ _)))






/-- Finite Bowen windows lift with the same radius at every window length. -/
theorem compact_finite_lift {Y : Set X} (hY : IsCompact Y) (a : G) :
    ∃ r : ℝ, 0 < r ∧ IsOpen (displacementRelation r) ∧
      (∀ q : X, (q,q) ∈ displacementRelation r) ∧
      ∀ (N : ℕ) (q q' : X), (∀ j ≤ N, a^j • q ∈ Y) →
        (∀ j ≤ N, (a^j • q,a^j • q') ∈ displacementRelation r) →
        ∃ g : G, ∀ j ≤ N,
          dist (a^j*g*(a⁻¹)^j) 1 < r ∧
          a^j • q' = (a^j*g*(a⁻¹)^j) • (a^j • q) := by
  classical
  obtain ⟨r,hr,ho,hd,_,hc⟩ := compact_small_lifts_conjugate hY a
  refine ⟨r,hr,ho,hd,?_⟩
  intro N q q' hq hrel
  have hex (j : ℕ) : ∃ g : G, j ≤ N →
      dist g 1 < r ∧ a^j • q' = g • (a^j • q) := by
    by_cases hj : j ≤ N
    · obtain ⟨g,hg,he⟩ := hrel j hj
      exact ⟨g,fun _ => ⟨hg,he⟩⟩
    · exact ⟨1,fun h => False.elim (hj h)⟩
  choose lift hprops using hex
  have hrec (j : ℕ) (hj : j+1 ≤ N) : lift (j+1) = a*lift j*a⁻¹ := by
    have hpow (z : X) : a • (a^j • z) = a^(j+1) • z := by
      rw [← MulAction.mul_smul,← pow_succ']
    apply hc (a^j • q) (a^j • q') (lift j) (lift (j+1))
    · rw [hpow]; exact hq (j+1) hj
    · exact (hprops j (by omega)).1
    · exact (hprops (j+1) hj).1
    · exact (hprops j (by omega)).2
    · simpa only [hpow] using (hprops (j+1) hj).2
  have he (j : ℕ) (hj : j ≤ N) : lift j = a^j*lift 0*(a⁻¹)^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [hrec j hj,ih (by omega),pow_succ' a,pow_succ a⁻¹]
      group
  refine ⟨lift 0,?_⟩
  intro j hj
  rw [← he j hj]
  exact hprops j hj

instance sl2_proper {F : Type*} [NormedField F] [ProperSpace F] : ProperSpace SL(2,F) := by
  letI : ProperSpace (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (ProperSpace (Fin 2 → Fin 2 → F))
  exact ProperSpace.of_isClosed (isClosed_eq continuous_id.matrix_det continuous_const)

/-- Uniform continuity of the literal action on compact group parameters
and compact base points, stated for any open diagonal neighborhood. -/
theorem compact_uniform_action_relation {C : Set G} (hC : IsCompact C)
    {Y : Set X} (hY : IsCompact Y) {E : Set (X × X)} (hE : IsOpen E)
    (hdiag : ∀ z : X, (z,z) ∈ E) :
    ∃ η : ℝ, 0 < η ∧ ∀ g ∈ C, ∀ h ∈ C, ∀ q ∈ Y,
      dist g h < η → (g • q,h • q) ∈ E := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let D := C ×ˢ Y
  letI : CompactSpace D := isCompact_iff_compactSpace.mp (hC.prod hY)
  let f : D → X := fun p => p.val.1 • p.val.2
  have hf : Continuous f := continuous_subtype_val.fst.smul continuous_subtype_val.snd
  let U : Set (D × D) := (Prod.map f f) ⁻¹' E
  have hU : IsOpen U := hE.preimage (hf.prodMap hf)
  have huni : U ∈ 𝓤 D := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    apply hU.mem_nhdsSet.mpr
    rintro ⟨a,b⟩ (hab : a=b)
    subst b
    exact hdiag (f a)
  obtain ⟨η,hη,hηU⟩ := Metric.mem_uniformity_dist.mp huni
  refine ⟨η,hη,?_⟩
  intro g hg h hh q hq hd
  apply @hηU (⟨(g,q),⟨hg,hq⟩⟩ : D) ⟨(h,q),⟨hh,hq⟩⟩
  change max (dist g h) (dist q q) < η
  simpa only [dist_self,max_eq_left dist_nonneg] using hd

end VV.BBEKFiniteBowen


