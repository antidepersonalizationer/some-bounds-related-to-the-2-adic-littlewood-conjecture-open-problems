import VV.BBEKLeafEntropyBoundary
import VV.BBEKOneRootTranslation

/-!
# Observable radii of safe joint-root plaques

The radius is capped at one. Its strict superlevel sets are open, and it is
one-Lipschitz along the actual joint-root action. These facts let boundary
cuts use the exact root contraction, without choosing a metric on the quotient.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped Topology ENNReal
namespace VV.BBEKLeafEntropySafety
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKOneRootTranslation BBEKLeafEntropyBoundary

theorem safeImage_antitone (c : Chart) {r s : ℝ} (hrs : r ≤ s) :
    safeImage c s ⊆ safeImage c r := by
  rintro q ⟨p,hp,rfl⟩
  exact ⟨p,fun u hu => hp u (closedBall_subset_closedBall hrs hu),rfl⟩

def safeRadii (c : Chart) (q : X) : Set ℝ :=
  {r | 0 ≤ r ∧ r ≤ 1 ∧ (r = 0 ∨ q ∈ safeImage c r)}

def safetyRadius (c : Chart) (q : X) : ℝ := sSup (safeRadii c q)

theorem safeRadii_nonempty (c : Chart) (q : X) : (safeRadii c q).Nonempty :=
  ⟨0,le_rfl,zero_le_one,Or.inl rfl⟩

theorem safeRadii_bddAbove (c : Chart) (q : X) : BddAbove (safeRadii c q) :=
  ⟨1,fun _ h => h.2.1⟩

theorem safetyRadius_nonneg (c : Chart) (q : X) : 0 ≤ safetyRadius c q :=
  le_csSup (safeRadii_bddAbove c q) ⟨le_rfl,zero_le_one,Or.inl rfl⟩

theorem safetyRadius_le_one (c : Chart) (q : X) : safetyRadius c q ≤ 1 :=
  csSup_le (safeRadii_nonempty c q) (fun _ h => h.2.1)

theorem le_safetyRadius_of_mem {c : Chart} {q : X} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hq : q ∈ safeImage c r) :
    r ≤ safetyRadius c q :=
  le_csSup (safeRadii_bddAbove c q) ⟨hr,hr1,Or.inr hq⟩

theorem lt_safetyRadius_iff {c : Chart} {q : X} {r : ℝ} (hr : 0 ≤ r) :
    r < safetyRadius c q ↔ ∃ s : ℝ, r < s ∧ s ≤ 1 ∧ q ∈ safeImage c s := by
  rw [safetyRadius,lt_csSup_iff (safeRadii_bddAbove c q) (safeRadii_nonempty c q)]
  constructor
  · rintro ⟨s,hs,hrs⟩
    refine ⟨s,hrs,hs.2.1,?_⟩
    exact hs.2.2.resolve_left (fun h => by linarith)
  · rintro ⟨s,hrs,hs1,hq⟩
    exact ⟨s,⟨hr.trans hrs.le,hs1,Or.inr hq⟩,hrs⟩

theorem mem_safeImage_of_lt_safetyRadius {c : Chart} {q : X} {r : ℝ}
    (hr : 0 ≤ r) (hq : r < safetyRadius c q) : q ∈ safeImage c r := by
  obtain ⟨s,hrs,_,hs⟩ := (lt_safetyRadius_iff hr).mp hq
  exact safeImage_antitone c hrs.le hs

theorem isOpen_safetyRadius_superlevel (c : Chart) (r : ℝ) :
    IsOpen {q | r < safetyRadius c q} := by
  by_cases hr : 0 ≤ r
  · have heq : {q | r < safetyRadius c q} =
        ⋃ (s : ℝ) (_ : r < s) (_ : s ≤ 1), safeImage c s := by
      ext q
      simp only [mem_setOf_eq,mem_iUnion,lt_safetyRadius_iff hr]
      exact ⟨fun ⟨s,hs,hs1,hq⟩ => ⟨s,hs,hs1,hq⟩,
        fun ⟨s,hs,hs1,hq⟩ => ⟨s,hs,hs1,hq⟩⟩
    rw [heq]
    exact isOpen_iUnion fun s => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
      isOpen_safeImage c s
  · have heq : {q | r < safetyRadius c q} = univ := by
      ext q
      simp only [mem_setOf_eq,mem_univ,iff_true]
      exact (lt_of_not_ge hr).trans_le (safetyRadius_nonneg c q)
    rw [heq]
    exact isOpen_univ

theorem measurable_safetyRadius (c : Chart) : Measurable (safetyRadius c) :=
  measurable_of_Ioi fun r => (isOpen_safetyRadius_superlevel c r).measurableSet

theorem safetyRadius_sub_norm_le (c : Chart) (q : X) (u : Leaf) :
    safetyRadius c q - ‖u‖ ≤ safetyRadius c (x u.1 u.2 • q) := by
  apply le_of_forall_lt_imp_le_of_dense
  intro r hr
  by_cases hr0 : 0 ≤ r
  · have hrs : r + ‖u‖ < safetyRadius c q := by linarith
    have hs := mem_safeImage_of_lt_safetyRadius (by positivity : 0 ≤ r+‖u‖) hrs
    exact le_safetyRadius_of_mem hr0
      (by have := safetyRadius_le_one c q; have := norm_nonneg u; linarith)
      (safeImage_root_shift c q u hs)
  · exact (lt_of_not_ge hr0).le.trans (safetyRadius_nonneg c _)

theorem root_neg_smul_cancel (u : Leaf) (q : X) :
    x (-u).1 (-u).2 • (x u.1 u.2 • q) = q := by
  rw [smul_smul]
  simp only [Prod.fst_neg,Prod.snd_neg,← x_add,neg_add_cancel,x_zero,one_smul]

theorem abs_safetyRadius_sub_le (c : Chart) (q : X) (u : Leaf) :
    |safetyRadius c (x u.1 u.2 • q) - safetyRadius c q| ≤ ‖u‖ := by
  have h₁ := safetyRadius_sub_norm_le c q u
  have h₂ := safetyRadius_sub_norm_le c (x u.1 u.2 • q) (-u)
  rw [root_neg_smul_cancel,norm_neg] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end VV.BBEKLeafEntropySafety
