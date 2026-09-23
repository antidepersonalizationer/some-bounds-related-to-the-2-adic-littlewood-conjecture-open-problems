import VV.BBEKBowenMetric
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open Set Metric Filter Function
open scoped Topology Uniformity
namespace VV.BBEKPeriodicOrbit
open BBEKDynamics BBEKQuotient BBEKDiagonal
open ErgodicTheory.Entropy

section Abelian
variable {H Z : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SigmaCompactSpace H] [MetricSpace Z] [CompactSpace Z] [Nonempty Z]
  [MulAction H Z] [ContinuousSMul H Z] [MulAction.IsPretransitive H Z]

theorem iterate_smul_eq (a : H) (z : Z) (n : ℕ) :
    ((fun z : Z => a • z)^[n]) z = a^n • z := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih,← MulAction.mul_smul,← pow_succ']

/-- On a compact transitive abelian homogeneous space, finitely many open
sets have arbitrarily small orbit diameter simultaneously at every time. -/
theorem finite_orbit_diameter_cover (a : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ ∃ W : Fin M → Set Z,
      (∀ i, IsOpen (W i)) ∧ (⋃ i, W i)=univ ∧
      ∀ i, ∀ y ∈ W i, ∀ z ∈ W i, ∀ n : ℕ,
        dist (((fun z : Z => a • z)^[n]) y) (((fun z : Z => a • z)^[n]) z) < ε := by
  classical
  have hcont : Continuous (fun p : H × Z => p.1 • p.2) := continuous_fst.smul continuous_snd
  obtain ⟨V,hV,hsmall⟩ := IsCompact.mem_uniformity_of_prod (f:=fun h : H => fun z : Z => h • z)
    (s:=univ) (q:=(1:H)) isCompact_univ hcont.continuousOn (mem_univ _)
    (Metric.dist_mem_uniformity (half_pos hε))
  rw [nhdsWithin_univ] at hV
  obtain ⟨U,hUV,hU,h1⟩ := mem_nhds_iff.mp hV
  let C : Z → Set Z := fun z => (fun h : H => h • z) '' U
  have hopen (z : Z) : IsOpen (C z) := isOpenMap_smul_of_sigmaCompact z U hU
  have hcover : (univ : Set Z) ⊆ ⋃ z : Z, C z := by
    intro z _
    exact mem_iUnion.mpr ⟨z,1,h1,one_smul _ _⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover C hopen hcover
  obtain ⟨z,hzs,_⟩ := mem_iUnion₂.mp (hs (mem_univ (Classical.choice (inferInstance : Nonempty Z))))
  letI : Nonempty s := ⟨⟨z,hzs⟩⟩
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s,Fintype.card_pos,fun i => C (e.symm i),?_,?_,?_⟩
  · intro i; exact hopen _
  · apply eq_univ_of_forall
    intro y
    obtain ⟨z,hz,hy⟩ := mem_iUnion₂.mp (hs (mem_univ y))
    refine mem_iUnion.mpr ⟨e ⟨z,hz⟩,?_⟩
    simpa only [Equiv.symm_apply_apply] using hy
  · intro i y hy z hz n
    obtain ⟨u,hu,rfl⟩ := hy
    obtain ⟨v,hv,rfl⟩ := hz
    rw [iterate_smul_eq,iterate_smul_eq]
    have hcomm (u : H) : a^n • (u • (e.symm i : s).val) = u • (a^n • (e.symm i : s).val) := by
      simp only [← MulAction.mul_smul,mul_comm]
    rw [hcomm,hcomm]
    have hu' : dist (u • (a^n • (e.symm i : s).val)) (a^n • (e.symm i : s).val) < ε/2 := by
      simpa only [one_smul] using hsmall u (hUV hu) (a^n • (e.symm i : s).val) (mem_univ _)
    have hv' : dist (v • (a^n • (e.symm i : s).val)) (a^n • (e.symm i : s).val) < ε/2 := by
      simpa only [one_smul] using hsmall v (hUV hv) (a^n • (e.symm i : s).val) (mem_univ _)
    calc
      _ ≤ dist (u • (a^n • (e.symm i : s).val)) (a^n • (e.symm i : s).val) +
        dist (a^n • (e.symm i : s).val) (v • (a^n • (e.symm i : s).val)) := dist_triangle _ _ _
      _ < ε/2+ε/2 := add_lt_add hu' (by simpa only [dist_comm] using hv')
      _ = ε := by ring

theorem uniformBowenCover_smul (a : H) (r : ℝ) : UniformBowenCover (fun z : Z => a • z) r := by
  intro ε hε
  obtain ⟨M,hM,W,_,hW,hdiam⟩ := finite_orbit_diameter_cover (Z:=Z) a hε
  refine ⟨M,hM,?_⟩
  intro n x
  refine ⟨W,by rw [hW]; exact subset_univ _,?_⟩
  intro i y hy z hz k _
  exact hdiam i y hy z hz k

end Abelian
end VV.BBEKPeriodicOrbit
