import VV.BBEKLeafEntropyBoundary
import VV.Entropy.SmallPartition

/-!
# Finite small partitions with exponential orbit-boundary control

The covering balls are selected with the summable boundary estimate, then made
exactly disjoint. For every measure-preserving time map, its iterates eventually
stay far enough from every cutting sphere that exponentially close points have
the same partition name. This is the boundary step in a subordinate-partition
construction; it does not assert the missing leaf entropy formula.
-/
noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped ENNReal Topology
namespace VV.BBEKLeafEntropyGoodPartition
open ErgodicTheory.Entropy BBEKLeafEntropyBoundary

variable {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z]
  [OpensMeasurableSpace Z]

omit [MeasurableSpace Z] [OpensMeasurableSpace Z] in
/-- Away from a cutting sphere, sufficiently close points agree on ball membership. -/
theorem mem_ball_iff_of_away {x y z : Z} {r ε : ℝ}
    (haway : ε < |dist x z-r|) (hxy : dist x y < ε) :
    x ∈ ball z r ↔ y ∈ ball z r := by
  change dist x z < r ↔ dist y z < r
  by_cases hx : dist x z < r
  · have he : ε < r-dist x z := by
      rw [abs_of_neg (sub_neg.mpr hx)] at haway
      linarith
    have hy : dist y z < r := by
      have ht := dist_triangle y x z
      rw [dist_comm y x] at ht
      linarith
    exact iff_of_true hx hy
  · have he : ε < dist x z-r := by
      rwa [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hx))] at haway
    have hy : ¬ dist y z < r := by
      have ht := dist_triangle x y z
      linarith
    exact iff_of_false hx hy

omit [MeasurableSpace Z] [PseudoMetricSpace Z] [OpensMeasurableSpace Z] in
/-- Disjointing a finite cover preserves agreement on membership in every set. -/
theorem mem_disjointed_iff_of_mem_iff {m : ℕ} (U : Fin m → Set Z) {x y : Z}
    (h : ∀ i, x ∈ U i ↔ y ∈ U i) (i : Fin m) :
    x ∈ disjointed U i ↔ y ∈ disjointed U i := by
  simp only [disjointed_eq_inter_compl, mem_inter_iff, mem_iInter, mem_compl_iff, h]

/-- Finite small partitions with genuinely summable cutting boundaries.
The partition is chosen before the preserving time map; hence the same
partition works for every such map without changing its cutting levels. -/
theorem exists_small_orbit_good_partition [CompactSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] {ε θ : ℝ}
    (hε : 0 < ε) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ m : ℕ, ∃ P : FixedPartition Z (Fin m),
      (∀ i, μ (frontier (P.cells i)) = 0) ∧
      (∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < ε) ∧
      ∀ T : Z → Z, MeasurePreserving T μ μ →
        ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop,
          ∀ y : Z, dist ((T^[n]) x) y < θ^n →
            ∀ i, ((T^[n]) x ∈ P.cells i ↔ y ∈ P.cells i) := by
  classical
  have hex : ∀ z : Z, ∃ r : ℝ, 0 < r ∧ 2*r < ε ∧
      (∑' n : ℕ, μ {x | |dist x z-r| ≤ θ^n}) < ∞ := by
    intro z
    obtain ⟨r,hr,hs,_,_⟩ := exists_geometric_ball_boundary_cut μ z
      (a := ε/4) (b := ε/2) (c := 1) (θ := θ) (by linarith) (by norm_num) hθ0 hθ1
    refine ⟨r,by linarith [hr.1],by linarith [hr.2],?_⟩
    simpa only [one_mul] using hs
  choose r hrpos hrsmall hrsum using hex
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover
    (fun z : Z => ball z (r z)) (fun _ => isOpen_ball)
    (by intro z _; exact mem_iUnion.mpr ⟨z,mem_ball_self (hrpos z)⟩)
  let m := Fintype.card F
  let e : Fin m ≃ F := (Fintype.equivFin F).symm
  let U : Fin m → Set Z := fun i => ball (e i).val (r (e i).val)
  have hU : ∀ i, MeasurableSet (U i) := fun _ => isOpen_ball.measurableSet
  have hcover : ⋃ i, U i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp (hF (mem_univ x))
    refine mem_iUnion.mpr ⟨e.symm ⟨z,hz⟩,?_⟩
    simpa only [U,e.apply_symm_apply] using hxz
  let P := FixedPartition.ofCover U hU hcover
  have hfront (i : Fin m) : μ (frontier (U i)) = 0 := by
    apply measure_mono_null frontier_ball_subset_sphere
    have hh := measure_level_eq_zero μ (f := fun x => dist x (e i).val)
      (r := r (e i).val) (c := 1) (θ := θ) (by norm_num) hθ0
      (by simpa only [boundaryTube,one_mul] using hrsum (e i).val)
    exact hh
  refine ⟨m,P,(fun i => disjointed_null_frontier μ U hfront i),?_,?_⟩
  · intro i x hx y hy
    have hxball := disjointed_subset U i hx
    have hyball := disjointed_subset U i hy
    change dist x (e i).val < r (e i).val at hxball
    change dist y (e i).val < r (e i).val at hyball
    have ht := dist_triangle x (e i).val y
    rw [dist_comm (e i).val y] at ht
    linarith [hrsmall (e i).val]
  · intro T hT
    have hall : ∀ i : Fin m, ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop,
        θ^n < |dist ((T^[n]) x) (e i).val-r (e i).val| := by
      intro i
      have hh := ae_orbit_eventually_away μ
        (continuous_id.dist continuous_const).measurable hT
        (r := r (e i).val) (c := 1) (θ := θ)
        (by simpa only [boundaryTube,one_mul] using hrsum (e i).val)
      simpa only [one_mul] using hh
    filter_upwards [ae_all_iff.mpr hall] with x hx
    filter_upwards [eventually_all.mpr hx] with n hn
    intro y hy i
    exact mem_disjointed_iff_of_mem_iff U
      (fun j => mem_ball_iff_of_away (hn j) hy) i

omit [OpensMeasurableSpace Z] in
/-- Outside all boundaries of a finite partition, all membership tests are
constant on one common metric neighborhood. -/
theorem exists_membership_radius {m : ℕ} (P : FixedPartition Z (Fin m))
    (x : Z) (hx : ∀ i, x ∉ frontier (P.cells i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : Z, dist x y < r →
      ∀ i, (x ∈ P.cells i ↔ y ∈ P.cells i) := by
  have hlocal : ∀ i : Fin m, ∀ᶠ y in 𝓝 x, (x ∈ P.cells i ↔ y ∈ P.cells i) := by
    intro i
    have hxi : x ∈ interior (P.cells i) ∪ interior (P.cells i)ᶜ := by
      rw [← compl_frontier_eq_union_interior]
      exact hx i
    rcases hxi with hi | hi
    · have hn : P.cells i ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hi
      filter_upwards [hn] with y hy
      exact iff_of_true (interior_subset hi) hy
    · have hn : (P.cells i)ᶜ ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hi
      filter_upwards [hn] with y hy
      exact iff_of_false (interior_subset hi) hy
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (eventually_all.mpr hlocal)
  refine ⟨r,hr,fun y hy => hball ?_⟩
  simpa only [mem_ball, dist_comm] using hy

/-- Once all finitely many early iterates are also outside the boundary, the
eventual exponential control improves to one positive radius for all iterates. -/
theorem exists_all_time_radius {m : ℕ} (P : FixedPartition Z (Fin m))
    (q : ℕ → Z) {θ : ℝ} (hθ : 0 < θ)
    (hboundary : ∀ n i, q n ∉ frontier (P.cells i))
    (heventual : ∀ᶠ n : ℕ in atTop, ∀ y, dist (q n) y < θ^n →
      ∀ i, (q n ∈ P.cells i ↔ y ∈ P.cells i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ n : ℕ, ∀ y, dist (q n) y < r*θ^n →
      ∀ i, (q n ∈ P.cells i ↔ y ∈ P.cells i) := by
  classical
  choose ρ hρ hρgood using (fun n => exists_membership_radius P (q n) (hboundary n))
  obtain ⟨N,hN⟩ := eventually_atTop.mp heventual
  let R : Unit ⊕ Fin N → ℝ := Sum.elim (fun _ => 1) (fun i => ρ i / θ^(i : ℕ))
  have hR : ∀ i, 0 < R i := by
    intro i
    rcases i with u | i
    · exact zero_lt_one
    · exact div_pos (hρ i) (pow_pos hθ _)
  have hne : (Finset.univ : Finset (Unit ⊕ Fin N)).Nonempty := ⟨Sum.inl (),Finset.mem_univ _⟩
  let r : ℝ := Finset.univ.inf' hne R
  have hr : 0 < r := (Finset.lt_inf'_iff hne).mpr (fun i _ => hR i)
  have hrone : r ≤ 1 := Finset.inf'_le R (Finset.mem_univ (Sum.inl ()))
  refine ⟨r,hr,?_⟩
  intro n y hy
  by_cases hn : n < N
  · have hrn : r ≤ ρ n / θ^n :=
      Finset.inf'_le R (Finset.mem_univ (Sum.inr (⟨n,hn⟩ : Fin N)))
    exact hρgood n y (hy.trans_le ((le_div_iff₀ (pow_pos hθ _)).mp hrn))
  · apply hN n (Nat.le_of_not_gt hn) y
    exact hy.trans_le (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hrone (pow_nonneg hθ.le n))

/-- The same actual finite partition controls every iterate with a positive
point-dependent radius, the geometric input for subordinate root atoms. -/
theorem exists_small_all_time_good_partition [CompactSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] {ε θ : ℝ}
    (hε : 0 < ε) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ m : ℕ, ∃ P : FixedPartition Z (Fin m),
      (∀ i, μ (frontier (P.cells i)) = 0) ∧
      (∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < ε) ∧
      ∀ T : Z → Z, MeasurePreserving T μ μ →
        ∀ᵐ x ∂μ, ∃ r : ℝ, 0 < r ∧
          ∀ n : ℕ, ∀ y : Z, dist ((T^[n]) x) y < r*θ^n →
            ∀ i, ((T^[n]) x ∈ P.cells i ↔ y ∈ P.cells i) := by
  obtain ⟨m,P,hnull,hmesh,hgood⟩ := exists_small_orbit_good_partition μ hε hθ0.le hθ1
  refine ⟨m,P,hnull,hmesh,?_⟩
  intro T hT
  have hb : ∀ n : ℕ, ∀ i : Fin m, ∀ᵐ x ∂μ, (T^[n]) x ∉ frontier (P.cells i) := by
    intro n i
    exact (hT.iterate n).quasiMeasurePreserving.ae
      (show ∀ᵐ y ∂μ, y ∉ frontier (P.cells i) from by
        simpa only [ae_iff,not_not] using hnull i)
  filter_upwards [hgood T hT,ae_all_iff.mpr (fun n => ae_all_iff.mpr (hb n))] with x hx hxb
  exact exists_all_time_radius P (fun n => (T^[n]) x) hθ0 hxb hx

end VV.BBEKLeafEntropyGoodPartition
