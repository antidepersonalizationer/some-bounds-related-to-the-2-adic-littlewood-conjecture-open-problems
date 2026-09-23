import VV.BBEKFiniteCover

noncomputable section
open Set Metric
open scoped Topology
namespace VV.BBEKFiniteBowen
open BBEKDynamics BBEKQuotient BBEKBowenLift BBEKEntropyExpansive
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Every coarse finite Bowen fiber admits a fine dynamical cover whose
cardinality is independent of the window length and the base point.
The proof uses only the two endpoint displacements in a fixed compact set. -/
theorem compact_bowen_uniform_cover {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : 0 < t) :
    ∃ r : ℝ, 0 < r ∧ IsOpen (displacementRelation r) ∧
      (∀ q : X, (q,q) ∈ displacementRelation r) ∧
      ∀ E : Set (X × X), IsOpen E → (∀ z : X, (z,z) ∈ E) →
        ∃ M : ℕ, ∀ (N : ℕ) (q : X) (S : Set X),
          (∀ j ≤ N, (psi t 1)^j • q ∈ Y) →
          (∀ y ∈ S, ∀ j ≤ N,
            ((psi t 1)^j • q,(psi t 1)^j • y) ∈ displacementRelation r) →
          ∃ s : Finset X, (s : Set X) ⊆ S ∧ s.card ≤ M ∧
            ∀ y ∈ S, ∃ z ∈ s, ∀ j ≤ N,
              ((psi t 1)^j • y,(psi t 1)^j • z) ∈ E := by
  classical
  obtain ⟨r,hr,ho,hd,hlift⟩ := compact_finite_lift hY (psi t 1)
  refine ⟨r,hr,ho,hd,?_⟩
  intro E hE hdiag
  let C : Set G := closedBall 1 r
  have hC : IsCompact C := isCompact_closedBall _ _
  obtain ⟨η,hη,hact⟩ := compact_uniform_action_relation hC hY hE hdiag
  obtain ⟨M,hM⟩ := finite_cover_of_map_into_compact (P:=X) (hC.prod hC) hη
  refine ⟨M,?_⟩
  intro N q S hq hS
  have hex (y : X) : ∃ g : G, y ∈ S → ∀ j ≤ N,
      dist (forwardConjugate t j g) 1 < r ∧
      (psi t 1)^j • y = forwardConjugate t j g • ((psi t 1)^j • q) := by
    by_cases hy : y ∈ S
    · obtain ⟨g,hg⟩ := hlift N q y hq (hS y hy)
      exact ⟨g,fun _ => hg⟩
    · exact ⟨1,fun h => False.elim (hy h)⟩
  choose lift hprops using hex
  let endpoint : X → G × G := fun y => (lift y,forwardConjugate t N (lift y))
  have hep : MapsTo endpoint S (C ×ˢ C) := by
    intro y hy
    refine ⟨?_,(hprops y hy N le_rfl).1.le⟩
    have hh := (hprops y hy 0 (Nat.zero_le _)).1.le
    simpa only [forwardConjugate,pow_zero,one_mul,mul_one] using hh
  obtain ⟨s,hs,hcard,hcover⟩ := hM S endpoint hep
  refine ⟨s,hs,hcard,?_⟩
  intro y hy
  obtain ⟨z,hz,hclose⟩ := hcover y hy
  refine ⟨z,hz,?_⟩
  intro j hj
  have hzS := hs hz
  rw [(hprops y hy j hj).2,(hprops z hzS j hj).2]
  apply hact _ (hprops y hy j hj).1.le _ (hprops z hzS j hj).1.le _ (hq j hj)
  apply lt_of_le_of_lt (forwardConjugate_dist_interpolate ht (lift y) (lift z) hj)
  exact hclose

end VV.BBEKFiniteBowen
