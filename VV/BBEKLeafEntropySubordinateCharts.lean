import VV.BBEKLeafEntropySubordinateTime

/-! Actual measurable subordinate codes for the joint, real, and 2-adic lower roots. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped Topology ENNReal
namespace VV.BBEKLeafEntropySubordinateCharts
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKLeafEntropyBoundary BBEKLeafEntropySafety BBEKLeafEntropySafetyCuts
  BBEKLeafEntropySubordinate BBEKLeafEntropySubordinateTime BBEKRootLeafKernel

section Construction
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

theorem compact_subordinate_codes
    (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (D : ℕ → U → U)
    (hconj : ∀ n u q, (inverseTime^[n]) (x (axis u).1 (axis u).2 • q) =
      x (axis (D n u)).1 (axis (D n u)).2 • (inverseTime^[n]) q)
    (hcontract : ∀ n u, ‖axis (D n u)‖ ≤ (1/4:ℝ)^n*‖u‖)
    (μ : Measure X) [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K)
    (hT : MeasurePreserving inverseTime μ μ) :
    ∃ C : Finset Chart, ∃ r : C → ℝ,
      Measurable (pastPlaqueCode s (fun c : C => c.val) r inverseTime) ∧
      (∀ q ∈ K, ∀ q', pastPlaqueCode s (fun c : C => c.val) r inverseTime q' =
        pastPlaqueCode s (fun c : C => c.val) r inverseTime q →
        ∃ u : U, q' = x (axis u).1 (axis u).2 • q) ∧
      (∀ᵐ q ∂μ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : U, ‖u‖ < ρ →
        pastPlaqueCode s (fun c : C => c.val) r inverseTime (x (axis u).1 (axis u).2 • q) =
          pastPlaqueCode s (fun c : C => c.val) r inverseTime q) := by
  classical
  obtain ⟨C,a,ha,r,har,hcov,hbound⟩ := compact_summable_safe_cuts μ hK
    (θ := 1/4) (by norm_num) (by norm_num)
  refine ⟨C,r,measurable_pastPlaqueCode s _ _ hT.measurable,?_,?_⟩
  · intro q hq q' he
    obtain ⟨i,hi⟩ := hcov q hq
    exact exists_root_of_pastPlaqueCode_eq s axis hs _ _ _
      ⟨i,(ha.trans (har i)).le,hi⟩ he
  · exact ae_root_ball_in_pastPlaqueCode s axis (fun p u => by rw [hs])
      μ _ r ha har (by norm_num) (by norm_num) hbound hT D hconj hcontract

end Construction

theorem compact_joint_subordinate_code (μ : Measure X) [IsFiniteMeasure μ]
    {K : Set X} (hK : IsCompact K) (hT : MeasurePreserving inverseTime μ μ) :
    ∃ C : Finset Chart, ∃ r : C → ℝ,
      Measurable (pastPlaqueCode splitCoordinates (fun c : C => c.val) r inverseTime) ∧
      (∀ q ∈ K, ∀ q', pastPlaqueCode splitCoordinates (fun c : C => c.val) r inverseTime q' =
        pastPlaqueCode splitCoordinates (fun c : C => c.val) r inverseTime q →
        ∃ u : Leaf, q' = x u.1 u.2 • q) ∧
      (∀ᵐ q ∂μ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : Leaf, ‖u‖ < ρ →
        pastPlaqueCode splitCoordinates (fun c : C => c.val) r inverseTime (x u.1 u.2 • q) =
          pastPlaqueCode splitCoordinates (fun c : C => c.val) r inverseTime q) := by
  exact compact_subordinate_codes splitCoordinates id
    (fun p u => by simp only [id_eq,leafShift,Homeomorph.apply_symm_apply])
    contractJoint inverseTime_conjugates_root norm_contractJoint_le μ hK hT

theorem compact_real_subordinate_code (μ : Measure X) [IsFiniteMeasure μ]
    {K : Set X} (hK : IsCompact K) (hT : MeasurePreserving inverseTime μ μ) :
    ∃ C : Finset Chart, ∃ r : C → ℝ,
      Measurable (pastPlaqueCode realSplit (fun c : C => c.val) r inverseTime) ∧
      (∀ q ∈ K, ∀ q', pastPlaqueCode realSplit (fun c : C => c.val) r inverseTime q' =
        pastPlaqueCode realSplit (fun c : C => c.val) r inverseTime q →
        ∃ u : ℝ, q' = x u 0 • q) ∧
      (∀ᵐ q ∂μ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : ℝ, ‖u‖ < ρ →
        pastPlaqueCode realSplit (fun c : C => c.val) r inverseTime (x u 0 • q) =
          pastPlaqueCode realSplit (fun c : C => c.val) r inverseTime q) := by
  apply compact_subordinate_codes realSplit (fun u => (u,0))
    (fun p u => by simp [leafShift,splitCoordinates,realSplit])
    contractReal inverseTime_conjugates_real _ μ hK hT
  intro n u
  simpa only [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using norm_contractReal_le n u

theorem compact_padic_subordinate_code (μ : Measure X) [IsFiniteMeasure μ]
    {K : Set X} (hK : IsCompact K) (hT : MeasurePreserving inverseTime μ μ) :
    ∃ C : Finset Chart, ∃ r : C → ℝ,
      Measurable (pastPlaqueCode padicSplit (fun c : C => c.val) r inverseTime) ∧
      (∀ q ∈ K, ∀ q', pastPlaqueCode padicSplit (fun c : C => c.val) r inverseTime q' =
        pastPlaqueCode padicSplit (fun c : C => c.val) r inverseTime q →
        ∃ u : Q2, q' = x 0 u • q) ∧
      (∀ᵐ q ∂μ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : Q2, ‖u‖ < ρ →
        pastPlaqueCode padicSplit (fun c : C => c.val) r inverseTime (x 0 u • q) =
          pastPlaqueCode padicSplit (fun c : C => c.val) r inverseTime q) := by
  apply compact_subordinate_codes padicSplit (fun u => (0,u))
    (fun p u => by simp [leafShift,splitCoordinates,padicSplit])
    contractPadic inverseTime_conjugates_padic _ μ hK hT
  intro n u
  simpa only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using (norm_contractPadic n u).le

end VV.BBEKLeafEntropySubordinateCharts
