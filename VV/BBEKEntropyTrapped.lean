import VV.BBEKEntropyBox
import VV.BBEKMahler
import VV.BBEKReduction

/-! The actual compact cone-trapped quotient set and the first, purely
topological part of EK Lemma 4.2 for the BBEK system. -/

noncomputable section
open Set Filter
open scoped Topology

namespace VV.BBEKEntropyTrapped
open BBEKDynamics BBEKQuotient BBEKOrbit BBEKMahler BBEKReduction
open BBEKEntropyExpansion BBEKEntropyNets BBEKEntropyBox P7BoxCover

def trappedQuotient (δ : ℝ) : Set X := {q | coneOrbit q ⊆ K δ}

theorem trappedQuotient_subset_K (δ : ℝ) : trappedQuotient δ ⊆ K δ :=
  fun q hq => hq (mem_coneOrbit_self q)

theorem isClosed_trappedQuotient (δ : ℝ) : IsClosed (trappedQuotient δ) := by
  have he : trappedQuotient δ = ⋂ t : ℝ, ⋂ n : ℤ, ⋂ (_ : Cone t n),
      (fun q : X => psi t n • q) ⁻¹' K δ := by
    ext q
    simp only [trappedQuotient,mem_setOf_eq,mem_iInter,mem_preimage]
    constructor
    · intro h t n hc
      exact h ⟨t,n,hc,rfl⟩
    · rintro h _ ⟨t,n,hc,rfl⟩
      exact h t n hc
  rw [he]
  exact isClosed_iInter fun t => isClosed_iInter fun n => isClosed_iInter fun _ =>
    (isClosed_K δ).preimage (continuous_const.smul continuous_id)

theorem compact_trappedQuotient {δ : ℝ} (hδ : 0 < δ) : IsCompact (trappedQuotient δ) :=
  (compact_K hδ).of_isClosed_subset (isClosed_trappedQuotient δ) (trappedQuotient_subset_K δ)

theorem trappedQuotient_forward {δ t : ℝ} {n : ℤ} (hc : Cone t n) :
    Set.MapsTo (fun q : X => psi t n • q) (trappedQuotient δ) (trappedQuotient δ) := by
  intro q hq z hz
  obtain ⟨s,m,hs,rfl⟩ := hz
  apply hq
  refine ⟨s+t,m+n,hs.add hc,?_⟩
  rw [psi_add,MulAction.mul_smul]

theorem trappedTimeForward (δ : ℝ) :
    Set.MapsTo (timeMap time0) (trappedQuotient δ) (trappedQuotient δ) :=
  trappedQuotient_forward time0_cone_unstable.1

def trappedCoordinates (δ : ℝ) : Set (ℝ × Q2) :=
  parameterBox ∩ {z | x z.1 z.2 ∈ trapped δ}

theorem trappedCoordinates_subset_box (δ : ℝ) : trappedCoordinates δ ⊆ parameterBox :=
  fun _ hz => hz.1

theorem trappedCoordinates_image (δ : ℝ) :
    (fun z : ℝ × Q2 => x z.1 z.2) '' trappedCoordinates δ = trappedParameters δ := by
  ext g
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,hz.1,rfl⟩,hz.2⟩
  · rintro ⟨⟨z,hz,rfl⟩,ht⟩
    exact ⟨z,⟨hz,ht⟩,rfl⟩

theorem trappedCoordinates_map (δ : ℝ) :
    ∀ z ∈ trappedCoordinates δ, x z.1 z.2 • basePoint ∈ trappedQuotient δ := by
  intro z hz
  simpa only [basePoint,smul_mk,mul_one] using hz.2

/-- The entropy in this statement is mathlib's cover entropy for the
time-(log 2+1,1) action on the literal compact cone-trapped quotient set. -/
def trappedEntropy (δ : ℝ) (hδ : 0 < δ) : EReal :=
  compactEntropy (trappedQuotient δ) (compact_trappedQuotient hδ) (trappedTimeForward δ)

theorem trapped_zero_box_of_entropy_nonpos {δ : ℝ} (hδ : 0 < δ)
    (hentropy : trappedEntropy δ hδ ≤ 0) : GeometricZeroUpperBox (trappedParameters δ) := by
  have hcoords : GeometricZeroUpperBox (trappedCoordinates δ) :=
    geometricZeroUpperBox_of_entropy_nonpos (compact_trappedQuotient hδ)
      time0_gt_log_two.le (trappedTimeForward δ) hentropy basePoint
      parameterBox_compact (trappedCoordinates_subset_box δ) (trappedCoordinates_map δ)
  have himage := geometricZeroUpperBox_image hcoords (fun z : ℝ × Q2 => x z.1 z.2)
    (fun z w => (isometry_x.dist_eq z w).le)
  rwa [trappedCoordinates_image] at himage

/-- The complete pure-topology implication needed from EK Lemma 4.2 in
the BBEK application. No box-dimension, separation, compactness, or entropy
conclusion is inserted as an extra hypothesis. -/
theorem trappedEntropy_pos_of_not_zero_box {δ : ℝ} (hδ : 0 < δ)
    (hbox : ¬ GeometricZeroUpperBox (trappedParameters δ)) :
    0 < trappedEntropy δ hδ := by
  by_contra! h
  exact hbox (trapped_zero_box_of_entropy_nonpos hδ h)

end VV.BBEKEntropyTrapped
