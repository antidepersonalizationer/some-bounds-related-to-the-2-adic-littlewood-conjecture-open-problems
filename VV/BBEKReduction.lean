import VV.BBEKOrbit
import VV.BBEKParameter
import VV.P7BoxCover

/-! The concrete dynamical reduction in BBEK Section 5.
The Diophantine set embeds isometrically into the compact parameter chart,
and Proposition 5.1 places it in the actual cone-trapped subset. The zero
box dimension of that subset is supplied in `BBEKFinal`, using the one
explicitly admitted EL low-entropy core. No theorem is admitted here. -/

noncomputable section
open Set Filter
open scoped Topology

namespace VV.BBEKReduction
open BBEKDynamics BBEKQuotient BBEKOrbit BBEKShortVector P7AdicLimits P7BoxCover

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def trapped (δ : ℝ) : Set G :=
  {g | coneOrbit (mk g) ⊆ K δ}

theorem mem_trapped_iff (δ : ℝ) (g : G) : g ∈ trapped δ ↔
    ∀ t : ℝ, ∀ n : ℤ, Cone t n → psi t n • mk g ∈ K δ := by
  constructor
  · intro h t n hc
    exact h ⟨t,n,hc,rfl⟩
  · rintro h q ⟨t,n,hc,rfl⟩
    exact h t n hc

theorem isClosed_trapped (δ : ℝ) : IsClosed (trapped δ) := by
  have he : trapped δ = ⋂ t : ℝ, ⋂ n : ℤ, ⋂ (_h : Cone t n),
      (fun g : G => psi t n • mk g) ⁻¹' K δ := by
    ext g
    simp only [mem_iInter,mem_preimage]
    exact mem_trapped_iff δ g
  rw [he]
  exact isClosed_iInter fun t => isClosed_iInter fun n => isClosed_iInter fun _ =>
    (isClosed_K δ).preimage (continuous_const.smul continuous_mk)

theorem trapped_forward {δ : ℝ} {g : G} (hg : g ∈ trapped δ)
    {t : ℝ} {n : ℤ} (hc : Cone t n) : psi t n * g ∈ trapped δ := by
  apply (mem_trapped_iff δ _).mpr
  intro s m hs
  have hh := (mem_trapped_iff δ g).mp hg (s+t) (m+n) (hs.add hc)
  simpa only [smul_mk,psi_add,mul_assoc] using hh

/-- The subset to which the unstable-direction entropy theorem must apply.
It lies in the actual group, with its maximum metric, not an abstract space. -/
def trappedParameters (δ : ℝ) : Set G := parameterImage ∩ trapped δ

theorem trappedParameters_compact (δ : ℝ) : IsCompact (trappedParameters δ) :=
  parameterImage_compact.inter_right (isClosed_trapped δ)

def parameterEmbedding (a : ℝ × ℤ_[2]) : G := x a.1 (a.2 : Q2)

theorem parameterEmbedding_isometry : Isometry parameterEmbedding := by
  apply Isometry.of_dist_eq
  intro a b
  calc
    dist (parameterEmbedding a) (parameterEmbedding b) =
        dist (a.1,(a.2:Q2)) (b.1,(b.2:Q2)) :=
      isometry_x.dist_eq (a.1,(a.2:Q2)) (b.1,(b.2:Q2))
    _ = dist a b := by
      rw [Prod.dist_eq,Prod.dist_eq]
      congr 1

theorem joint_mapsTo_trappedParameters {ε : ℝ} (hε : 0 < ε) :
    MapsTo parameterEmbedding (JointBadlyApproximable ε)
      (trappedParameters (shortRadius ε)) := by
  rintro ⟨u,v⟩ h
  constructor
  · refine ⟨(u,(v:Q2)),?_,rfl⟩
    apply (mem_parameterBox _).mpr
    exact ⟨h.1.1,h.1.2,PadicInt.norm_le_one v⟩
  · exact proposition51 hε h

theorem geometricZeroUpperBox_pullback {A B : Type*}
    [PseudoMetricSpace A] [PseudoMetricSpace B] {S : Set A} {T : Set B}
    {f : A → B} (hf : Isometry f) (hmap : MapsTo f S T)
    (hT : GeometricZeroUpperBox T) : GeometricZeroUpperBox S := by
  intro ρ t hρ0 hρ1 ht
  filter_upwards [hT ρ t hρ0 hρ1 ht] with n hn
  obtain ⟨m,U,hcover,hsmall,hcard⟩ := hn
  refine ⟨m,fun i => f ⁻¹' U i,?_,?_,hcard⟩
  · intro a ha
    exact hcover (f a) (hmap ha)
  · intro i a ha b hb
    rw [← hf.dist_eq a b]
    exact hsmall i (f a) ha (f b) hb

/-- Reusable reduction from zero upper box dimension of the actual trapped
unstable parameters. `BBEKFinal.trappedParameters_zero_upper_box` supplies
this input internally, with the one named EL-core admission. -/
theorem BBEK_of_trapped_zero_box
    (hbox : ∀ δ : ℝ, 0 < δ → GeometricZeroUpperBox (trappedParameters δ)) :
    BBEKTheorem42 := by
  intro ε hε
  exact geometricZeroUpperBox_pullback parameterEmbedding_isometry
    (joint_mapsTo_trappedParameters hε) (hbox _ (shortRadius_pos hε))

theorem problem7_of_trapped_zero_box
    (hbox : ∀ δ : ℝ, 0 < δ → GeometricZeroUpperBox (trappedParameters δ)) :
    Problem7.Statement :=
  problem7_of_BBEK (BBEK_of_trapped_zero_box hbox)

end VV.BBEKReduction
