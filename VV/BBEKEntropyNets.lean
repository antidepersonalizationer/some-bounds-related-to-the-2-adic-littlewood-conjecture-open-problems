import VV.BBEKEntropyExpansion
import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import Mathlib.Topology.UniformSpace.OfCompactT2
import Mathlib.Topology.UniformSpace.Compact

/-! The concrete first-exit geometry produces actual Bowen-Dinaburg nets. -/

noncomputable section
open Set Topology Dynamics
open scoped Topology Uniformity

namespace VV.BBEKEntropyNets
open BBEKDynamics BBEKQuotient BBEKEntropyExpansion

theorem card_le_netMaxcard_of_separating_map {P Z : Type*} (s : Finset P)
    (f : P → Z) (T : Z → Z) (V E : Set (Z × Z)) (n : ℕ)
    (hV : IsSymmetricRel V) (hcomp : V ○ V ⊆ E) (hdiag : ∀ z : Z, (z,z) ∈ E)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ k < n, (T^[k] (f b),T^[k] (f a)) ∉ E) :
    (s.card : ℕ∞) ≤ netMaxcard T Set.univ V n := by
  classical
  have hi : Set.InjOn f (s : Set P) := by
    intro a ha b hb he
    by_contra hab
    obtain ⟨k,hk,hfar⟩ := hsep a ha b hb hab
    exact hfar (by rw [he]; exact hdiag _)
  have hnet : IsDynNetIn T Set.univ V n (s.image f : Set Z) := by
    refine ⟨subset_univ _,?_⟩
    intro a ha b hb hab
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    have huv : u ≠ v := fun he => hab (congrArg f he)
    obtain ⟨k,hk,hfar⟩ := hsep u hu v hv huv
    apply Set.disjoint_left.mpr
    intro z hza hzb
    have hnear := mem_ball_dynEntourage_comp T n hV (f u) (f v) ⟨z,hza,hzb⟩
    have hp : (T^[k] (f v),T^[k] (f u)) ∈ V ○ V :=
      mem_dynEntourage.mp hnear k hk
    exact hfar (hcomp hp)
  have hcard := hnet.card_le_netMaxcard
  rw [Finset.card_image_iff.mpr hi] at hcard
  exact hcard

def compactUniformSpace (Y : Set X) (hY : IsCompact Y) : UniformSpace Y := by
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  exact uniformSpaceOfCompactT2

def restrictedTimeMap {Y : Set X} {t : ℝ}
    (hforward : Set.MapsTo (timeMap t) Y Y) : Y → Y :=
  fun q => ⟨timeMap t q,hforward q.property⟩

@[simp] theorem restrictedTimeMap_iterate_coe {Y : Set X} {t : ℝ}
    (hforward : Set.MapsTo (timeMap t) Y Y) (q : Y) (n : ℕ) :
    ((restrictedTimeMap hforward)^[n] q : X) = (timeMap t)^[n] q := by
  have h : Function.Semiconj ((↑) : Y → X) (restrictedTimeMap hforward) (timeMap t) :=
    fun _ => rfl
  exact h.iterate_right n q

theorem restrictedTimeMap_continuous {Y : Set X} {t : ℝ}
    (hforward : Set.MapsTo (timeMap t) Y Y) : Continuous (restrictedTimeMap hforward) :=
  ((timeMap_continuous t).comp continuous_subtype_val).subtype_mk _

/-- Finite unstable parameter packings inject into genuine dynamical nets
in the compact invariant set. The common entourage is constructed from
compactness and first-exit geometry, rather than supplied as an input. -/
theorem compact_parameter_card_le_net {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : Real.log 2 ≤ t) (hforward : Set.MapsTo (timeMap t) Y Y) :
    letI : UniformSpace Y := compactUniformSpace Y hY
    ∃ R : ℝ, 0 < R ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set (Y × Y), V ∈ 𝓤 Y ∧
      ∀ (q : X) (s : Finset (ℝ × Q2)) (n : ℕ), 0 < n →
        (∀ z ∈ s, x z.1 z.2 • q ∈ Y) →
        (∀ z ∈ s, ∀ w ∈ s, dist z w ≤ R) →
        (∀ z ∈ s, ∀ w ∈ s, z ≠ w → ε ≤ (4 : ℝ)^(n-1) * dist z w) →
        (s.card : ℕ∞) ≤ netMaxcard (restrictedTimeMap hforward) Set.univ V n := by
  classical
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  letI : UniformSpace Y := compactUniformSpace Y hY
  obtain ⟨R,hR,ε,hε,E,hE,hdiag,hsep⟩ := compact_first_exit_separation hY ht
  let EY : Set (Y × Y) := (fun p : Y × Y => ((p.1 : X),(p.2 : X))) ⁻¹' E
  have hEY : IsOpen EY :=
    hE.preimage (continuous_subtype_val.prodMap continuous_subtype_val)
  have hdiagY : ∀ z : Y, (z,z) ∈ EY := fun z => hdiag z
  have hEYuni : EY ∈ 𝓤 Y := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    apply hEY.mem_nhdsSet.mpr
    rintro ⟨a,b⟩ (hab : a = b)
    subst b
    exact hdiagY a
  obtain ⟨V,hV,hVsym,hVcomp⟩ := comp_symm_mem_uniformity_sets hEYuni
  refine ⟨R,hR,ε,hε,V,hV,?_⟩
  intro q s n hn hs hdiam hpack
  let f : {z // z ∈ s} → Y := fun z => ⟨x z.val.1 z.val.2 • q,hs z z.property⟩
  have hc := card_le_netMaxcard_of_separating_map s.attach f
    (restrictedTimeMap hforward) V EY n hVsym hVcomp hdiagY ?_
  · simpa only [Finset.card_attach] using hc
  · intro a _ b _ hab
    have hab' : (a : ℝ × Q2) ≠ b := fun he => hab (Subtype.ext he)
    have htrapped : ∀ k ≤ n-1, (timeMap t)^[k] (x b.val.1 b.val.2 • q) ∈ Y := by
      intro k _
      have hh := ((restrictedTimeMap hforward)^[k] (f b)).property
      simpa only [restrictedTimeMap_iterate_coe,f] using hh
    obtain ⟨j,hjn,hfar⟩ := hsep q a b (n-1)
      (hdiam a a.property b b.property) htrapped (hpack a a.property b b.property hab')
    refine ⟨j,by omega,?_⟩
    change (((restrictedTimeMap hforward)^[j] (f b) : X),
      ((restrictedTimeMap hforward)^[j] (f a) : X)) ∉ E
    simpa only [restrictedTimeMap_iterate_coe,f] using hfar

/-- The usual maximal finite packing cardinal, with an explicit separation
scale in the original real/2-adic parameter metric. -/
def IsParameterPacking (S : Set (ℝ × Q2)) (η : ℝ) (s : Finset (ℝ × Q2)) : Prop :=
  (s : Set (ℝ × Q2)) ⊆ S ∧
    ∀ z ∈ s, ∀ w ∈ s, z ≠ w → η ≤ dist z w

def parameterPackingCard (S : Set (ℝ × Q2)) (η : ℝ) : ℕ∞ :=
  ⨆ (s : Finset (ℝ × Q2)) (_ : IsParameterPacking S η s), (s.card : ℕ∞)

def compactEntropy (Y : Set X) (hY : IsCompact Y) {t : ℝ}
    (hforward : Set.MapsTo (timeMap t) Y Y) : EReal :=
  letI : UniformSpace Y := compactUniformSpace Y hY
  coverEntropy (restrictedTimeMap hforward) Set.univ

/-- Exponential packing growth in an actual local unstable parameter set
is bounded by the usual topological entropy on the compact invariant set.
The fixed prefactor epsilon does not assert any packing growth; it is the
separation constant constructed by the geometry. -/
theorem local_packing_growth_le_entropy {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : Real.log 2 ≤ t) (hforward : Set.MapsTo (timeMap t) Y Y) :
    ∃ R : ℝ, 0 < R ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ (q : X) (S : Set (ℝ × Q2)),
      (∀ z ∈ S, x z.1 z.2 • q ∈ Y) →
      (∀ z ∈ S, ∀ w ∈ S, dist z w ≤ R) →
      ExpGrowth.expGrowthSup (fun n : ℕ =>
        (parameterPackingCard S (ε / (4 : ℝ)^(n-1))).toENNReal) ≤
          compactEntropy Y hY hforward := by
  letI : UniformSpace Y := compactUniformSpace Y hY
  obtain ⟨R,hR,ε,hε,V,hV,hcard⟩ := compact_parameter_card_le_net hY ht hforward
  refine ⟨R,hR,ε,hε,?_⟩
  intro q S hSY hdiam
  have hle : ∀ n : ℕ, 1 ≤ n → parameterPackingCard S (ε / (4 : ℝ)^(n-1)) ≤
      netMaxcard (restrictedTimeMap hforward) Set.univ V n := by
    intro n hn
    apply iSup₂_le
    intro s hs
    apply hcard q s n (by omega)
    · exact fun z hz => hSY z (hs.1 hz)
    · exact fun z hz w hw => hdiam z (hs.1 hz) w (hs.1 hw)
    · intro z hz w hw hne
      have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 4^(n-1))).mp (hs.2 z hz w hw hne)
      simpa only [mul_comm] using hh
  have hgrowth := ExpGrowth.expGrowthSup_eventually_monotone
    (show (fun n : ℕ => (parameterPackingCard S (ε / (4 : ℝ)^(n-1))).toENNReal) ≤ᶠ[Filter.atTop]
      (fun n : ℕ => (netMaxcard (restrictedTimeMap hforward) Set.univ V n).toENNReal) from
      (Filter.eventually_ge_atTop 1).mono fun n hn => ENat.toENNReal_mono (hle n hn))
  exact hgrowth.trans (netEntropyEntourage_le_coverEntropy (restrictedTimeMap hforward) Set.univ hV)

end VV.BBEKEntropyNets
