import VV.BBEKBowenCover
import VV.BBEKEntropyNets
import VV.Entropy.BowenPartition

noncomputable section
open Set Metric Function
open scoped Topology Uniformity
namespace VV.BBEKFiniteBowen
open BBEKDynamics BBEKQuotient BBEKBowenLift BBEKEntropyExpansion BBEKEntropyNets
open ErgodicTheory.Entropy

theorem restrictedTimeMap_iterate_pow {Y : Set X} {t : ℝ}
    (hf : MapsTo (timeMap t) Y Y) (q : Y) (n : ℕ) :
    ((restrictedTimeMap hf)^[n] q : X) = (psi t 1)^n • (q : X) := by
  rw [restrictedTimeMap_iterate_coe]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    change psi t 1 • ((psi t 1)^n • (q : X)) = _
    rw [← MulAction.mul_smul,← pow_succ']

/-- The concrete homogeneous action satisfies the genuine uniform finite
Bowen-cover property used by the partition-entropy theorem. The metric is
chosen from the proved metrizability of X and has its original topology. -/
theorem compact_uniformBowenCover {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : 0 < t) (hf : MapsTo (timeMap t) Y Y) :
    letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    ∃ ρ : ℝ, 0 < ρ ∧ UniformBowenCover (restrictedTimeMap hf) ρ := by
  classical
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  obtain ⟨r,hr,ho,hd,hcov⟩ := compact_bowen_uniform_cover hY ht
  let V : Set (Y × Y) := (fun p : Y × Y => ((p.1 : X),(p.2 : X))) ⁻¹' displacementRelation r
  have hV : IsOpen V := ho.preimage (continuous_subtype_val.prodMap continuous_subtype_val)
  have huni : V ∈ 𝓤 Y := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    apply hV.mem_nhdsSet.mpr
    rintro ⟨a,b⟩ (hab : a=b)
    subst b
    exact hd a
  obtain ⟨ρ,hρ,hρV⟩ := Metric.mem_uniformity_dist.mp huni
  refine ⟨ρ,hρ,?_⟩
  intro ε hε
  let E : Set (X × X) := {p | dist p.1 p.2 < ε/2}
  have hE : IsOpen E := isOpen_lt (continuous_fst.dist continuous_snd) continuous_const
  obtain ⟨M,hM⟩ := hcov E hE (fun z => by simpa [E] using half_pos hε)
  refine ⟨M+1,by omega,?_⟩
  intro n x
  by_cases hn : n=0
  · subst n
    refine ⟨fun _ => univ,?_,?_⟩
    · intro y _; exact mem_iUnion.mpr ⟨⟨0,Nat.zero_lt_succ M⟩,mem_univ y⟩
    · intro i y hy z hz k hk; omega
  have hnpos : 0<n := Nat.pos_of_ne_zero hn
  let B : Set Y := {y | ∀ k<n, dist ((restrictedTimeMap hf)^[k] x) ((restrictedTimeMap hf)^[k] y) < ρ}
  let S : Set X := Subtype.val '' B
  have hq (j : ℕ) (_ : j ≤ n-1) : (psi t 1)^j • (x : X) ∈ Y := by
    rw [← restrictedTimeMap_iterate_pow hf x j]
    exact ((restrictedTimeMap hf)^[j] x).property
  have hS : ∀ y ∈ S, ∀ j ≤ n-1,
      ((psi t 1)^j • (x : X),(psi t 1)^j • y) ∈ displacementRelation r := by
    rintro y ⟨z,hz,rfl⟩ j hj
    have hp := @hρV ((restrictedTimeMap hf)^[j] x) ((restrictedTimeMap hf)^[j] z) (hz j (by omega))
    change (((restrictedTimeMap hf)^[j] x : X),((restrictedTimeMap hf)^[j] z : X)) ∈ displacementRelation r at hp
    simpa only [restrictedTimeMap_iterate_pow] using hp
  obtain ⟨s,hs,hcard,hfine⟩ := hM (n-1) x S hq hS
  have hsize : Fintype.card s ≤ Fintype.card (Fin (M+1)) := by
    simpa using hcard.trans (Nat.le_succ M)
  obtain ⟨index⟩ := Function.Embedding.nonempty_of_card_le hsize
  let U : Fin (M+1) → Set Y := fun i =>
    {y | ∃ z : s, index z=i ∧ ∀ k<n,
      dist (((restrictedTimeMap hf)^[k] y : Y) : X) ((psi t 1)^k • (z.val : X)) < ε/2}
  refine ⟨U,?_,?_⟩
  · intro y hy
    obtain ⟨z,hz,hclose⟩ := hfine y ⟨y,hy,rfl⟩
    refine mem_iUnion.mpr ⟨index ⟨z,hz⟩,⟨⟨z,hz⟩,rfl,?_⟩⟩
    intro k hk
    rw [restrictedTimeMap_iterate_pow]
    exact hclose k (by omega)
  · rintro i y ⟨z,hzi,hy⟩ w ⟨z',hz'i,hw⟩ k hk
    have he : z=z' := index.injective (hzi.trans hz'i.symm)
    subst z'
    change dist (((restrictedTimeMap hf)^[k] y : Y) : X)
      (((restrictedTimeMap hf)^[k] w : Y) : X) < ε
    calc
      _ ≤ dist (((restrictedTimeMap hf)^[k] y : Y) : X) ((psi t 1)^k • (z.val : X)) +
        dist ((psi t 1)^k • (z.val : X)) (((restrictedTimeMap hf)^[k] w : Y) : X) := dist_triangle _ _ _
      _ < ε/2+ε/2 := add_lt_add (hy k hk) (by simpa only [dist_comm] using hw k hk)
      _ = ε := by ring

end VV.BBEKFiniteBowen

