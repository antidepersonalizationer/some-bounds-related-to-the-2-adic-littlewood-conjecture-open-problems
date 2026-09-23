import VV.Entropy.BadSymbol
import VV.Entropy.FixedRefinement

/-! Relative Bowen covers control the entropy of compact-core names. -/

noncomputable section
open MeasureTheory Function Filter Set
open scoped ENNReal Topology

namespace ErgodicTheory.Entropy

variable {X I J : Type*} [MeasurableSpace X]

def FixedPartition.join [Fintype I] [Fintype J]
    (P : FixedPartition X I) (Q : FixedPartition X J) : FixedPartition X (I × J) where
  cells a := P.cells a.1 ∩ Q.cells a.2
  measurable a := (P.measurable a.1).inter (Q.measurable a.2)
  disjoint := by
    intro a b hab
    by_cases hfirst : a.1 = b.1
    · have hsecond : a.2 ≠ b.2 := fun h => hab (Prod.ext hfirst h)
      exact (Q.disjoint hsecond).mono inter_subset_right inter_subset_right
    · exact (P.disjoint hfirst).mono inter_subset_left inter_subset_left
  cover := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (P.cover ▸ mem_univ x)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (Q.cover ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨(i,j),hi,hj⟩

def binaryPartition (B : Set X) (hB : MeasurableSet B) : FixedPartition X Bool where
  cells b := if b then B else Bᶜ
  measurable b := by cases b <;> simp [hB, hB.compl]
  disjoint := by
    intro a b hab
    cases a <;> cases b <;> simp_all [Function.onFun, Set.disjoint_left]
  cover := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    by_cases hx : x ∈ B
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩

theorem binaryPartition_mem_iff {B : Set X} (hB : MeasurableSet B) (b : Bool) (x : X) :
    x ∈ (binaryPartition B hB).cells b ↔ (x ∈ B ↔ b = true) := by
  cases b <;> simp [binaryPartition]

section Metric
variable [PseudoMetricSpace X]

/-- Uniformly bounded fine covers of finite coarse Bowen balls.  This
geometric property is verified separately for the concrete homogeneous
system; the statements below establish its measure-theoretic consequences. -/
def UniformBowenCover (T : X → X) (r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, ∀ x : X,
    ∃ U : Fin M → Set X,
      {y | ∀ k < n, dist ((T^[k]) x) ((T^[k]) y) < r} ⊆ ⋃ i, U i ∧
      ∀ i, ∀ y ∈ U i, ∀ z ∈ U i, ∀ k < n,
        dist ((T^[k]) y) ((T^[k]) z) < ε

/-- Close orbit names with identical exceptional-position patterns agree
when all ordinary symbols have uniformly separated cores. -/
theorem core_names_eq_of_close [Fintype J]
    (R : FixedPartition X (Option J)) {T : X → X} {η : ℝ}
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ R.cells (some i), ∀ y ∈ R.cells (some j), η ≤ dist x y)
    {n : ℕ} {a b : Fin n → Option J} {x y : X}
    (hx : x ∈ ksJoinCells R.cells T n a) (hy : y ∈ ksJoinCells R.cells T n b)
    (hbad : ∀ k < n, (T^[k]) x ∈ R.cells none ↔ (T^[k]) y ∈ R.cells none)
    (hclose : ∀ k < n, dist ((T^[k]) x) ((T^[k]) y) < η) : a = b := by
  classical
  funext k
  have hxk := mem_iInter.mp hx k
  have hyk := mem_iInter.mp hy k
  have hbk := hbad k.val k.isLt
  have hck := hclose k.val k.isLt
  cases ha : a k with
  | none =>
    have hxnone : (T^[k.val]) x ∈ R.cells none := by simpa only [ha] using hxk
    have hynone := hbk.mp hxnone
    cases hb : b k with
    | none => rfl
    | some j =>
      have hysome : (T^[k.val]) y ∈ R.cells (some j) := by simpa only [hb] using hyk
      exact False.elim (Set.disjoint_left.mp (R.disjoint (by simp : (none : Option J) ≠ some j))
        hynone hysome)
  | some i =>
    have hxsome : (T^[k.val]) x ∈ R.cells (some i) := by simpa only [ha] using hxk
    cases hb : b k with
    | none =>
      have hynone : (T^[k.val]) y ∈ R.cells none := by simpa only [hb] using hyk
      exact False.elim (Set.disjoint_left.mp (R.disjoint (by simp : (none : Option J) ≠ some i))
        (hbk.mpr hynone) hxsome)
    | some j =>
      have hysome : (T^[k.val]) y ∈ R.cells (some j) := by simpa only [hb] using hyk
      by_cases hij : i = j
      · exact congrArg some hij
      · exact False.elim (hck.not_le (hsep i j hij _ hxsome _ hysome))

/-- A fixed coarse name together with its bad-position pattern has at most
as many core names as there are fine Bowen-cover elements. -/
theorem core_name_fiber_count [Fintype I] [Fintype J]
    {μ : Measure X} (P : FixedPartition X I) (R : FixedPartition X (Option J))
    {T : X → X} {r η : ℝ} (hmesh : ∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < r)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ R.cells (some i), ∀ y ∈ R.cells (some j), η ≤ dist x y)
    (M : ℕ) (hcover : ∀ n : ℕ, ∀ x : X, ∃ U : Fin M → Set X,
      {y | ∀ k < n, dist ((T^[k]) x) ((T^[k]) y) < r} ⊆ ⋃ i, U i ∧
      ∀ i, ∀ y ∈ U i, ∀ z ∈ U i, ∀ k < n, dist ((T^[k]) y) ((T^[k]) z) < η)
    (n : ℕ) (a : Fin n → I × Bool) :
    (Finset.univ.filter (fun b : Fin n → Option J =>
      μ (ksJoinCells (P.join (binaryPartition (R.cells none) (R.measurable none))).cells T n a ∩
        ksJoinCells R.cells T n b) ≠ 0)).card ≤ M := by
  classical
  let C := P.join (binaryPartition (R.cells none) (R.measurable none))
  let S := Finset.univ.filter (fun b : Fin n → Option J =>
    μ (ksJoinCells C.cells T n a ∩ ksJoinCells R.cells T n b) ≠ 0)
  change S.card ≤ M
  by_cases hempty : S = ∅
  · simp [hempty]
  obtain ⟨b₀,hb₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨x,hxC,hxR⟩ := nonempty_of_measure_ne_zero (Finset.mem_filter.mp hb₀).2
  obtain ⟨U,hU,hdiam⟩ := hcover n x
  have hpoint : ∀ b : S, ∃ y, y ∈ ksJoinCells C.cells T n a ∧ y ∈ ksJoinCells R.cells T n b :=
    fun b => nonempty_of_measure_ne_zero (Finset.mem_filter.mp b.property).2
  choose y hyC hyR using hpoint
  have hidx : ∀ b : S, ∃ i : Fin M, y b ∈ U i := by
    intro b
    apply mem_iUnion.mp
    apply hU
    intro k hk
    have hxk := mem_iInter.mp hxC (⟨k,hk⟩ : Fin n)
    have hyk := mem_iInter.mp (hyC b) (⟨k,hk⟩ : Fin n)
    exact hmesh (a ⟨k,hk⟩).1 _ hxk.1 _ hyk.1
  choose idx hidx using hidx
  have hinj : Function.Injective idx := by
    intro b c heq
    apply Subtype.ext
    apply core_names_eq_of_close R hsep (hyR b) (hyR c)
    · intro k hk
      have hb := (mem_iInter.mp (hyC b) (⟨k,hk⟩ : Fin n)).2
      have hc := (mem_iInter.mp (hyC c) (⟨k,hk⟩ : Fin n)).2
      exact (binaryPartition_mem_iff (R.measurable none) _ _).mp hb |>.trans
        ((binaryPartition_mem_iff (R.measurable none) _ _).mp hc).symm
    · intro k hk
      exact hdiam (idx b) _ (hidx b) _ (heq ▸ hidx c) k hk
  have hc := Fintype.card_le_of_injective idx hinj
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

/-- Uniform finite Bowen covers imply that only the bad-position process
can add entropy beyond the coarse partition. -/
theorem coreEntropy_le_coarse_add_binary [Fintype I] [Fintype J]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) (P : FixedPartition X I) (R : FixedPartition X (Option J))
    {r : ℝ} (hcover : UniformBowenCover T r)
    (hmesh : ∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < r)
    {η : ℝ} (hη : 0 < η)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ R.cells (some i), ∀ y ∈ R.cells (some j), η ≤ dist x y) :
    ksEntropyPartition hT (R.toMeasurePartition μ) ≤
      ksEntropyPartition hT (P.toMeasurePartition μ) +
        entropy μ (binaryPartition (R.cells none) (R.measurable none)).cells := by
  classical
  obtain ⟨M,hM,hfine⟩ := hcover η hη
  let B := binaryPartition (R.cells none) (R.measurable none)
  let C := P.join B
  have hle : ksEntropyPartition hT (R.toMeasurePartition μ) ≤
      ksEntropyPartition hT (C.toMeasurePartition μ) :=
    ksEntropyPartition_le_of_subexponential_fibers hT
      (C.toMeasurePartition μ) (R.toMeasurePartition μ) (fun _ => M) (fun _ => hM)
      (core_name_fiber_count P R hmesh hsep M hfine)
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log M))
  have hjoin := ksEntropyPartition_join_le hT (P.toMeasurePartition μ) (B.toMeasurePartition μ)
  have hB := ksEntropyPartition_le_entropy hT (B.toMeasurePartition μ)
  exact hle.trans (hjoin.trans (add_le_add_left hB _))

end Metric
end ErgodicTheory.Entropy


