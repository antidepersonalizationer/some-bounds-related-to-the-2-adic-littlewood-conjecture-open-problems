import VV.Entropy.FiberCount

/-! The entropy cost of one exceptional symbol in a finite observable. -/

noncomputable section
open MeasureTheory Function Filter Set
open scoped ENNReal Topology

namespace ErgodicTheory.Entropy

variable {X I : Type*} [MeasurableSpace X] [Fintype I] [DecidableEq I]

/-- The marginal mass of any coordinate of a dynamical name is its original
cell mass under an invariant probability. -/
theorem dynJoin_symbol_mass {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (P : FixedPartition X I)
    (n : ℕ) (k : Fin n) (i : I) :
    (∑ a : Fin n → I, if a k = i then (μ (ksJoinCells P.cells T n a)).toReal else 0) =
      (μ (P.cells i)).toReal := by
  classical
  let A := (T^[k.val]) ⁻¹' P.cells i
  have hA : MeasurableSet A := (P.measurable i).preimage (hT.iterate k.val).measurable
  have hrow := ((P.dynJoin hT.measurable n).toMeasurePartition μ).measure_eq_sum_inter hA
  have hcell : ∀ a : Fin n → I, μ (A ∩ ksJoinCells P.cells T n a) =
      if a k = i then μ (ksJoinCells P.cells T n a) else 0 := by
    intro a
    have hsub : ksJoinCells P.cells T n a ⊆ (T^[k.val]) ⁻¹' P.cells (a k) :=
      iInter_subset _ k
    by_cases ha : a k = i
    · rw [if_pos ha, inter_eq_right.mpr (by simpa only [A, ha] using hsub)]
    · rw [if_neg ha]
      apply measure_mono_null (inter_subset_inter_right A hsub)
      have hd := (P.disjoint (Ne.symm ha)).preimage (T^[k.val])
      rw [show A = (T^[k.val]) ⁻¹' P.cells i from rfl,
        disjoint_iff_inter_eq_empty.mp hd, measure_empty]
  have hμA : μ A = μ (P.cells i) :=
    (hT.iterate k.val).measure_preimage (P.measurable i).nullMeasurableSet
  rw [hμA] at hrow
  rw [hrow, ENNReal.toReal_sum (fun a _ => measure_ne_top μ _)]
  apply Finset.sum_congr rfl
  intro a ha
  change _ = (μ (A ∩ ksJoinCells P.cells T n a)).toReal
  rw [hcell]
  split_ifs <;> simp

/-- Expected number of occurrences of a symbol in an `n`-name is exactly
`n` times its probability. -/
theorem dynJoin_expected_symbol_count {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (P : FixedPartition X I)
    (n : ℕ) (i : I) :
    (∑ a : Fin n → I, (μ (ksJoinCells P.cells T n a)).toReal *
      ((Finset.univ.filter (fun k => a k = i)).card : ℝ)) =
      (n : ℝ) * (μ (P.cells i)).toReal := by
  classical
  have hc : ∀ a : Fin n → I,
      ((Finset.univ.filter (fun k => a k = i)).card : ℝ) =
        ∑ k : Fin n, if a k = i then (1 : ℝ) else 0 := by
    intro a
    simp
  simp_rw [hc, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp_rw [dynJoin_symbol_mass hT P n]
  simp

/-- A nonexceptional coarse symbol determines the fine symbol.  Therefore
only exceptional positions contribute choices to a conditional name. -/
theorem dynJoin_fiber_count_of_bad_symbol {μ : Measure X}
    (Q : FixedPartition X I) (R : FixedPartition X (Option I))
    (hcore : ∀ i, R.cells (some i) ⊆ Q.cells i)
    (T : X → X) (n : ℕ) (a : Fin n → Option I) :
    (Finset.univ.filter (fun b : Fin n → I =>
      μ (ksJoinCells R.cells T n a ∩ ksJoinCells Q.cells T n b) ≠ 0)).card ≤
        Fintype.card I ^ (Finset.univ.filter (fun k => a k = none)).card := by
  classical
  let allowed : Fin n → Finset I := fun k => (a k).elim Finset.univ (fun i => {i})
  have hsub : (Finset.univ.filter (fun b : Fin n → I =>
      μ (ksJoinCells R.cells T n a ∩ ksJoinCells Q.cells T n b) ≠ 0)) ⊆
        Fintype.piFinset allowed := by
    intro b hb
    have hmass := (Finset.mem_filter.mp hb).2
    obtain ⟨x, hxR, hxQ⟩ := nonempty_of_measure_ne_zero hmass
    apply Fintype.mem_piFinset.mpr
    intro k
    cases ha : a k with
    | none => simp [allowed, ha]
    | some i =>
      have hx1 : (T^[k.val]) x ∈ Q.cells i :=
        hcore i (by simpa only [ha] using Set.mem_iInter.mp hxR k)
      have hx2 : (T^[k.val]) x ∈ Q.cells (b k) := Set.mem_iInter.mp hxQ k
      have heq : b k = i := by
        by_contra hne
        exact Set.disjoint_left.mp (Q.disjoint hne) hx2 hx1
      simp [allowed, ha, heq]
  refine (Finset.card_le_card hsub).trans_eq ?_
  rw [Fintype.card_piFinset]
  have heq : (∏ k : Fin n, (allowed k).card) =
      ∏ k : Fin n, if a k = none then Fintype.card I else 1 := by
    apply Finset.prod_congr rfl
    intro k hk
    cases ha : a k <;> simp [allowed, ha]
  rw [heq, ← Finset.prod_filter, Finset.prod_const]

/-- Replacing the original symbols by compact-core symbols and one bad symbol
costs at most the bad-set probability times the log alphabet size in entropy. -/
theorem ksEntropyPartition_le_bad_symbol [Nonempty I]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ)
    (Q : FixedPartition X I) (R : FixedPartition X (Option I))
    (hcore : ∀ i, R.cells (some i) ⊆ Q.cells i) :
    ksEntropyPartition hT (Q.toMeasurePartition μ) ≤
      ksEntropyPartition hT (R.toMeasurePartition μ) +
        (μ (R.cells none)).toReal * Real.log (Fintype.card I) := by
  classical
  have hfinite : ∀ n : ℕ,
      ksEntropySeq hT (Q.toMeasurePartition μ) n ≤
        ksEntropySeq hT (R.toMeasurePartition μ) n +
          (n : ℝ) * (μ (R.cells none)).toReal * Real.log (Fintype.card I) := by
    intro n
    have h := entropy_le_add_sum_log_of_fiber_counts
      (ksJoin hT (R.toMeasurePartition μ) n) (ksJoin hT (Q.toMeasurePartition μ) n)
      (fun a => Fintype.card I ^ (Finset.univ.filter (fun k => a k = none)).card)
      (fun _ => pow_pos Fintype.card_pos _)
      (dynJoin_fiber_count_of_bad_symbol Q R hcore T n)
    have hs : (∑ a : Fin n → Option I, (μ (ksJoinCells R.cells T n a)).toReal *
        Real.log ((Fintype.card I ^
          (Finset.univ.filter (fun k => a k = none)).card : ℕ) : ℝ)) =
        (n : ℝ) * (μ (R.cells none)).toReal * Real.log (Fintype.card I) := by
      simp_rw [Nat.cast_pow, Real.log_pow]
      calc
        _ = (∑ a : Fin n → Option I, (μ (ksJoinCells R.cells T n a)).toReal *
            ((Finset.univ.filter (fun k => a k = none)).card : ℝ)) *
              Real.log (Fintype.card I) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun a _ => by ring)
        _ = _ := by rw [dynJoin_expected_symbol_count hT R n none]
    change ksEntropySeq hT (Q.toMeasurePartition μ) n ≤
      ksEntropySeq hT (R.toMeasurePartition μ) n + _ at h
    rw [show (∑ a : Fin n → Option I,
      (μ ((ksJoin hT (R.toMeasurePartition μ) n).cells a)).toReal *
        Real.log (Fintype.card I ^ (Finset.univ.filter (fun k => a k = none)).card : ℕ)) =
      (n : ℝ) * (μ (R.cells none)).toReal * Real.log (Fintype.card I) from hs] at h
    exact h
  apply le_of_tendsto_of_tendsto (tendsto_ksEntropySeq hT (Q.toMeasurePartition μ))
    ((tendsto_ksEntropySeq hT (R.toMeasurePartition μ)).add_const
      ((μ (R.cells none)).toReal * Real.log (Fintype.card I)))
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (ksEntropySeq hT (R.toMeasurePartition μ) n +
        (n : ℝ) * (μ (R.cells none)).toReal * Real.log (Fintype.card I)) / n :=
      div_le_div_of_nonneg_right (hfinite n) hnR.le
    _ = _ := by field_simp; ring

end ErgodicTheory.Entropy

