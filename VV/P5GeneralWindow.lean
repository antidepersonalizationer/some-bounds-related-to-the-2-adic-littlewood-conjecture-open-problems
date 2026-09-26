import VV.P5Window

/-!
# Arbitrary finite windows and digit bounds

The discriminant argument does not depend on the unverified depth-14,
bound-10 check. This module proves it for every digit bound, window width,
and chosen middle layer. A proved rank certificate at any synchronization
depth therefore has a direct real continued-fraction consequence.
No concrete finite check or entropy input is assumed by these reductions.
-/

namespace VV.P5GeneralWindow

open QuadraticScaling

/-- A finite primitive-discriminant table for the selected layer of each
window of `width + 1` consecutive bounded layers. -/
def WindowClassification (C width middle : ℕ) : Prop :=
  ∃ S : Finset ℕ, ∀ x : ℝ, Irrational x →
    (∀ k : ℕ, k ≤ width → EventualBound ((2 : ℝ) ^ k * x) C) →
    ∃ Q : Quadratic, Q.eval ((2 : ℝ) ^ middle * x) = 0 ∧
      Problem3.PrimitiveTriple Q.A Q.B Q.C ∧ Q.disc.natAbs ∈ S

/-- A uniformly bounded period in the chosen layer gives the required
finite discriminant table, without enumerating that table. -/
theorem classification_of_bounded_period {C width middle K : ℕ}
    (h : ∀ x : ℝ, Irrational x →
      (∀ k : ℕ, k ≤ width → EventualBound ((2 : ℝ) ^ k * x) C) →
      P5Period.BoundedPeriod ((2 : ℝ) ^ middle * x) C K) :
    WindowClassification C width middle := by
  refine ⟨P5Period.discriminantTable C K, ?_⟩
  intro x hx hlow
  obtain ⟨Q, _, hp, hr, hd⟩ := P5Period.finite_discriminants_of_bounded_period
    C K (irrational_dyadic_mul hx middle) (h x hx hlow)
  exact ⟨Q, hr, hp, hd⟩

/-- The primitive discriminants of a dyadic orbit cannot stay in one
finite table. This conclusion is independent of the numerical bound. -/
theorem not_bOrbitBound_of_classification {C width middle : ℕ}
    (classification : WindowClassification C width middle)
    {x : ℝ} (hx : Irrational x) : ¬ BOrbitBound x C := by
  intro allLow
  obtain ⟨S, classify⟩ := classification
  obtain ⟨Q, hQ, pQ, _⟩ := classify x hx (fun k _ => allLow k)
  let β : ℝ := (2 : ℝ) ^ middle * x
  have hβ : Irrational β := irrational_dyadic_mul hx middle
  have hA : Q.A ≠ 0 := A_ne_zero_of_primitive_irrational_root Q hβ hQ pQ
  have unbounded := normalizedScale_discriminants_unbounded Q hA hβ hQ
  apply Problem5.unbounded_sequence_not_in_finite_set
    (fun j => (Q.normalizedScale j).disc.natAbs) unbounded S
  intro j
  have hxj := irrational_dyadic_mul hx j
  have lowj := bOrbitBound_shift allLow j
  obtain ⟨R, hR, pR, hmem⟩ := classify ((2 : ℝ) ^ j * x) hxj (fun k _ => lowj k)
  have hroot : (Q.normalizedScale j).eval ((2 : ℝ) ^ j * β) = 0 :=
    normalizedScale_root Q hA hQ j
  have hR' : R.eval ((2 : ℝ) ^ j * β) = 0 := by
    have harg : (2 : ℝ) ^ j * β = (2 : ℝ) ^ middle * ((2 : ℝ) ^ j * x) := by
      dsimp [β]
      ring
    rw [harg]
    exact hR
  have hdisc := primitive_same_root_disc (Q.normalizedScale j) R
    (irrational_dyadic_mul hβ j) hroot hR'
    (normalizedScale_primitive Q hA j) pR
  simpa only [hdisc] using hmem

/-- Any such classification forces digits at least `C + 1` infinitely
often in one fixed layer of every irrational dyadic orbit. -/
theorem frequently_large_of_classification {C width middle : ℕ}
    (classification : WindowClassification C width middle)
    (x : ℝ) (hx : Irrational x) :
    ∃ k : ℕ, DigitsFrequentlyAtLeast ((2 : ℝ) ^ k * x) (C + 1) := by
  by_contra h
  apply not_bOrbitBound_of_classification classification hx
  intro k
  by_contra hlow
  exact h ⟨k, (not_eventualBound_iff _ C).mp hlow⟩

/-- More strongly, all sufficiently late windows contain such a layer.
The finite initial delay may depend on the input real number. -/
theorem eventual_every_window {C width middle : ℕ}
    (classification : WindowClassification C width middle)
    (x : ℝ) (hx : Irrational x) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ k : ℕ, k ≤ width ∧
      DigitsFrequentlyAtLeast ((2 : ℝ) ^ (j + k) * x) (C + 1) := by
  classical
  obtain ⟨S, classify⟩ := classification
  let low : ℕ → Prop := fun j =>
    ∀ k : ℕ, k ≤ width → EventualBound ((2 : ℝ) ^ (j + k) * x) C
  have finish (j : ℕ) (h : ¬ low j) : ∃ k : ℕ, k ≤ width ∧
      DigitsFrequentlyAtLeast ((2 : ℝ) ^ (j + k) * x) (C + 1) := by
    by_contra h'
    apply h
    intro k hk
    by_contra hb
    exact h' ⟨k, hk, (not_eventualBound_iff _ C).mp hb⟩
  by_cases anyLow : ∃ j, low j
  · obtain ⟨j₀, hj₀⟩ := anyLow
    have hbase : Irrational ((2 : ℝ) ^ j₀ * x) := irrational_dyadic_mul hx j₀
    obtain ⟨Q, hQ, pQ, _⟩ := classify ((2 : ℝ) ^ j₀ * x) hbase (by
      intro k hk
      simpa only [pow_add, mul_assoc, mul_left_comm] using hj₀ k hk)
    let β : ℝ := (2 : ℝ) ^ middle * ((2 : ℝ) ^ j₀ * x)
    have hβ : Irrational β := irrational_dyadic_mul hbase middle
    have hA := A_ne_zero_of_primitive_irrational_root Q hβ hQ pQ
    let M := S.sup id
    refine ⟨j₀ + Q.A.natAbs ^ 2 * M, ?_⟩
    intro j hj
    apply finish j
    intro hjlow
    have hshift : j₀ + (j - j₀) = j := by omega
    have hlarge := Problem5.reduced_discriminants_eventually_above
      Q.A.natAbs Q.disc.natAbs
      (Problem5.scaledContent Q.A.natAbs Q.B.natAbs Q.C.natAbs)
      (fun t => (Q.normalizedScale t).disc.natAbs)
      (Int.natAbs_pos.mpr (disc_ne_zero_of_irrational_root Q hA hβ hQ))
      (Problem5.scaledContent_le (Int.natAbs_pos.mpr hA) Q.B.natAbs Q.C.natAbs)
      (normalizedScale_abs_discriminant Q) M (j - j₀) (by omega)
    obtain ⟨R, hR, pR, hmem⟩ := classify ((2 : ℝ) ^ j * x)
      (irrational_dyadic_mul hx j) (by
        intro k hk
        simpa only [pow_add, mul_assoc, mul_left_comm] using hjlow k hk)
    have harg : (2 : ℝ) ^ (j - j₀) * β =
        (2 : ℝ) ^ middle * ((2 : ℝ) ^ j * x) := by
      calc
        (2 : ℝ) ^ (j - j₀) * β =
            (2 : ℝ) ^ middle * ((2 : ℝ) ^ (j₀ + (j - j₀)) * x) := by
          dsimp [β]
          rw [pow_add]
          ring
        _ = (2 : ℝ) ^ middle * ((2 : ℝ) ^ j * x) := by rw [hshift]
    have hroot := normalizedScale_root Q hA hQ (j - j₀)
    have hR' : R.eval ((2 : ℝ) ^ (j - j₀) * β) = 0 := by rwa [harg]
    have hdisc := primitive_same_root_disc (Q.normalizedScale (j - j₀)) R
      (irrational_dyadic_mul hβ (j - j₀)) hroot hR'
      (normalizedScale_primitive Q hA (j - j₀)) pR
    have hm : (Q.normalizedScale (j - j₀)).disc.natAbs ≤ M := by
      have := Finset.le_sup (f := id) hmem
      simpa only [hdisc] using this
    exact (not_lt_of_ge hm) hlarge
  · exact ⟨0, fun j _ => finish j (fun hj => anyLow ⟨j, hj⟩)⟩

/-- The generic infinite-path and discriminant argument for any explicitly
specified finite graph and a supplied rank certificate. -/
theorem classification_of_rank_graph {C width middle : ℕ}
    (G : P5Graph.Graph) (rank : Fin G.size → Fin (G.size + 1))
    (hcert : G.RankCertificate rank) (hlab : ∀ v, G.label v ≤ C)
    (coverage : ∀ x : ℝ, Irrational x →
      (∀ k : ℕ, k ≤ width → EventualBound ((2 : ℝ) ^ k * x) C) →
      G.Realizes ((2 : ℝ) ^ middle * x)) :
    WindowClassification C width middle := by
  apply classification_of_bounded_period (K := G.size)
  intro x hx hlow
  exact G.boundedPeriod_of_rank_realizes C rank hcert hlab (coverage x hx hlow)

/-- A rank certificate at depth `r` suffices for the actual window of
`2 * (r + 1) + 1` dyadic layers, for any bound `C`. -/
theorem classification_of_window_check (C r : ℕ)
    (hfinite : (P5Window.windowGraph C r).checkEventuallyDeterministic = true) :
    WindowClassification C (2 * (r + 1)) (r + 1) := by
  letI : DecidableEq (P5Synchronize.StateAt (P5Machine.Pair C) r) :=
    P5Window.stateAtDecidableEq (P5Machine.Pair C) r
  obtain ⟨rank, hcert⟩ := of_decide_eq_true hfinite
  exact classification_of_rank_graph (P5Window.windowGraph C r) rank hcert
    (P5MachineGraph.graph_label_bound C (P5Synchronize.iterate (P5Machine.step C) r))
    (fun _ hx h => P5Window.windowGraph_realizes C r hx h)

theorem frequently_large_of_window_check (C r : ℕ)
    (hfinite : (P5Window.windowGraph C r).checkEventuallyDeterministic = true)
    (x : ℝ) (hx : Irrational x) :
    ∃ k : ℕ, DigitsFrequentlyAtLeast ((2 : ℝ) ^ k * x) (C + 1) :=
  frequently_large_of_classification (classification_of_window_check C r hfinite) x hx

theorem eventual_every_window_of_check (C r : ℕ)
    (hfinite : (P5Window.windowGraph C r).checkEventuallyDeterministic = true)
    (x : ℝ) (hx : Irrational x) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ k : ℕ, k ≤ 2 * (r + 1) ∧
      DigitsFrequentlyAtLeast ((2 : ℝ) ^ (j + k) * x) (C + 1) :=
  eventual_every_window (classification_of_window_check C r hfinite) x hx

end VV.P5GeneralWindow
