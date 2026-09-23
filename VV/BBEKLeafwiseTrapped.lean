import VV.BBEKEntropyGeometry
import VV.BBEKTopology
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! On compact inverse-diagonal trapped orbits the contracting lower-unipotent
action is free. Finite invariant measures supported on the compact set satisfy
this condition almost surely, with no freeness premise. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace VV.BBEKLeafwiseTrapped
open BBEKDynamics BBEKQuotient BBEKEntropyGeometry BBEKTopology

theorem contracting_stabilizer_eq_one {K : Set X} (hK : IsCompact K)
    (a h : G) (q : X) (hq : ∀ n : ℕ, (a⁻¹)^n • q ∈ K)
    (hcontract : Tendsto (fun n : ℕ => (a⁻¹)^n*h*a^n) atTop (𝓝 1))
    (hfix : h • q = q) : h = 1 := by
  obtain ⟨r,hr,hfree⟩ := compact_uniform_no_small_stabilizer hK
  have hsmall : ∀ᶠ n : ℕ in atTop, dist ((a⁻¹)^n*h*a^n) 1 < r :=
    hcontract.eventually (ball_mem_nhds _ hr)
  obtain ⟨n,hn⟩ := hsmall.exists
  have hnfix : ((a⁻¹)^n*h*a^n) • ((a⁻¹)^n • q) = (a⁻¹)^n • q := by
    calc
      _ = ((a⁻¹)^n*h) • q := by rw [← mul_smul]; congr 1; group
      _ = _ := by rw [mul_smul,hfix]
  have he := hfree ((a⁻¹)^n • q) (hq n) _ hn hnfix
  calc
    h = a^n*((a⁻¹)^n*h*a^n)*(a⁻¹)^n := by group
    _ = 1 := by rw [he]; group

/-- Freeness of the entire real/2-adic lower root group on the actual compact
trapped orbit. This excludes periodic leaf identifications before extending plaques. -/
theorem lower_fixed_iff_zero {K : Set X} (hK : IsCompact K)
    {t : ℝ} (ht : 0 < t) (q : X)
    (hq : ∀ n : ℕ, ((psi t 1)⁻¹)^n • q ∈ K) (u : ℝ) (v : Q2) :
    x u v • q = q ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro hf
    have he := contracting_stabilizer_eq_one hK (psi t 1) (x u v) q hq
      (lower_inverse_conjugates_tendsto ht u v) hf
    have hh : (u,v) = (0,0) := isometry_x.injective (he.trans x_zero.symm)
    exact Prod.mk.inj hh
  · rintro ⟨rfl,rfl⟩
    rw [x_zero,one_smul]

theorem inverse_smul_iterate (a : G) (n : ℕ) (q : X) :
    ((fun z : X => a⁻¹ • z)^[n]) q = (a⁻¹)^n • q := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, ← mul_smul, ← pow_succ']

theorem ae_compact_inverse_orbit (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1) (a : G)
    (hT : MeasurePreserving (fun q : X => a⁻¹ • q) μ μ) :
    ∀ᵐ q ∂μ, ∀ n : ℕ, (a⁻¹)^n • q ∈ K := by
  have hmem : ∀ᵐ q ∂μ, q ∈ K := by
    apply ae_iff.mpr
    change μ Kᶜ = 0
    rw [measure_compl hK.measurableSet (measure_ne_top _ _), measure_univ, hμK, tsub_self]
  apply ae_all_iff.mpr
  intro n
  simpa only [inverse_smul_iterate] using (hT.iterate n).quasiMeasurePreserving.ae hmem

/-- The actual invariant compactly supported probability almost surely has
free lower root orbits, not merely locally injective ones. -/
theorem ae_lower_fixed_iff_zero (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : 0 < t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∀ᵐ q ∂μ, ∀ (u : ℝ) (v : Q2), x u v • q = q ↔ u = 0 ∧ v = 0 := by
  filter_upwards [ae_compact_inverse_orbit μ hK hμK (psi t 1) hT] with q hq u v
  exact lower_fixed_iff_zero hK ht q hq u v

end VV.BBEKLeafwiseTrapped
