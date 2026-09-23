import VV.BBEKLattice
import VV.BBEKQuotient
import VV.BBEKShortVector

/-! The actual arithmetic lattice and short-vector set K_delta on G/Gamma.
In particular the Diophantine implication in BBEK Proposition 5.1 is an
ordinary theorem, not an input about an unspecified dynamical system. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups Topology

namespace VV.BBEKOrbit
open BBEKDynamics BBEKQuotient BBEKLattice BBEKShortVector P7AdicLimits

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev Ambient := (Fin 2 → ℝ) × (Fin 2 → Q2)
abbrev Coefficients := Fin 2 → BBEKDyadic.dyadic

def arithmeticLattice (q : X) : Set Ambient :=
  quotientLattice dyadicToReal dyadicToQ2 q

@[simp] theorem arithmeticLattice_mk (M : G) :
    arithmeticLattice (mk M) = lattice dyadicToReal dyadicToQ2 M := rfl

/-- The paper's actual no-short-vector set, using the product sup norm. -/
def K (δ : ℝ) : Set X :=
  {q | ∀ w ∈ arithmeticLattice q, w ≠ 0 → δ ≤ ‖w‖}

theorem mem_K_mk_iff (δ : ℝ) (M : G) : mk M ∈ K δ ↔
    ∀ r : Coefficients, r ≠ 0 → δ ≤ ‖vectorImage dyadicToReal dyadicToQ2 M r‖ := by
  constructor
  · intro h r hr
    apply h _ ⟨r,rfl⟩
    intro he
    apply hr
    exact (vectorImage_injective dyadicToReal dyadicToQ2 dyadicToReal_injective M)
      (he.trans (vectorImage_zero dyadicToReal dyadicToQ2 M).symm)
  · intro h w hw hne
    obtain ⟨r,rfl⟩ := hw
    apply h r
    intro hr
    apply hne
    rw [hr,vectorImage_zero]

theorem continuous_vectorImage (r : Coefficients) :
    Continuous (fun M : G => vectorImage dyadicToReal dyadicToQ2 M r) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    change Continuous (fun M : G => ∑ j : Fin 2, M.1 i j * dyadicToReal (r j))
    apply continuous_finset_sum
    intro j _
    have hc : Continuous (fun M : G => (M.1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).mul continuous_const
  · apply continuous_pi
    intro i
    change Continuous (fun M : G => ∑ j : Fin 2, M.2 i j * dyadicToQ2 (r j))
    apply continuous_finset_sum
    intro j _
    have hc : Continuous (fun M : G => (M.2 : Matrix (Fin 2) (Fin 2) Q2)) :=
      continuous_subtype_val.comp continuous_snd
    exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).mul continuous_const

/-- Closedness follows directly from continuous lattice vectors and the
quotient topology; no Mahler compactness assertion is used. -/
theorem isClosed_K (δ : ℝ) : IsClosed (K δ) := by
  apply (QuotientGroup.isQuotientMap_mk Gamma).isClosed_preimage.mp
  have he : (QuotientGroup.mk : G → X) ⁻¹' K δ =
      ⋂ r : Coefficients, ⋂ (_h : r ≠ 0),
        {M : G | δ ≤ ‖vectorImage dyadicToReal dyadicToQ2 M r‖} := by
    ext M
    simp only [mem_preimage,mem_iInter,mem_setOf_eq]
    exact mem_K_mk_iff δ M
  rw [he]
  exact isClosed_iInter fun r => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_vectorImage r).norm

theorem orbit_vector_formula (t : ℝ) (n : ℤ) (u : ℝ) (v : Q2) (r : Coefficients) :
    vectorImage dyadicToReal dyadicToQ2 (psi t n * x u v) r =
      (![Real.exp (-t) * dyadicToReal (r 0),
          Real.exp t * (dyadicToReal (r 0) * u + dyadicToReal (r 1))],
       ![(2:Q2)^n * dyadicToQ2 (r 0),
          (2:Q2)^(-n) * (dyadicToQ2 (r 0) * v + dyadicToQ2 (r 1))]) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [vectorImage,psi,x,BBEKDynamics.diagonal,lower,Matrix.mulVec,Matrix.mul_apply,
      dotProduct,Fin.sum_univ_two,Real.exp_neg,zpow_neg,Function.comp_def] <;> ring

theorem parameter_orbit_mem_K {ε u : ℝ} {v : ℤ_[2]}
    (hε : 0 < ε) (h : (u,v) ∈ JointBadlyApproximable ε)
    (t : ℝ) (n : ℤ) (hc : Cone t n) :
    psi t n • parameterPoint u (v : Q2) ∈ K (shortRadius ε) := by
  rw [parameterPoint,smul_mk]
  apply (mem_K_mk_iff _ _).mpr
  intro r hr
  by_contra! hs
  have hcoords := orbit_vector_formula t n u (v : Q2) r
  have hfirst := (norm_le_pi_norm
    (vectorImage dyadicToReal dyadicToQ2 (psi t n * x u (v : Q2)) r).1 0).trans_lt
    ((norm_fst_le _).trans_lt hs)
  have hsecond := (norm_le_pi_norm
    (vectorImage dyadicToReal dyadicToQ2 (psi t n * x u (v : Q2)) r).1 1).trans_lt
    ((norm_fst_le _).trans_lt hs)
  have hthird := (norm_le_pi_norm
    (vectorImage dyadicToReal dyadicToQ2 (psi t n * x u (v : Q2)) r).2 0).trans_lt
    ((norm_snd_le _).trans_lt hs)
  have hfourth := (norm_le_pi_norm
    (vectorImage dyadicToReal dyadicToQ2 (psi t n * x u (v : Q2)) r).2 1).trans_lt
    ((norm_snd_le _).trans_lt hs)
  rw [hcoords] at hfirst hsecond hthird hfourth
  change ‖Real.exp (-t) * ((r 0).val : ℝ)‖ < shortRadius ε at hfirst
  change ‖Real.exp t * (((r 0).val : ℝ) * u + ((r 1).val : ℝ))‖ <
    shortRadius ε at hsecond
  have hne : (r 0).val ≠ 0 ∨ -(r 1).val ≠ 0 := by
    by_contra! he
    apply hr
    funext i
    apply Subtype.ext
    fin_cases i
    · exact he.1
    · simpa using he.2
  apply no_dyadic_short_vector_zpow hε h t n hc.1 hc.2
    (r 0).val (-(r 1).val) (r 0).property (BBEKDyadic.dyadic.neg_mem (r 1).property) hne
  · simpa only [Real.norm_eq_abs] using hfirst
  · simpa only [Rat.cast_neg,sub_neg_eq_add,Real.norm_eq_abs] using hsecond
  · simpa using hthird
  · simpa using hfourth

/-- BBEK Proposition 5.1, for p=2, on the actual S-arithmetic quotient.
Its radius is the radius in the proposition, (epsilon/2)^(1/3).
No compactness, measure rigidity, entropy theorem, or computation is assumed. -/
theorem proposition51 {ε u : ℝ} {v : ℤ_[2]}
    (hε : 0 < ε) (h : (u,v) ∈ JointBadlyApproximable ε) :
    coneOrbit (parameterPoint u (v : Q2)) ⊆ K (shortRadius ε) := by
  rintro q ⟨t,n,hc,rfl⟩
  exact parameter_orbit_mem_K hε h t n hc

end VV.BBEKOrbit
