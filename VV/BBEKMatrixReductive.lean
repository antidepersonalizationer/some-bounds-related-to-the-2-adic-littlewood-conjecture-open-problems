import VV.BBEKZariskiRoots

/-! Reductivity expressed by its defining geometric condition: every connected
closed normal unipotent matrix subgroup is trivial. All root-group witnesses
used to apply this condition are constructed in `BBEKZariskiRoots`. -/
noncomputable section
open Matrix Set MulAction MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups Topology
namespace VV.BBEKMatrixReductive
open BBEKAlgebraicTangent BBEKAlgebraicTrichotomy BBEKZariskiRoots
open BBEKDiagonalDensity BBEKDiagonal BBEKNormalizerOrbit BBEKNormalizerExclusion
open BBEKDynamics BBEKQuotient BBEKAlgebraicOrbit

variable {K : Type*} [Field K]

/-- Triviality of connected normal unipotent algebraic subgroups in the
specified field. Geometric reductivity requires this condition after every
field extension; see `BBEKRationalReductive`. Closedness and connectedness are
in the actual matrix Zariski topology, not the real or p-adic topology. -/
def IsReductive (L : Subgroup SL(2,K)) : Prop :=
  ∀ U : Subgroup SL(2,K), U ≤ L → PolynomialClosed (U : Set SL(2,K)) →
    @IsConnected _ (zariski K) (U : Set SL(2,K)) →
    (U.subgroupOf L).Normal → (∀g∈U, IsNilpotent (g.val-1)) → U=⊥

theorem diagonal_unipotent_eq_one {g : SL(2,K)}
    (hg : g ∈ diagonalGroup K) (hu : IsNilpotent (g.val-1)) : g=1 := by
  obtain ⟨hb,hc⟩ := (BBEKGaussChart.mem_diagonalGroup_iff g).mp hg
  have hd : g.val-1=Matrix.diagonal (fun i => g i i-1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb,hc]
  obtain ⟨n,hn⟩ := hu
  rw [hd,Matrix.diagonal_pow] at hn
  have hz (i : Fin 2) : g i i=1 := by
    have he := congrArg (fun M : Mat2 K => M i i) hn
    have hp : (g i i-1)^n=0 := by simpa using he
    exact sub_eq_zero.mp (pow_eq_zero hp)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb,hc,hz]

/-- The split torus satisfies the actual reductivity condition: even a
single unipotent diagonal element is the identity. -/
theorem diagonal_isReductive : IsReductive (diagonalGroup K) := by
  intro U hU _ _ _ hu
  apply le_antisymm _ bot_le
  intro g hg
  exact diagonal_unipotent_eq_one (hU hg) (hu g hg)

variable [CharZero K]

/-- A proper reductive polynomial subgroup containing the split torus
normalizes that torus. This uses actual normal connected unipotent root
groups to rule out the other alternatives of the matrix trichotomy. -/
theorem proper_reductive_le_normalizer (L : Subgroup SL(2,K))
    (hclosed : PolynomialClosed (L : Set SL(2,K))) (hproper : L ≠ ⊤)
    (hred : IsReductive L) (hD : diagonalGroup K ≤ L) :
    L ≤ (diagonalGroup K).normalizer := by
  obtain ⟨P,hP⟩ := hclosed
  rcases proper_polynomial_trichotomy L P hP hproper hD with h | ⟨hle,hn⟩ | ⟨hle,hn⟩
  · exact h
  · exact (upperRoot_nontrivial (hred (upperRoot K) hle upperRoot_polynomialClosed
      upperRoot_connected hn (fun _ hg => upperRoot_unipotent hg))).elim
  · exact (lowerRoot_nontrivial (hred (lowerRoot K) hle lowerRoot_polynomialClosed
      lowerRoot_connected hn (fun _ hg => lowerRoot_unipotent hg))).elim

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- The local-points periodic-orbit exclusion. No diagonal-containment,
Lie-algebra reductivity, compact-orbit, or zero-entropy hypothesis is supplied.
All of those conclusions are derived from the displayed geometric data. -/
theorem closed_reductive_orbit_entropy_zero
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul A X μ]
    (LR : Subgroup SL(2,ℝ)) (LP : Subgroup SL(2,Q2))
    (hR : PolynomialClosed (LR : Set SL(2,ℝ)))
    (hP : PolynomialClosed (LP : Set SL(2,Q2)))
    (hproperR : LR ≠ ⊤) (hproperP : LP ≠ ⊤)
    (hredR : IsReductive LR) (hredP : IsReductive LP)
    (q : X) (hq : IsClosed (orbit (LR.prod LP) q))
    (hO : μ (orbit (LR.prod LP) q)=1)
    {C : Set X} (hC : IsCompact C) (hfull : μ C=1) (t : ℝ) (n : ℤ) :
    ErgodicTheory.Entropy.ksEntropy
      (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ)=0 := by
  obtain ⟨PR,hPR⟩ := hR
  obtain ⟨PP,hPP⟩ := hP
  have hD := diagonal_le_of_closed_polynomial_orbit μ LR LP PR PP hPR hPP q hq hO
  have hDR : diagonalGroup ℝ ≤ LR := fun g hg =>
    (hD (show (g,1) ∈ A from ⟨hg,(diagonalGroup Q2).one_mem⟩)).1
  have hDP : diagonalGroup Q2 ≤ LP := fun g hg =>
    (hD (show (1,g) ∈ A from ⟨(diagonalGroup ℝ).one_mem,hg⟩)).2
  have hNR := proper_reductive_le_normalizer LR ⟨PR,hPR⟩ hproperR hredR hDR
  have hNP := proper_reductive_le_normalizer LP ⟨PP,hPP⟩ hproperP hredP hDP
  have hLN : LR.prod LP ≤ N := by
    intro g hg
    change g.1 ∈ monomialGroup ℝ ∧ g.2 ∈ monomialGroup Q2
    rw [monomial_eq_normalizer,monomial_eq_normalizer]
    exact ⟨hNR hg.1,hNP hg.2⟩
  exact closed_subgroup_orbit_entropy_zero μ (LR.prod LP) hLN q hq hO hC hfull t n

end VV.BBEKMatrixReductive

