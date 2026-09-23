import VV.BBEKAlgebraicTrichotomy

/-! The matrix Zariski topology and the actual algebraic, connected,
unipotent root groups. This supplies geometric witnesses, rather than a
special-purpose axiom excluding the root alternatives. -/
noncomputable section
open Matrix MvPolynomial Set
open scoped MatrixGroups Topology
namespace VV.BBEKZariskiRoots
open BBEKAlgebraicTangent BBEKNilpotentTangent BBEKAlgebraicTrichotomy
open BBEKDiagonalDensity BBEKDynamics BBEKMahlerPadic
open BBEKSl2Reductive (E F)

variable {K : Type*} [Field K]

def PolynomialClosed (s : Set SL(2,K)) : Prop := ∃ P : Set (Polys K), s=matrixZeroSet P

theorem polynomialClosed_empty : PolynomialClosed (∅ : Set SL(2,K)) := by
  refine ⟨{1},?_⟩
  ext g
  simp [matrixZeroSet]

theorem polynomialClosed_sInter (S : Set (Set SL(2,K)))
    (hS : ∀ s ∈ S, PolynomialClosed s) : PolynomialClosed (⋂₀ S) := by
  classical
  choose P hP using hS
  refine ⟨⋃ s, ⋃ hs : s∈S, P s hs,?_⟩
  ext g
  simp only [mem_sInter,matrixZeroSet,mem_setOf_eq,mem_iUnion,exists_prop]
  constructor
  · intro hg p ⟨s,hs,hp⟩
    have he := hg s hs
    rw [hP s hs] at he
    exact he p hp
  · intro hg s hs
    rw [hP s hs]
    intro p hp
    exact hg p ⟨s,hs,hp⟩

theorem polynomialClosed_union {s t : Set SL(2,K)}
    (hs : PolynomialClosed s) (ht : PolynomialClosed t) : PolynomialClosed (s∪t) := by
  classical
  obtain ⟨P,rfl⟩ := hs
  obtain ⟨Q,rfl⟩ := ht
  refine ⟨{p | ∃a∈P,∃b∈Q,p=a*b},?_⟩
  ext g
  constructor
  · rintro (hg | hg) p ⟨a,ha,b,hb,rfl⟩
    · simp [map_mul,hg a ha]
    · simp [map_mul,hg b hb]
  · intro hg
    by_cases hp : g ∈ matrixZeroSet P
    · exact Or.inl hp
    · right
      simp only [matrixZeroSet,mem_setOf_eq,not_forall] at hp
      obtain ⟨a,ha,haz⟩ := hp
      intro b hb
      have he := hg (a*b) ⟨a,ha,b,hb,rfl⟩
      rw [map_mul] at he
      exact (mul_eq_zero.mp he).resolve_left haz

/-- Closed sets are exactly zero sets of arbitrary families of matrix
coordinate polynomials, restricted to determinant-one matrices. -/
def zariski (K : Type*) [Field K] : TopologicalSpace SL(2,K) :=
  TopologicalSpace.ofClosed {s | PolynomialClosed s} polynomialClosed_empty
    polynomialClosed_sInter (fun _ hs _ ht => polynomialClosed_union hs ht)

theorem isClosed_zariski_iff (s : Set SL(2,K)) :
    IsClosed[zariski K] s ↔ PolynomialClosed s := by
  letI := zariski K
  rw [← isOpen_compl_iff]
  change PolynomialClosed sᶜᶜ ↔ PolynomialClosed s
  rw [compl_compl]

theorem upperRoot_polynomialClosed : PolynomialClosed (upperRoot K : Set SL(2,K)) := by
  refine ⟨{X (0,0)-1,X (1,0),X (1,1)-1},?_⟩
  ext g
  simp [upperRoot,matrixZeroSet,sub_eq_zero]

theorem lowerRoot_polynomialClosed : PolynomialClosed (lowerRoot K : Set SL(2,K)) := by
  refine ⟨{X (0,0)-1,X (0,1),X (1,1)-1},?_⟩
  ext g
  simp [lowerRoot,matrixZeroSet,sub_eq_zero]

theorem upperRoot_nontrivial : upperRoot K ≠ ⊥ := by
  intro he
  have hu : upper (1:K) ∈ upperRoot K := (mem_upperRoot_iff _).mpr ⟨1,rfl⟩
  rw [he] at hu
  have hm : upper (1:K)=1 := hu
  have hc := congrArg (fun g : SL(2,K) => g 0 1) hm
  simpa [upper] using hc

theorem lowerRoot_nontrivial : lowerRoot K ≠ ⊥ := by
  intro he
  have hu : lower (1:K) ∈ lowerRoot K := (mem_lowerRoot_iff _).mpr ⟨1,rfl⟩
  rw [he] at hu
  have hm : lower (1:K)=1 := hu
  have hc := congrArg (fun g : SL(2,K) => g 1 0) hm
  simpa [lower] using hc

theorem upperRoot_unipotent {g : SL(2,K)} (hg : g ∈ upperRoot K) :
    IsNilpotent (g.val-1) := by
  obtain ⟨u,rfl⟩ := (mem_upperRoot_iff g).mp hg
  refine ⟨2,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two,upper,Matrix.mul_apply,Fin.sum_univ_two]

theorem lowerRoot_unipotent {g : SL(2,K)} (hg : g ∈ lowerRoot K) :
    IsNilpotent (g.val-1) := by
  obtain ⟨u,rfl⟩ := (mem_lowerRoot_iff g).mp hg
  refine ⟨2,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two,lower,Matrix.mul_apply,Fin.sum_univ_two]

variable [CharZero K]

/-- Polynomial images of the affine line are irreducible in the literal
matrix Zariski topology. The proof uses infinite roots of a univariate
polynomial, not connectedness in a local-field topology. -/
theorem nilpotent_curve_irreducible (M : Mat2 K) (f : K → SL(2,K))
    (hf : ∀t, (f t).val=1+t • M) :
    @IsIrreducible _ (zariski K) (range f) := by
  letI := zariski K
  refine ⟨range_nonempty f,?_⟩
  apply isPreirreducible_iff_isClosed_union_isClosed.mpr
  intro s t hs ht hcover
  obtain ⟨P,rfl⟩ := (isClosed_zariski_iff s).mp hs
  obtain ⟨Q,rfl⟩ := (isClosed_zariski_iff t).mp ht
  by_cases hp : range f ⊆ matrixZeroSet P
  · exact Or.inl hp
  · right
    obtain ⟨g,⟨a,rfl⟩,hga⟩ := not_subset.mp hp
    simp only [matrixZeroSet,mem_setOf_eq,not_forall] at hga
    obtain ⟨p,hp,hpa⟩ := hga
    have hn : curve M p ≠ 0 := by
      intro he
      have hv := congrArg (Polynomial.eval a) he
      rw [eval_curve,← hf a] at hv
      exact hpa (by simpa [entries] using hv)
    rintro g ⟨b,rfl⟩ q hq
    have hzero : curve M p * curve M q=0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.infinite_univ.mono
      intro u _
      change (curve M p * curve M q).eval u=0
      rw [Polynomial.eval_mul,eval_curve,eval_curve,← hf u]
      rcases hcover (mem_range_self u) with hu | hu
      · exact mul_eq_zero.mpr (Or.inl (hu p hp))
      · exact mul_eq_zero.mpr (Or.inr (hu q hq))
    have hqzero := (mul_eq_zero.mp hzero).resolve_left hn
    have hv := congrArg (Polynomial.eval b) hqzero
    rw [eval_curve,← hf b] at hv
    simpa [entries] using hv

theorem upperRoot_connected :
    @IsConnected _ (zariski K) (upperRoot K : Set SL(2,K)) := by
  letI := zariski K
  have hf (t : K) : (upper t).val=1+t • (E : Mat2 K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper,E]
  have hr : (upperRoot K : Set SL(2,K))=range upper := by
    ext g
    simpa only [mem_range,eq_comm] using mem_upperRoot_iff g
  rw [hr]
  exact (nilpotent_curve_irreducible E upper hf).isConnected

theorem lowerRoot_connected :
    @IsConnected _ (zariski K) (lowerRoot K : Set SL(2,K)) := by
  letI := zariski K
  have hf (t : K) : (lower t).val=1+t • (F : Mat2 K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lower,F]
  have hr : (lowerRoot K : Set SL(2,K))=range lower := by
    ext g
    simpa only [mem_range,eq_comm] using mem_lowerRoot_iff g
  rw [hr]
  exact (nilpotent_curve_irreducible F lower hf).isConnected

end VV.BBEKZariskiRoots



