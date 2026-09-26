import VV.P4Encoding
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Uniform alphabets for fixed-period successful tail classes

Rooting is a bijection between classes with a cyclic phase and actual rooted
words. Every eventual digit of every successful class of least period ℓ
belongs to one finite positive alphabet, of size at most 3 * ℓ^2 * 4^ℓ.
Its maximum gives a uniform eventual bound, without evaluating that maximum.
This does not assert the earlier proposed explicit formula digitBound ℓ.
-/

noncomputable section
namespace VV.Problem4
open Hurwitz

theorem classCycle_toClass_tail {ℓ : ℕ} (r : Representative ℓ) :
    TailEquivalent r.val (classCycle (toClass r)).x := by
  have hr : TailEquivalent (toClass r).out.val r.val := by
    apply (toClass_eq_iff _ _).mp
    simp only [toClass,Quotient.out_eq]
  exact hr.symm.trans (classCycle_tail _)

/-- Every actual rooted word occurs among the roots of its genuine class. -/
theorem rootedClassWord_surjective (ℓ : ℕ) :
    Function.Surjective (@rootedClassWord ℓ) := by
  intro w
  obtain ⟨x,hx,hw,hlen,hmin,hclass,hgood⟩ := w.property
  obtain ⟨y,hxy,hy⟩ := hclass
  let r : Representative ℓ :=
    ⟨y,hy,(exactEventualPeriod_iff_of_tailEquivalent hxy ℓ).mp hmin⟩
  let q := toClass r
  have htail : TailEquivalent (classCycle q).x x :=
    (classCycle_toClass_tail r).symm.trans hxy.symm
  obtain ⟨k,hk,he⟩ := cycle_block_alignment (classCycle q).model hx
    (classCycle q).positive hw (hlen.trans (classCycle q).length.symm)
    (by rw [(classCycle q).length]; exact hmin.1) htail
  refine ⟨(q,⟨k,by simpa only [(classCycle q).length] using hk⟩),?_⟩
  apply Subtype.ext
  change P5Period.digitBlock (classCycle q).x k ℓ=w.val
  simpa only [(classCycle q).length] using he.symm

def rootedClassWordEquiv (ℓ : ℕ) : Class ℓ × Fin ℓ ≃ RootedWord ℓ :=
  Equiv.ofBijective rootedClassWord
    ⟨rootedClassWord_injective ℓ,rootedClassWord_surjective ℓ⟩

/-- Exact root multiplicity, beyond the earlier injection bound. -/
theorem card_rootedWord (ℓ : ℕ) :
    Nat.card (RootedWord ℓ)=ℓ*Nat.card (Class ℓ) := by
  rw [← Nat.card_congr (rootedClassWordEquiv ℓ),Nat.card_prod,Nat.card_eq_fintype_card (α := Fin ℓ),Fintype.card_fin]
  exact Nat.mul_comm _ _

instance finite_rootedWord (ℓ : ℕ) : Finite (RootedWord ℓ) := by
  letI : Finite (Class ℓ) := (problem4_all_periods ℓ).1
  exact Finite.of_surjective rootedClassWord (rootedClassWord_surjective ℓ)

theorem card_rootedWord_le (ℓ : ℕ) :
    Nat.card (RootedWord ℓ)≤3*ℓ^2*4^ℓ := by
  rw [card_rootedWord]
  calc
    ℓ*Nat.card (Class ℓ)≤ℓ*(3*ℓ*4^ℓ) := Nat.mul_le_mul_left _ (problem4_all_periods ℓ).2
    _ = 3*ℓ^2*4^ℓ := by ring

/-- First digits of all possible cyclic roots collect all cycle digits. -/
def uniformAlphabet (ℓ : ℕ) : Finset ℤ := by
  letI : Fintype (RootedWord ℓ) := Fintype.ofFinite _
  exact Finset.univ.image (fun w : RootedWord ℓ => w.val.headD 0)

theorem mem_uniformAlphabet_iff (ℓ : ℕ) (a : ℤ) :
    a∈uniformAlphabet ℓ ↔ ∃w : RootedWord ℓ, w.val.headD 0=a := by
  classical
  simp [uniformAlphabet]

theorem uniformAlphabet_positive {ℓ : ℕ} {a : ℤ} (ha : a∈uniformAlphabet ℓ) : 1≤a := by
  obtain ⟨w,rfl⟩ := (mem_uniformAlphabet_iff ℓ a).mp ha
  obtain ⟨x,hx,hpos,hlen,hmin,hclass,hgood⟩ := w.property
  cases he : w.val with
  | nil =>
    have hp := hmin.1
    simp only [he,List.length_nil] at hlen
    omega
  | cons b v =>
    have hb : b∈w.val := by rw [he]; simp
    simpa only [he,List.headD_cons] using hpos b hb

theorem card_uniformAlphabet_le_rooted (ℓ : ℕ) :
    (uniformAlphabet ℓ).card≤Nat.card (RootedWord ℓ) := by
  classical
  letI : Fintype (RootedWord ℓ) := Fintype.ofFinite _
  simpa only [uniformAlphabet,Nat.card_eq_fintype_card,Finset.card_univ] using
    (Finset.card_image_le (s := (Finset.univ : Finset (RootedWord ℓ)))
      (f := fun w : RootedWord ℓ => w.val.headD 0))

theorem card_uniformAlphabet_le (ℓ : ℕ) :
    (uniformAlphabet ℓ).card≤3*ℓ^2*4^ℓ :=
  (card_uniformAlphabet_le_rooted ℓ).trans (card_rootedWord_le ℓ)

theorem RootedCycle.digit_mem_uniformAlphabet {ℓ : ℕ} (r : RootedCycle ℓ) (n : ℕ) :
    partialQuotient r.x n∈uniformAlphabet ℓ := by
  apply (mem_uniformAlphabet_iff _ _).mpr
  refine ⟨(r.rotate n).toWord,?_⟩
  change (P5Period.digitBlock r.x n ℓ).headD 0=partialQuotient r.x n
  have hpos := r.least.1
  cases ℓ with
  | zero => omega
  | succ k => rfl

/-- One alphabet works for all representatives; finite prefixes may vary. -/
theorem eventual_digits_mem_uniformAlphabet {x : ℝ} {ℓ : ℕ}
    (hclass : HasTripleRepresentative x) (hperiod : ExactEventualPeriod x ℓ) :
    ∃N : ℕ, ∀n≥N, partialQuotient x (n+1)∈uniformAlphabet ℓ := by
  obtain ⟨y,hxy,hy⟩ := hclass
  let r : Representative ℓ :=
    ⟨y,hy,(exactEventualPeriod_iff_of_tailEquivalent hxy ℓ).mp hperiod⟩
  let c := classCycle (toClass r)
  have ht : TailEquivalent x c.x := hxy.trans (classCycle_toClass_tail r)
  obtain ⟨m,k,hk⟩ := ht
  refine ⟨m,fun n hn => ?_⟩
  have he := hk (n-m)
  have hm : m+(n-m)+1=n+1 := by omega
  rw [hm] at he
  rw [he]
  exact c.digit_mem_uniformAlphabet _

/-- A canonical finite maximum, not a numerically evaluated formula. -/
def uniformDigitBound (ℓ : ℕ) : ℕ := (uniformAlphabet ℓ).sup Int.toNat

theorem le_uniformDigitBound_of_mem {ℓ : ℕ} {a : ℤ}
    (ha : a∈uniformAlphabet ℓ) : a≤(uniformDigitBound ℓ : ℤ) := by
  have h := Finset.le_sup (f := Int.toNat) ha
  have hc : (a.toNat : ℤ)≤(uniformDigitBound ℓ : ℤ) := Int.ofNat_le.mpr h
  simpa only [Int.toNat_of_nonneg (le_trans (by omega : (0 : ℤ)≤1) (uniformAlphabet_positive ha))] using hc

theorem eventualBound_uniformDigitBound {x : ℝ} {ℓ : ℕ}
    (hclass : HasTripleRepresentative x) (hperiod : ExactEventualPeriod x ℓ) :
    EventualBound x (uniformDigitBound ℓ) := by
  obtain ⟨N,hN⟩ := eventual_digits_mem_uniformAlphabet hclass hperiod
  exact ⟨N,fun n hn => le_uniformDigitBound_of_mem (hN n hn)⟩

theorem B_le_uniformDigitBound {x : ℝ} {ℓ : ℕ}
    (hclass : HasTripleRepresentative x) (hperiod : ExactEventualPeriod x ℓ) :
    B x≤(uniformDigitBound ℓ : ℕ∞) :=
  (B_le_iff x (uniformDigitBound ℓ)).mpr (eventualBound_uniformDigitBound hclass hperiod)

/-- Uniform eventual boundedness of the whole successful period stratum. -/
theorem exists_uniform_eventual_bound (ℓ : ℕ) :
    ∃C : ℕ, ∀x : ℝ, HasTripleRepresentative x → ExactEventualPeriod x ℓ → EventualBound x C :=
  ⟨uniformDigitBound ℓ,fun _ hc hp => eventualBound_uniformDigitBound hc hp⟩

end VV.Problem4


