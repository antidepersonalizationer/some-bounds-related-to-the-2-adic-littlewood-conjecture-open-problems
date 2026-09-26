import VV.P4PeriodFourEvenCases
import VV.P4PeriodFourOddCases
import VV.P4PeriodFourEvenOddCases

/-!
# Exact successful tail class of least period four

The symbolic branch proofs force a cycle rooted at a largest digit to be
[5,2,1,2]. Rotations then give exactly four rooted words and exactly one
actual tail-equivalence class. The explicit quadratic supplies existence.
-/

noncomputable section
namespace VV.Problem4
open Hurwitz P5RealCursor PeriodFourCases
theorem canonical_max_four {x : ℝ} {a b c d : ℤ}
    (hx : CycleModel x [a,b,c,d]) (hw : ∀e∈[a,b,c,d],1≤e)
    (hp : ExactEventualPeriod x 4) (hclass : HasTripleRepresentative x)
    (hg : HasGoodPair x) (hmax : b≤a ∧ c≤a ∧ d≤a) :
    a=5 ∧ b=2 ∧ c=1 ∧ d=2 := by
  have hapos : 1≤a := hw a (by simp)
  have hbpos : 1≤b := hw b (by simp)
  have hcpos : 1≤c := hw c (by simp)
  have hdpos : 1≤d := hw d (by simp)
  rcases parity_four hx hclass with he|he|he
  · obtain ⟨hpa,hpb,hpc,hpd⟩ := he
    by_cases hsa : a=2
    · by_cases hsb : b=2
      · by_cases hsc : c=2
        · by_cases hsd : d=2
          · exact case_1111 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_1113 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=2
          · exact case_1131 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_1133 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
      · by_cases hsc : c=2
        · by_cases hsd : d=2
          · exact case_1311 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_1313 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=2
          · exact case_1331 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_1333 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
    · by_cases hsb : b=2
      · by_cases hsc : c=2
        · by_cases hsd : d=2
          · exact case_3111 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_3113 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=2
          · exact case_3131 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_3133 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
      · by_cases hsc : c=2
        · by_cases hsd : d=2
          · exact case_3311 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_3313 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=2
          · exact case_3331 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_3333 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
  · obtain ⟨hpa,hpb,hpc,hpd⟩ := he
    by_cases hsa : a=1
    · by_cases hsb : b=2
      · by_cases hsc : c=1
        · by_cases hsd : d=2
          · exact case_0101 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_0103 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=2
          · exact case_0121 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_0123 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
      · by_cases hsc : c=1
        · by_cases hsd : d=2
          · exact case_0301 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_0303 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=2
          · exact case_0321 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_0323 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
    · by_cases hsb : b=2
      · by_cases hsc : c=1
        · by_cases hsd : d=2
          · exact case_2101 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_2103 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=2
          · exact case_2121 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_2123 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
      · by_cases hsc : c=1
        · by_cases hsd : d=2
          · exact case_2301 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_2303 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=2
          · exact case_2321 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_2323 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
  · obtain ⟨hpa,hpb,hpc,hpd⟩ := he
    by_cases hsa : a=2
    · by_cases hsb : b=1
      · by_cases hsc : c=2
        · by_cases hsd : d=1
          · exact case_1010 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_1012 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=1
          · exact case_1030 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_1032 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
      · by_cases hsc : c=2
        · by_cases hsd : d=1
          · exact case_1210 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_1212 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=1
          · exact case_1230 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_1232 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
    · by_cases hsb : b=1
      · by_cases hsc : c=2
        · by_cases hsd : d=1
          · exact case_3010 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_3012 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=1
          · exact case_3030 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_3032 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
      · by_cases hsc : c=2
        · by_cases hsd : d=1
          · exact case_3210 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_3212 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
        · by_cases hsd : d=1
          · exact case_3230 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)
          · exact case_3232 hx hw hp hclass hg hmax (by omega) (by omega) (by omega) (by omega)

theorem list_length_four {w : List ℤ} (hw : w.length=4) :
    ∃ a b c d,w=[a,b,c,d] := by
  cases w with
  | nil => simp at hw
  | cons a w =>
    have hh : w.length=3 := by simpa using hw
    obtain ⟨b,c,d,he⟩ := List.length_eq_three.mp hh
    exact ⟨a,b,c,d,by rw [he]⟩

theorem rootedWord_four_form (w : RootedWord 4) :
    w.val=[5,2,1,2] ∨ w.val=[2,1,2,5] ∨ w.val=[1,2,5,2] ∨ w.val=[2,5,2,1] := by
  obtain ⟨x,hx,hw,hlen,hmin,hclass,hgood⟩ := w.property
  obtain ⟨a,b,c,d,hword⟩ := list_length_four hlen
  rw [hword] at hx hw
  let r : RootedCycle 4 := ⟨x,[a,b,c,d],hx,hw,rfl,hmin,hclass,hgood⟩
  have hrot1 : (r.rotate 1).w=[b,c,d,a] := by
    obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := digits_four hx hw
    change P5Period.digitBlock x 1 4=_
    simp [P5Period.digitBlock,h1,h2,h3,h4]
  have hrot2 : (r.rotate 2).w=[c,d,a,b] := by
    obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := digits_four hx hw
    change P5Period.digitBlock x 2 4=_
    simp [P5Period.digitBlock,h2,h3,h4,h5]
  have hrot3 : (r.rotate 3).w=[d,a,b,c] := by
    obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := digits_four hx hw
    change P5Period.digitBlock x 3 4=_
    simp [P5Period.digitBlock,h3,h4,h5,h6]
  have hmax : (b≤a ∧ c≤a ∧ d≤a) ∨ (c≤b ∧ d≤b ∧ a≤b) ∨
      (d≤c ∧ a≤c ∧ b≤c) ∨ (a≤d ∧ b≤d ∧ c≤d) := by omega
  rcases hmax with hm|hm|hm|hm
  · obtain ⟨rfl,rfl,rfl,rfl⟩ := canonical_max_four hx hw hmin hclass hgood hm
    simp [hword]
  · have hm' := (r.rotate 1).model
    have hp' := (r.rotate 1).positive
    rw [hrot1] at hm' hp'
    obtain ⟨rfl,rfl,rfl,rfl⟩ := canonical_max_four hm' hp' (r.rotate 1).least
      (r.rotate 1).triple (r.rotate 1).good hm
    simp [hword]
  · have hm' := (r.rotate 2).model
    have hp' := (r.rotate 2).positive
    rw [hrot2] at hm' hp'
    obtain ⟨rfl,rfl,rfl,rfl⟩ := canonical_max_four hm' hp' (r.rotate 2).least
      (r.rotate 2).triple (r.rotate 2).good hm
    simp [hword]
  · have hm' := (r.rotate 3).model
    have hp' := (r.rotate 3).positive
    rw [hrot3] at hm' hp'
    obtain ⟨rfl,rfl,rfl,rfl⟩ := canonical_max_four hm' hp' (r.rotate 3).least
      (r.rotate 3).triple (r.rotate 3).good hm
    simp [hword]

theorem card_rootedWord_four_le : Nat.card (RootedWord 4)≤4 := by
  let S : Finset (List ℤ) := {[5,2,1,2],[2,1,2,5],[1,2,5,2],[2,5,2,1]}
  let f : RootedWord 4 → {w // w∈S} := fun w =>
    ⟨w.val,by simpa [S] using rootedWord_four_form w⟩
  have hf : Function.Injective f := by
    intro w v he
    apply Subtype.ext
    exact congrArg (fun z : {w : List ℤ // w∈S} => z.val) he
  have hh := Nat.card_le_card_of_injective f hf
  have hS : Nat.card {w : List ℤ // w∈S}=4 := by
    change Nat.card ↥S=4
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    norm_num [S]
  simpa only [hS] using hh

theorem card_class_four : Nat.card (Class 4)=1 := by
  have hh := card_rootedWord_four_le
  rw [card_rootedWord] at hh
  have hp := card_class_four_pos
  omega

/-- The entire successful period-four stratum is the class of [5,2,1,2]. -/
theorem period_four_iff {x : ℝ} :
    HasTripleRepresentative x ∧ ExactEventualPeriod x 4 ↔
      TailEquivalent x periodFourValue := by
  constructor
  · rintro ⟨⟨y,hxy,hy⟩,hp⟩
    let r : Representative 4 :=
      ⟨y,hy,(exactEventualPeriod_iff_of_tailEquivalent hxy 4).mp hp⟩
    have hs : Subsingleton (Class 4) := (Nat.card_eq_one_iff_unique.mp card_class_four).1
    have he := hs.elim (toClass r) (toClass periodFourRepresentative)
    exact hxy.trans ((toClass_eq_iff r periodFourRepresentative).mp he)
  · intro h
    exact ⟨⟨periodFourValue,h,periodFourValue_triple⟩,
      (exactEventualPeriod_iff_of_tailEquivalent h 4).mpr periodFourValue_least⟩

theorem B_eq_five_of_period_four {x : ℝ} (hc : HasTripleRepresentative x)
    (hp : ExactEventualPeriod x 4) : B x=5 :=
  (period_four_iff.mp ⟨hc,hp⟩).B_eq.trans periodFourValue_B




def periodFourCycle : RootedCycle 4 :=
  ⟨periodFourValue,[5,2,1,2],periodFourValue_model,by simp,rfl,
    periodFourValue_least,⟨periodFourValue,TailEquivalent.refl _,periodFourValue_triple⟩,
    goodPair_of_triple periodFourValue_triple⟩

theorem uniformAlphabet_four : uniformAlphabet 4={1,2,5} := by
  ext a
  constructor
  · intro ha
    obtain ⟨w,hw⟩ := (mem_uniformAlphabet_iff 4 a).mp ha
    rcases rootedWord_four_form w with he|he|he|he <;>
      simp [he] at hw <;> simp [← hw]
  · intro ha
    have h1 : (1:ℤ)∈uniformAlphabet 4 := by
      have hh := periodFourCycle.digit_mem_uniformAlphabet 2
      simpa only [periodFourCycle,periodFourValue_digits.2.2.1] using hh
    have h2 : (2:ℤ)∈uniformAlphabet 4 := by
      have hh := periodFourCycle.digit_mem_uniformAlphabet 1
      simpa only [periodFourCycle,periodFourValue_digits.2.1] using hh
    have h5 : (5:ℤ)∈uniformAlphabet 4 := by
      have hh := periodFourCycle.digit_mem_uniformAlphabet 0
      simpa only [periodFourCycle,periodFourValue_digits.1] using hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl
    · exact h1
    · exact h2
    · exact h5

theorem uniformDigitBound_four : uniformDigitBound 4=5 := by
  norm_num [uniformDigitBound,uniformAlphabet_four,Int.toNat]

end VV.Problem4

