import VV.P4SymbolicOutput
import VV.P4Counting

/-! The actual finite encoding for Problem 4. The relation `Fits` below is
constructed for every genuine rooted word, and its fibers are proved to be
singletons using the normalized literal transducer. -/

namespace VV.P4Symbolic
open Hurwitz

def digitType (a : ℤ) : Fin 4 :=
  if a=1 then 0 else if a=2 then 1 else if a%2=1 then 2 else 3

def digitVariable (a : ℤ) : ℤ :=
  if a=1 ∨ a=2 then 0 else (a-typeBase (digitType a))/2

theorem digit_coding {a : ℤ} (ha : 1≤a) :
    0≤digitVariable a ∧ inputDigit (digitType a) (digitVariable a)=a := by
  have hm : a%2=0 ∨ a%2=1 := by omega
  rcases hm with hm|hm <;>
    by_cases h1 : a=1 <;> by_cases h2 : a=2 <;>
    simp [digitVariable,digitType,h1,h2,hm,inputDigit,typeBase,large] <;> omega

theorem exists_vector {α : Type*} {n : ℕ} (w : List α) (hlen : w.length=n) :
    ∃ a : Fin n → α,List.ofFn a=w := by
  subst n
  exact ⟨w.get,List.ofFn_get w⟩

theorem inputWord_ofFn {n : ℕ} (types : Fin n → Fin 4) (u : Fin n → ℤ) :
    inputWord types u (List.finRange n)=List.ofFn (fun i => inputDigit (types i) (u i)) :=
  List.ofFn_eq_map.symm

theorem word_coding {n : ℕ} (w : List ℤ) (hlen : w.length=n) (hw : ∀ a∈w,1≤a) :
    ∃ types : Fin n → Fin 4, ∃ u : Fin n → ℤ,
      (∀ i,0≤u i) ∧ w=inputWord types u (List.finRange n) := by
  obtain ⟨a,ha⟩ := exists_vector w hlen
  have hapos (i : Fin n) : 1≤a i := hw (a i) (by rw [← ha]; simp)
  refine ⟨fun i => digitType (a i),fun i => digitVariable (a i),
    fun i => (digit_coding (hapos i)).1,?_⟩
  rw [inputWord_ofFn,← ha]
  apply congrArg List.ofFn
  funext i
  exact (digit_coding (hapos i)).2.symm

def pairLeft : Fin 3 → State
  | ⟨0,_⟩ => .D
  | ⟨1,_⟩ => .D
  | ⟨_,_⟩ => .H0

def pairRight : Fin 3 → State
  | ⟨0,_⟩ => .H0
  | ⟨_,_⟩ => .H1

theorem pair_distinct (k : Fin 3) : pairLeft k ≠ pairRight k := by fin_cases k <;> decide

theorem good_pair_code {x : ℝ} (h : HasGoodPair x) :
    ∃ k : Fin 3,TailEquivalent x (P5RealCursor.stateValue (pairLeft k) x) ∧
      TailEquivalent x (P5RealCursor.stateValue (pairRight k) x) := by
  obtain ⟨s,t,hst,hs,ht⟩ := h
  cases s <;> cases t
  · exact False.elim (hst rfl)
  · exact ⟨0,hs,ht⟩
  · exact ⟨1,hs,ht⟩
  · exact ⟨0,ht,hs⟩
  · exact False.elim (hst rfl)
  · exact ⟨2,hs,ht⟩
  · exact ⟨1,ht,hs⟩
  · exact ⟨2,ht,hs⟩
  · exact False.elim (hst rfl)

def shift {n : ℕ} (hn : 0<n) (r : Fin n) : Equiv.Perm (Fin n) := by
  letI : NeZero n := ⟨by omega⟩
  exact Equiv.addLeft r

theorem shift_val {n : ℕ} (hn : 0<n) (r j : Fin n) :
    (shift hn r j).val=(r.val+j.val)%n := rfl

theorem block_phase {n : ℕ} (hn : 0<n) (types : Fin n → Fin 4) (u : Fin n → ℤ)
    (hu : ∀ i,0≤u i) {x : ℝ} (hx : CycleModel x (inputWord types u (List.finRange n)))
    (r : Fin n) :
    P5Period.digitBlock x r.val n =
      List.ofFn (fun j => inputDigit (types (shift hn r j)) (u (shift hn r j))) := by
  have hw : ∀ a ∈ inputWord types u (List.finRange n),1≤a := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    exact inputDigit_positive (types i) (hu i)
  have hlen : (inputWord types u (List.finRange n)).length=n := by simp [inputWord]
  have hp : DigitPeriod x n := hlen ▸ hx.digitPeriod hw
  have hd := hx.digitBlock hw
  rw [hlen,P5Period.digitBlock_eq_ofFn,inputWord_ofFn] at hd
  have hd' := List.ofFn_injective hd
  rw [P5Period.digitBlock_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  rw [Problem4.period_digit_mod hp (r.val+j.val)]
  have h := congrFun hd' (shift hn r j)
  simpa only [Nat.zero_add,shift_val] using h

theorem output_phase {n : ℕ} (hn : 2≤n) (types : Fin n → Fin 4) (u : Fin n → ℤ)
    (hu : ∀ i,0≤u i) {x : ℝ} (hx : CycleModel x (inputWord types u (List.finRange n)))
    (hmin : Problem4.ExactEventualPeriod x n) (hclass : HasTripleRepresentative x)
    (s : State) (hgood : TailEquivalent x (P5RealCursor.stateValue s x)) :
    ∃ r : Fin n,(output types s).map (fun e => eval e u) =
      List.ofFn (fun j => inputDigit (types (shift (by omega) r j))
        (u (shift (by omega) r j))) := by
  obtain ⟨y,hy,hv,hl,hxy,_⟩ := output_model types s u hu hx hmin hn hclass hgood
  have hw : ∀ a ∈ inputWord types u (List.finRange n),1≤a := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    exact inputDigit_positive (types i) (hu i)
  have hlen : (inputWord types u (List.finRange n)).length=n := by simp [inputWord]
  obtain ⟨r,hr,he⟩ := cycle_block_alignment hx hy hw hv
    (by simpa only [List.length_map,hlen] using hl) (by omega) hxy
  refine ⟨⟨r,by omega⟩,?_⟩
  rw [he,hlen,block_phase (by omega) types u hu hx ⟨r,by omega⟩]

def Fits {n : ℕ} (hn : 0<n) (w : Problem4.RootedWord n) (T : Problem4.Template n) : Prop :=
  ∃ u : Fin n → ℤ, (∀ i,0≤u i) ∧ w.val=inputWord T.1 u (List.finRange n) ∧
    (output T.1 (pairLeft T.2.1)).map (fun e => eval e u) =
      List.ofFn (fun j => inputDigit (T.1 (shift hn T.2.2.1 j)) (u (shift hn T.2.2.1 j))) ∧
    (output T.1 (pairRight T.2.1)).map (fun e => eval e u) =
      List.ofFn (fun j => inputDigit (T.1 (shift hn T.2.2.2 j)) (u (shift hn T.2.2.2 j)))

theorem exists_fits {n : ℕ} (hn : 0<n) (w : Problem4.RootedWord n) :
    ∃ T : Problem4.Template n,Fits hn w T := by
  obtain ⟨x,hx,hw,hlen,hmin,hclass,hgood⟩ := w.property
  obtain ⟨types,u,hu,hword⟩ := word_coding w.val hlen hw
  have hx' : CycleModel x (inputWord types u (List.finRange n)) := hword ▸ hx
  have hn2 : 2≤n := by
    obtain ⟨y,hxy,hy⟩ := hclass
    have hm := (Problem4.exactEventualPeriod_iff_of_tailEquivalent hxy n).mp hmin
    have hh := Problem4.period_at_least_three_of_triple hy hm.1 hm.2.1
    omega
  obtain ⟨k,hk₁,hk₂⟩ := good_pair_code hgood
  obtain ⟨r,hr⟩ := output_phase hn2 types u hu hx' hmin hclass (pairLeft k) hk₁
  obtain ⟨s,hs⟩ := output_phase hn2 types u hu hx' hmin hclass (pairRight k) hk₂
  exact ⟨⟨types,k,r,s⟩,u,hu,hword,hr,hs⟩

theorem fits_unique {n : ℕ} (hn : 0<n) {w v : Problem4.RootedWord n}
    {T : Problem4.Template n} (hw : Fits hn w T) (hv : Fits hn v T) : w=v := by
  obtain ⟨u,_,hwu,huE,huF⟩ := hw
  obtain ⟨z,_,hvz,hzE,hzF⟩ := hv
  have hlenE : (output T.1 (pairLeft T.2.1)).length=n := by
    have h := congrArg List.length huE
    simpa only [List.length_map,List.length_ofFn] using h
  have hlenF : (output T.1 (pairRight T.2.1)).length=n := by
    have h := congrArg List.length huF
    simpa only [List.length_map,List.length_ofFn] using h
  obtain ⟨E,hE⟩ := exists_vector _ hlenE
  obtain ⟨F,hF⟩ := exists_vector _ hlenF
  rw [← hE,List.map_ofFn] at huE hzE
  rw [← hF,List.map_ofFn] at huF hzF
  have he := normalized_pair_unique hn T.1 (pairLeft T.2.1) (pairRight T.2.1)
    (pair_distinct T.2.1) u z E F hE hF (shift hn T.2.2.1) (shift hn T.2.2.2)
    (congrFun (List.ofFn_injective huE)) (congrFun (List.ofFn_injective hzE))
    (congrFun (List.ofFn_injective huF)) (congrFun (List.ofFn_injective hzF))
  apply Subtype.ext
  rw [hwu,hvz,inputWord_ofFn,inputWord_ofFn]
  exact congrArg List.ofFn (funext he)

theorem rooted_template_encoding {n : ℕ} (hn : 0<n) :
    ∃ encode : Problem4.RootedWord n → Problem4.Template n,Function.Injective encode := by
  classical
  choose encode hencode using exists_fits hn
  refine ⟨encode,fun w v he => ?_⟩
  exact fits_unique hn (he ▸ hencode w) (hencode v)

end VV.P4Symbolic

namespace VV.Problem4

/-- The previously missing encoding is now constructed from the actual
Hurwitz transducer, with every infinite/theoretical step proved. -/
theorem hasRootedEncoding {ℓ : ℕ} (hℓ : 0<ℓ) : HasRootedEncoding ℓ :=
  rootedEncoding_of_word_encoding (P4Symbolic.rooted_template_encoding hℓ)

/-- Unconditional Problem 4: finitely many genuine least-period tail classes,
with the explicit bound obtained in the research conversation. -/
theorem problem4_finiteness_and_bound {ℓ : ℕ} (hℓ : 0<ℓ) :
    Finite (Class ℓ) ∧ Nat.card (Class ℓ) ≤ 3*ℓ*4^ℓ :=
  actual_finiteness_and_bound hℓ (hasRootedEncoding hℓ)

theorem problem4_all_periods (ℓ : ℕ) :
    Finite (Class ℓ) ∧ Nat.card (Class ℓ) ≤ 3*ℓ*4^ℓ := by
  by_cases hℓ : 0<ℓ
  · exact problem4_finiteness_and_bound hℓ
  · have hzero : ℓ=0 := by omega
    subst ℓ
    letI := isEmpty_class_small (show 0≤2 by omega)
    exact ⟨inferInstance,by simp [Nat.card_of_isEmpty]⟩

end VV.Problem4
