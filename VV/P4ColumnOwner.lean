import VV.P4Columns

namespace VV.P4Symbolic
open scoped BigOperators

theorem single_nonzero_of_dvd_sum {n : ℕ} (a : Fin n → ℤ) (c : ℤ) (hc : 0<c)
    (ha : ∀ j,0≤a j) (hd : ∀ j,c ∣ a j) (hs : ∑ j,a j=c) :
    ∃ i : Fin n, ∀ j,a j=if j=i then c else 0 := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : (∑ j,a j)≠0)
  obtain ⟨k,hk⟩ := hd i
  have hip : 0<a i := lt_of_le_of_ne (ha i) (Ne.symm hi)
  have hkp : 0<k := by nlinarith
  have hic : c≤a i := by nlinarith
  have his : a i≤∑ j,a j := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ _)
  have hie : a i=c := by omega
  have hrest : ∑ j ∈ Finset.univ.erase i,a j=0 := by
    have hh := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
    omega
  refine ⟨i,fun j => ?_⟩
  by_cases hji : j=i
  · simpa [hji] using hie
  · simp only [hji,if_false]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp hrest j (by simp [hji])

theorem owner_of_column {n : ℕ} (hn : 0<n) (E : Fin n → Expr n)
    (hE : ∀ j,Valid (E j)) (i : Fin n) (c : ℤ) (hc : 0≤c)
    (hd : ∀ j,c ∣ (E j).coeff i) (hs : ∑ j,(E j).coeff i=c) :
    ∃ k : Fin n, ∀ j,(E j).coeff i=if j=k then c else 0 := by
  by_cases hzero : c=0
  · refine ⟨⟨0,hn⟩,fun j => ?_⟩
    have hj : (E j).coeff i=0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hE j).2.1 i)).mp
        (hs.trans hzero) j (Finset.mem_univ _)
    simp [hj,hzero]
  · exact single_nonzero_of_dvd_sum (fun j => (E j).coeff i) c (by omega)
      (fun j => (hE j).2.1 i) hd hs

theorem column_ofFn {n m : ℕ} (E : Fin m → Expr n) (i : Fin n) :
    column (List.ofFn E) i = ∑ j,(E j).coeff i := by
  simp [column,List.map_ofFn,List.sum_ofFn]

theorem inputDigit_sub {n : ℕ} (types : Fin n → Fin 4) (u v : Fin n → ℤ) (i : Fin n) :
    (inputDigit (types i) (u i) : ℝ)-inputDigit (types i) (v i) =
      if large (types i) then 2*((u i:ℝ)-v i) else 0 := by
  dsimp [inputDigit]
  split_ifs <;> push_cast <;> ring

theorem eval_sub {n : ℕ} (e : Expr n) (u v : Fin n → ℤ) :
    (eval e u : ℝ)-eval e v = ∑ i,(e.coeff i:ℝ)*((u i:ℝ)-v i) := by
  simp only [eval,Int.cast_add,Int.cast_sum,Int.cast_mul,mul_sub,Finset.sum_sub_distrib]
  ring

/-- Coefficient ownership converts an actual symbolic output equation into
the precise no-splitting transport equation used by the two-branch kernel. -/
theorem output_difference {n : ℕ} (types : Fin n → Fin 4) (u v : Fin n → ℤ)
    (E : Fin n → Expr n) (σ : Equiv.Perm (Fin n)) (owner : Fin n → Fin n)
    (c : Fin n → ℤ) (branch : Fin n → Bool)
    (hcoeff : ∀ j i,(E j).coeff i=if j=owner i then c i else 0)
    (hscale : ∀ i,(c i:ℝ)*((u i:ℝ)-v i) =
      Problem4.scale (branch i) *
        (if large (types i) then 2*((u i:ℝ)-v i) else 0))
    (hu : ∀ j,eval (E j) u=inputDigit (types (σ j)) (u (σ j)))
    (hv : ∀ j,eval (E j) v=inputDigit (types (σ j)) (v (σ j))) :
    ∀ j, (if large (types j) then 2*((u j:ℝ)-v j) else 0) =
      Problem4.push (fun i => σ (owner i)) (fun i => Problem4.scale (branch i))
        (fun i => if large (types i) then 2*((u i:ℝ)-v i) else 0) j := by
  intro j
  have he := eval_sub (E (σ.symm j)) u v
  rw [hu,hv,σ.apply_symm_apply,inputDigit_sub] at he
  rw [he]
  unfold Problem4.push
  apply Finset.sum_congr rfl
  intro i _
  rw [hcoeff]
  by_cases hi : σ (owner i)=j
  · have hh : σ.symm j=owner i := by rw [← hi,σ.symm_apply_apply]
    simp only [hh,if_true,hi]
    exact hscale i
  · have hh : σ.symm j≠owner i := by
      intro hh
      apply hi
      rw [← hh,σ.apply_symm_apply]
    simp [hh,hi]

theorem affine_pair_unique {n : ℕ} (types : Fin n → Fin 4) (u v : Fin n → ℤ)
    (E F : Fin n → Expr n) (σ τ : Equiv.Perm (Fin n))
    (ownerE ownerF : Fin n → Fin n) (c d : Fin n → ℤ)
    (a b : Fin n → Bool)
    (hE : ∀ j i,(E j).coeff i=if j=ownerE i then c i else 0)
    (hF : ∀ j i,(F j).coeff i=if j=ownerF i then d i else 0)
    (hc : ∀ i,(c i:ℝ)*((u i:ℝ)-v i)=Problem4.scale (a i)*
      (if large (types i) then 2*((u i:ℝ)-v i) else 0))
    (hd : ∀ i,(d i:ℝ)*((u i:ℝ)-v i)=Problem4.scale (b i)*
      (if large (types i) then 2*((u i:ℝ)-v i) else 0))
    (hno : ∀ i,¬(a i=true ∧ b i=true))
    (huE : ∀ j,eval (E j) u=inputDigit (types (σ j)) (u (σ j)))
    (hvE : ∀ j,eval (E j) v=inputDigit (types (σ j)) (v (σ j)))
    (huF : ∀ j,eval (F j) u=inputDigit (types (τ j)) (u (τ j)))
    (hvF : ∀ j,eval (F j) v=inputDigit (types (τ j)) (v (τ j))) :
    ∀ i,inputDigit (types i) (u i)=inputDigit (types i) (v i) := by
  have he := output_difference types u v E σ ownerE c a hE hc huE hvE
  have hf := output_difference types u v F τ ownerF d b hF hd huF hvF
  have hz := Problem4.two_branch_kernel (fun i => σ (ownerE i)) (fun i => τ (ownerF i))
    a b (fun i => if large (types i) then 2*((u i:ℝ)-v i) else 0) hno he hf
  intro i
  have heq : (inputDigit (types i) (u i):ℝ)=inputDigit (types i) (v i) := by
    apply sub_eq_zero.mp
    rw [inputDigit_sub]
    exact hz i
  exact_mod_cast heq

end VV.P4Symbolic
