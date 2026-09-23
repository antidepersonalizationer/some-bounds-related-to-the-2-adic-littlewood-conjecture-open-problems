import VV.BBEKEntropyNets
import VV.P7BoxCover

/-! The standard passage from finite packing growth to geometric covers. -/

noncomputable section
open Set Filter Metric
open scoped Topology ENNReal

namespace VV.BBEKEntropyBox
open BBEKDynamics BBEKEntropyNets P7BoxCover

theorem parameterPackingCard_attained {S : Set (ℝ × Q2)} {η : ℝ}
    (hfin : parameterPackingCard S η < ⊤) :
    ∃ s : Finset (ℝ × Q2), IsParameterPacking S η s ∧
      (s.card : ℕ∞) = parameterPackingCard S η := by
  haveI : Nonempty {s : Finset (ℝ × Q2) // IsParameterPacking S η s} :=
    ⟨⟨∅,⟨by simp,by simp⟩⟩⟩
  have he : parameterPackingCard S η =
      ⨆ s : {s : Finset (ℝ × Q2) // IsParameterPacking S η s}, (s.val.card : ℕ∞) := by
    simp only [parameterPackingCard,iSup_subtype']
  obtain ⟨s,hs⟩ := ENat.exists_eq_iSup_of_lt_top (he ▸ hfin)
  exact ⟨s.val,s.property,hs.trans he.symm⟩

theorem parameterPackingCard_cover {S : Set (ℝ × Q2)} {η : ℝ} (hη : 0 < η)
    (hfin : parameterPackingCard S η < ⊤) :
    ∃ s : Finset (ℝ × Q2), (s.card : ℕ∞) = parameterPackingCard S η ∧
      ∀ z ∈ S, ∃ w ∈ s, dist z w < η := by
  classical
  obtain ⟨s,hs,hcard⟩ := parameterPackingCard_attained hfin
  refine ⟨s,hcard,?_⟩
  intro z hz
  by_contra! hmiss
  have hzs : z ∉ s := fun hz' => (hmiss z hz').not_lt (by simpa using hη)
  have hins : IsParameterPacking S η (insert z s) := by
    constructor
    · simpa only [Finset.coe_insert] using Set.insert_subset hz hs.1
    · intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact False.elim (hab rfl)
        · exact hmiss b hb
      · rcases hb with rfl | hb
        · simpa only [dist_comm] using hmiss a ha
        · exact hs.2 a ha b hb hab
  have hle : ((insert z s).card : ℕ∞) ≤ parameterPackingCard S η :=
    le_iSup₂ (α := ℕ∞) (insert z s) hins
  rw [← hcard,Finset.card_insert_of_notMem hzs] at hle
  exact (Nat.not_succ_le_self s.card) (by exact_mod_cast hle)

theorem packing_eventually_le_pow {S : Set (ℝ × Q2)} {ε : ℝ}
    (hgrowth : ExpGrowth.expGrowthSup (fun n : ℕ =>
      (parameterPackingCard S (ε / (4 : ℝ)^(n-1))).toENNReal) ≤ 0)
    {b : ℝ} (hb : 1 < b) : ∀ᶠ n : ℕ in atTop,
      (parameterPackingCard S (ε / (4 : ℝ)^(n-1))).toENNReal ≤ ENNReal.ofReal (b^n) := by
  have hlog : (0 : EReal) < ENNReal.log (ENNReal.ofReal b) := by
    rw [ENNReal.log_ofReal_of_pos (by linarith)]
    exact_mod_cast Real.log_pos hb
  have hh := ExpGrowth.eventually_le_exp (hgrowth.trans_lt hlog)
  filter_upwards [hh] with n hn
  rw [mul_comm,EReal.exp_nmul,ENNReal.exp_log,← ENNReal.ofReal_pow (by linarith : 0 ≤ b)] at hn
  exact hn

/-- Nonpositive exponential packing growth at one fixed geometric scale
implies the all-scales geometric covering formulation of zero upper box
dimension. The fixed separation prefactor is harmless. -/
theorem geometricZeroUpperBox_of_packing_growth {S : Set (ℝ × Q2)} {ε : ℝ}
    (hε : 0 < ε)
    (hgrowth : ExpGrowth.expGrowthSup (fun n : ℕ =>
      (parameterPackingCard S (ε / (4 : ℝ)^(n-1))).toENNReal) ≤ 0) :
    GeometricZeroUpperBox S := by
  classical
  intro ρ t hρ0 hρ1 ht
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hρ0 (by norm_num : (1/4 : ℝ) < 1)
  have hk0 : 0 < k := by
    by_contra! h
    have hkz : k = 0 := by omega
    simp only [hkz,pow_zero] at hk
    linarith
  let q : ℝ := (1/4 : ℝ)^k
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hqρ : q < ρ := hk
  let b : ℝ := t ^ (1 / ((k+1 : ℕ) : ℝ))
  have hb : 1 < b := Real.one_lt_rpow ht (by positivity)
  have hbpow : b^(k+1) = t := by
    dsimp [b]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ t)]
    have he : (1 / ((k+1 : ℕ) : ℝ)) * ((k+1 : ℕ) : ℝ) = 1 := by
      field_simp
    rw [he,Real.rpow_one]
  have hindex : Tendsto (fun n : ℕ => k*n+1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    have hmul : n ≤ k*n := Nat.le_mul_of_pos_left n hk0
    omega
  have hbound := hindex.eventually (packing_eventually_le_pow hgrowth hb)
  have hratio0 : 0 ≤ q/ρ := (div_pos hq0 hρ0).le
  have hratio1 : q/ρ < 1 := (div_lt_one hρ0).mpr hqρ
  have hlim : Tendsto (fun n : ℕ => (2*ε)*(q/ρ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1).const_mul (2*ε)
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hscale (n : ℕ) : ε / (4 : ℝ)^(k*n+1-1) = ε*q^n := by
    simp [q,div_eq_mul_inv,pow_mul,inv_pow]
  filter_upwards [hbound,hsmall,eventually_ge_atTop 1] with n hn hsn hn1
  let η : ℝ := ε / (4 : ℝ)^(k*n+1-1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηsmall : 2*η < ρ^n := by
    have hp : (0 : ℝ) < ρ^n := pow_pos hρ0 n
    have hm := mul_lt_mul_of_pos_right hsn hp
    have he : ((2*ε)*(q/ρ)^n)*ρ^n = (2*ε)*q^n := by
      rw [div_pow]
      field_simp
    rw [he,one_mul] at hm
    rw [show η = ε*q^n from hscale n]
    nlinarith
  have hfin : parameterPackingCard S η < ⊤ :=
    ENat.toENNReal_lt_top.mp (hn.trans_lt ENNReal.ofReal_lt_top)
  obtain ⟨s,hcard,hcover⟩ := parameterPackingCard_cover hη hfin
  have hcardb : (s.card : ℝ) ≤ b^(k*n+1) := by
    change (parameterPackingCard S η).toENNReal ≤ ENNReal.ofReal (b^(k*n+1)) at hn
    have hh : ENNReal.ofReal (s.card : ℝ) ≤ ENNReal.ofReal (b^(k*n+1)) := by
      simpa only [← hcard,ENat.toENNReal_coe,ENNReal.ofReal_natCast] using hn
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hcardt : (s.card : ℝ) ≤ t^n := by
    apply hcardb.trans
    calc
      b^(k*n+1) ≤ b^((k+1)*n) := pow_le_pow_right₀ hb.le (by rw [Nat.add_mul]; omega)
      _ = t^n := by rw [pow_mul,hbpow]
  refine ⟨s.card,fun i => ball ((s.equivFin.symm i).val) η,?_,?_,hcardt⟩
  · intro z hz
    obtain ⟨w,hw,hzw⟩ := hcover z hz
    refine ⟨s.equivFin ⟨w,hw⟩,?_⟩
    simpa using hzw
  · intro i a ha c hc
    calc
      dist a c ≤ dist a (s.equivFin.symm i).val + dist (s.equivFin.symm i).val c :=
        dist_triangle _ _ _
      _ < η+η := add_lt_add ha (by simpa only [dist_comm] using hc)
      _ < ρ^n := by linarith

theorem geometricZeroUpperBox_mono {P : Type*} [PseudoMetricSpace P] {S T : Set P}
    (hT : GeometricZeroUpperBox T) (hST : S ⊆ T) : GeometricZeroUpperBox S := by
  intro ρ t hρ0 hρ1 ht
  filter_upwards [hT ρ t hρ0 hρ1 ht] with n hn
  obtain ⟨m,U,hcover,hsmall,hcard⟩ := hn
  exact ⟨m,U,fun z hz => hcover z (hST hz),hsmall,hcard⟩

theorem geometricZeroUpperBox_empty {P : Type*} [PseudoMetricSpace P] :
    GeometricZeroUpperBox (∅ : Set P) := by
  intro ρ t _ _ ht
  apply Eventually.of_forall
  intro n
  refine ⟨0,fun i => Fin.elim0 i,?_,?_,?_⟩
  · simp
  · intro i
    exact Fin.elim0 i
  · simpa using pow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) n

theorem geometricZeroUpperBox_union {P : Type*} [PseudoMetricSpace P] {S T : Set P}
    (hS : GeometricZeroUpperBox S) (hT : GeometricZeroUpperBox T) :
    GeometricZeroUpperBox (S ∪ T) := by
  intro ρ t hρ0 hρ1 ht
  let b : ℝ := (t+1)/2
  have hb : 1 < b := by dsimp [b]; linarith
  have hbt : b < t := by dsimp [b]; linarith
  have ht0 : 0 < t := by linarith
  have hlim : Tendsto (fun n : ℕ => 2*(b/t)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ b/t)
        ((div_lt_one ht0).mpr hbt)).const_mul 2
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hS ρ b hρ0 hρ1 hb,hT ρ b hρ0 hρ1 hb,hsmall] with n hnS hnT hsn
  obtain ⟨m,U,hUS,hUsmall,hUcard⟩ := hnS
  obtain ⟨k,V,hVT,hVsmall,hVcard⟩ := hnT
  have hcard : ((m+k : ℕ) : ℝ) ≤ t^n := by
    have hm := mul_lt_mul_of_pos_right hsn (pow_pos ht0 n)
    have he : (2*(b/t)^n)*t^n = 2*b^n := by rw [div_pow]; field_simp
    rw [he,one_mul] at hm
    push_cast
    linarith
  refine ⟨m+k,Fin.addCases U V,?_,?_,hcard⟩
  · intro z hz
    rcases hz with hz | hz
    · obtain ⟨i,hi⟩ := hUS z hz
      exact ⟨Fin.castAdd k i,by simpa using hi⟩
    · obtain ⟨i,hi⟩ := hVT z hz
      exact ⟨Fin.natAdd m i,by simpa using hi⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hUsmall j
    · simpa using hVsmall j

theorem geometricZeroUpperBox_finset_union {P I : Type*} [PseudoMetricSpace P]
    (s : Finset I) (F : I → Set P) (hF : ∀ i ∈ s, GeometricZeroUpperBox (F i)) :
    GeometricZeroUpperBox (⋃ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (geometricZeroUpperBox_empty (P := P))
  | @insert a s ha ih =>
      have he : (⋃ i ∈ insert a s, F i) = F a ∪ (⋃ i ∈ s, F i) := by ext z; simp
      rw [he]
      exact geometricZeroUpperBox_union (hF a (by simp))
        (ih (fun i hi => hF i (by simp [hi])))

theorem geometricZeroUpperBox_of_entropy_nonpos
    {Y : Set BBEKQuotient.X} (hY : IsCompact Y) {t : ℝ} (ht : Real.log 2 ≤ t)
    (hforward : Set.MapsTo (BBEKEntropyExpansion.timeMap t) Y Y)
    (hentropy : compactEntropy Y hY hforward ≤ 0)
    (q : BBEKQuotient.X) {B S : Set (ℝ × Q2)} (hB : IsCompact B) (hSB : S ⊆ B)
    (hSY : ∀ z ∈ S, x z.1 z.2 • q ∈ Y) : GeometricZeroUpperBox S := by
  obtain ⟨R,hR,ε,hε,hgrowth⟩ := local_packing_growth_le_entropy hY ht hforward
  have hcover : B ⊆ ⋃ c : ℝ × Q2, ball c (R/2) := by
    intro z _
    exact mem_iUnion.mpr ⟨z,by simp [hR]⟩
  obtain ⟨s,hs⟩ := hB.elim_finite_subcover (fun c : ℝ × Q2 => ball c (R/2))
    (fun _ => isOpen_ball) hcover
  have hlocal (c : ℝ × Q2) : GeometricZeroUpperBox (S ∩ ball c (R/2)) := by
    apply geometricZeroUpperBox_of_packing_growth hε
    apply (hgrowth q (S ∩ ball c (R/2)) (fun z hz => hSY z hz.1) ?_).trans hentropy
    intro z hz w hw
    have hzw := dist_triangle z c w
    have hz' : dist z c < R/2 := hz.2
    have hw' : dist c w < R/2 := by rw [dist_comm]; exact hw.2
    linarith
  apply geometricZeroUpperBox_mono
    (geometricZeroUpperBox_finset_union s (fun c => S ∩ ball c (R/2)) (fun c _ => hlocal c))
  intro z hz
  obtain ⟨c,hcs,hzc⟩ := mem_iUnion₂.mp (hs (hSB hz))
  exact mem_iUnion₂.mpr ⟨c,hcs,hz,hzc⟩

/-- EK Lemma 4.2's first conclusion, expressed using the all-scales zero
upper box criterion: failure of zero upper box dimension in a compact
unstable parameter set forces positive actual topological entropy. -/
theorem entropy_pos_of_not_geometricZeroUpperBox
    {Y : Set BBEKQuotient.X} (hY : IsCompact Y) {t : ℝ} (ht : Real.log 2 ≤ t)
    (hforward : Set.MapsTo (BBEKEntropyExpansion.timeMap t) Y Y)
    (q : BBEKQuotient.X) {B S : Set (ℝ × Q2)} (hB : IsCompact B) (hSB : S ⊆ B)
    (hSY : ∀ z ∈ S, x z.1 z.2 • q ∈ Y) (hbox : ¬ GeometricZeroUpperBox S) :
    0 < compactEntropy Y hY hforward := by
  by_contra! h
  exact hbox (geometricZeroUpperBox_of_entropy_nonpos hY ht hforward h q hB hSB hSY)

end VV.BBEKEntropyBox
