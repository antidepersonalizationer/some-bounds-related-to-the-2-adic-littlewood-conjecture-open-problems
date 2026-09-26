import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Martingale.OptionalStopping
import VV.BBEKLeafEntropySubordinate

/-! A reverse-martingale maximal bound, uniform in the number of enlarged
leaf partitions. The conditional expectations below are literal ones. -/
noncomputable section
open Set MeasureTheory Filter Finset
open scoped ENNReal NNReal MeasureTheory
namespace VV.BBEKReverseMaximal

variable {Z : Type*} [MeasurableSpace Z]

def reverseFiltration (M : ℕ → MeasurableSpace Z) (hM : Antitone M)
    (hle : ∀ n, M n ≤ ‹MeasurableSpace Z›) (N : ℕ) :
    Filtration ℕ ‹MeasurableSpace Z› where
  seq n := M (N-n)
  mono' := fun _ _ hij => hM (Nat.sub_le_sub_left hij N)
  le' n := hle (N-n)

theorem positive_condExp_martingale (μ : Measure Z) [IsFiniteMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Z›) (f : Z → ℝ)
    (hf : 0 ≤ᵐ[μ] f) :
    Martingale (fun n z => max (μ[f | F n] z) 0) F μ := by
  have he (n : ℕ) : (fun z => max (μ[f | F n] z) 0) =ᵐ[μ] μ[f | F n] := by
    filter_upwards [condExp_nonneg hf] with z hz
    exact max_eq_left hz
  refine ⟨fun n => (stronglyMeasurable_condExp.measurable.max measurable_const).stronglyMeasurable,?_⟩
  intro i j hij
  exact (condExp_congr_ae (he j)).trans
    (((martingale_condExp f F μ).condExp_ae_eq hij).trans (he i).symm)

theorem reverse_condExp_maximal_finite (μ : Measure Z) [IsFiniteMeasure μ]
    (M : ℕ → MeasurableSpace Z) (hM : Antitone M)
    (hle : ∀ n, M n ≤ ‹MeasurableSpace Z›)
    (f : Z → ℝ) (hf : 0 ≤ᵐ[μ] f)
    (ε : ℝ≥0) (N : ℕ) :
    (ε : ℝ≥0∞) * μ {z | ∃ n ≤ N, (ε : ℝ) ≤ μ[f | M n] z} ≤
      ENNReal.ofReal (∫ z, f z ∂μ) := by
  let F := reverseFiltration M hM hle N
  let g : ℕ → Z → ℝ := fun n z => max (μ[f | F n] z) 0
  have hg := positive_condExp_martingale μ F f hf
  have hgnonneg : 0 ≤ g := fun n z => le_max_right _ _
  have hmax := maximal_ineq hg.submartingale hgnonneg (ε := ε) N
  let E := {z | (ε : ℝ) ≤ (range (N+1)).sup' nonempty_range_succ (fun k => g k z)}
  have hsub : {z | ∃ n ≤ N, (ε : ℝ) ≤ μ[f | M n] z} ⊆ E := by
    rintro z ⟨n,hn,he⟩
    have hindex : N-n ∈ range (N+1) := mem_range.mpr (by omega)
    have hv : μ[f | M n] z ≤ g (N-n) z := by
      dsimp only [g,F,reverseFiltration]
      rw [Nat.sub_sub_self hn]
      exact le_max_left _ _
    exact he.trans (hv.trans (le_sup' (fun k => g k z) hindex))
  have hgeq : g N =ᵐ[μ] μ[f | F N] := by
    filter_upwards [condExp_nonneg hf] with z hz
    exact max_eq_left hz
  calc
    (ε : ℝ≥0∞) * μ {z | ∃ n ≤ N, (ε : ℝ) ≤ μ[f | M n] z} ≤
        (ε : ℝ≥0∞) * μ E := mul_le_mul_left' (measure_mono hsub) _
    _ ≤ ENNReal.ofReal (∫ z in E, g N z ∂μ) := hmax
    _ ≤ ENNReal.ofReal (∫ z, g N z ∂μ) := ENNReal.ofReal_le_ofReal
      (setIntegral_le_integral (hg.integrable N) (ae_of_all _ (hgnonneg N)))
    _ = ENNReal.ofReal (∫ z, f z ∂μ) := by
      rw [integral_congr_ae hgeq,integral_condExp (F.le N)]

theorem reverse_condExp_maximal (μ : Measure Z) [IsFiniteMeasure μ]
    (M : ℕ → MeasurableSpace Z) (hM : Antitone M)
    (hle : ∀ n, M n ≤ ‹MeasurableSpace Z›)
    (f : Z → ℝ) (hf : 0 ≤ᵐ[μ] f) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * μ {z | ∃ n, (ε : ℝ) ≤ μ[f | M n] z} ≤
      ENNReal.ofReal (∫ z, f z ∂μ) := by
  let E : ℕ → Set Z := fun N => {z | ∃ n ≤ N, (ε : ℝ) ≤ μ[f | M n] z}
  have hE : Monotone E := by
    rintro N L hNL z ⟨n,hn,he⟩
    exact ⟨n,hn.trans hNL,he⟩
  have hU : {z | ∃ n, (ε : ℝ) ≤ μ[f | M n] z} = ⋃ N, E N := by
    ext z
    simp only [mem_setOf_eq,mem_iUnion,E]
    exact ⟨fun ⟨n,hn⟩ => ⟨n,n,le_rfl,hn⟩,fun ⟨_,n,_,hn⟩ => ⟨n,hn⟩⟩
  rw [hU,hE.measure_iUnion,ENNReal.mul_iSup]
  exact iSup_le (fun N => reverse_condExp_maximal_finite μ M hM hle f hf ε N)

theorem reverse_bad_set_maximal (μ : Measure Z) [IsFiniteMeasure μ]
    (M : ℕ → MeasurableSpace Z) (hM : Antitone M)
    (hle : ∀ n, M n ≤ ‹MeasurableSpace Z›)
    {B : Set Z} (hB : MeasurableSet B) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * μ {z | ∃ n, (ε : ℝ) ≤ μ[B.indicator (fun _ => (1 : ℝ)) | M n] z} ≤ μ B := by
  have hh := reverse_condExp_maximal μ M hM hle (B.indicator (fun _ => (1 : ℝ)))
    (ae_of_all _ fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z) ε
  simpa only [integral_indicator_const _ hB,smul_eq_mul,mul_one,measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top μ B)] using hh

theorem reverse_condKernel_maximal [StandardBorelSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (M : ℕ → MeasurableSpace Z) (hM : Antitone M)
    (hle : ∀ n, M n ≤ ‹MeasurableSpace Z›)
    {B : Set Z} (hB : MeasurableSet B) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * μ {z | ∃ n, (ε : ℝ) ≤ (ProbabilityTheory.condExpKernel μ (M n) z).real B} ≤ μ B := by
  have he : {z | ∃ n, (ε : ℝ) ≤ (ProbabilityTheory.condExpKernel μ (M n) z).real B}
      =ᵐ[μ] {z | ∃ n, (ε : ℝ) ≤ μ[B.indicator (fun _ => (1 : ℝ)) | M n] z} := by
    filter_upwards [ae_all_iff.mpr (fun n =>
      ProbabilityTheory.condExpKernel_ae_eq_condExp (μ := μ) (hle n) hB)] with z hz
    apply propext
    exact exists_congr (fun n => by rw [hz n])
  rw [measure_congr he]
  exact reverse_bad_set_maximal μ M hM hle hB ε

/-- One measurable set controls every enlarged conditional plaque at once. -/
theorem exists_reverse_condKernel_good_set [StandardBorelSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (M : ℕ → MeasurableSpace Z) (hM : Antitone M)
    (hle : ∀ n, M n ≤ ‹MeasurableSpace Z›)
    {B : Set Z} (hB : MeasurableSet B) (ε : ℝ≥0) :
    ∃ G : Set Z, MeasurableSet G ∧ (ε : ℝ≥0∞) * μ Gᶜ ≤ μ B ∧
      ∀ z ∈ G, ∀ n, (ProbabilityTheory.condExpKernel μ (M n) z).real B < ε := by
  let G := {z | ∀ n, (ProbabilityTheory.condExpKernel μ (M n) z).real B < ε}
  have hG : MeasurableSet G := by
    change MeasurableSet {z | ∀ n, (ProbabilityTheory.condExpKernel μ (M n) z).real B < ε}
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro n
    have hh := ((ProbabilityTheory.condExpKernel μ (M n)).measurable_coe hB).mono (hle n) le_rfl
    exact measurableSet_lt hh.ennreal_toReal measurable_const
  refine ⟨G,hG,?_,fun _ hz => hz⟩
  have he : Gᶜ = {z | ∃ n, (ε : ℝ) ≤ (ProbabilityTheory.condExpKernel μ (M n) z).real B} := by
    ext z
    simp only [G,mem_compl_iff,mem_setOf_eq,not_forall,not_lt]
  rw [he]
  exact reverse_condKernel_maximal μ M hM hle hB ε

section Codes
variable {Y : Type*} [MeasurableSpace Y]

def tailCode (f : Z → ℕ → Y) (n : ℕ) (z : Z) : ℕ → Y := fun k => f z (n+k)

theorem measurable_tailCode (f : Z → ℕ → Y) (hf : Measurable f) (n : ℕ) :
    Measurable (tailCode f n) := by
  exact measurable_pi_lambda _ (fun k => (measurable_pi_apply (n+k)).comp hf)

def tailSigma (f : Z → ℕ → Y) (n : ℕ) : MeasurableSpace Z :=
  (inferInstance : MeasurableSpace (ℕ → Y)).comap (tailCode f n)

theorem tailSigma_le (f : Z → ℕ → Y) (hf : Measurable f) (n : ℕ) :
    tailSigma f n ≤ ‹MeasurableSpace Z› := (measurable_tailCode f hf n).comap_le

omit [MeasurableSpace Z] in
theorem tailSigma_antitone (f : Z → ℕ → Y) : Antitone (tailSigma f) := by
  intro n m hnm
  have hm : @Measurable Z (ℕ → Y) (tailSigma f n) _ (tailCode f n) :=
    measurable_iff_comap_le.mpr le_rfl
  have hs : Measurable (fun a : ℕ → Y => fun k => a (m-n+k)) :=
    measurable_pi_lambda _ (fun k => measurable_pi_apply _)
  have hh := hs.comp hm
  have he : (fun a : ℕ → Y => fun k => a (m-n+k)) ∘ tailCode f n = tailCode f m := by
    funext z k
    dsimp [tailCode]
    congr 1
    omega
  rw [he] at hh
  exact hh.comap_le

/-- In particular the estimate applies to the actual past-plaque code by
forgetting finitely many coordinates. No filtration compatibility is assumed. -/
theorem tail_code_bad_set_maximal (μ : Measure Z) [IsFiniteMeasure μ]
    (f : Z → ℕ → Y) (hf : Measurable f) {B : Set Z} (hB : MeasurableSet B) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * μ {z | ∃ n,
      (ε : ℝ) ≤ μ[B.indicator (fun _ => (1 : ℝ)) | tailSigma f n] z} ≤ μ B :=
  reverse_bad_set_maximal μ (tailSigma f) (tailSigma_antitone f) (tailSigma_le f hf) hB ε

end Codes

end VV.BBEKReverseMaximal
