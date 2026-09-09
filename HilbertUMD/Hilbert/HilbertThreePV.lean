import HilbertUMD.Hilbert.HilbertConstant
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Localization of the real-line principal-value transform from L² to L³. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HilbertUMD.HilbertThreePV

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

def cutoff (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (Icc (-(n : ℝ)) n).indicator f

theorem cutoff_memLp {f : ℝ → ℝ} {p : ℝ≥0∞} (hf : MemLp f p volume) (n : ℕ) :
    MemLp (cutoff n f) p volume := hf.indicator measurableSet_Icc

theorem cutoff_memLp_two {f : ℝ → ℝ} (hf : MemLp f 3 volume) (n : ℕ) :
    MemLp (cutoff n f) 2 volume := by
  apply (cutoff_memLp hf n).mono_exponent_of_measure_support_ne_top
    (s := Icc (-(n : ℝ)) n)
  · intro t ht
    exact indicator_of_notMem ht f
  · exact (measure_Icc_lt_top).ne
  · norm_num

theorem eventually_cutoff_eq (f : ℝ → ℝ) (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, cutoff n f t = f t := by
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  filter_upwards [eventually_ge_atTop N] with n hn
  apply indicator_of_mem
  have h : |t| ≤ (n : ℝ) := le_trans hN.le (by exact_mod_cast hn)
  exact abs_le.mp h

theorem cutoff_tendsto_three {f : ℝ → ℝ} (hf : MemLp f 3 volume) :
    Tendsto (fun n => (cutoff_memLp hf n).toLp (cutoff n f)) atTop
      (𝓝 (hf.toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  have hi := hf.integrable_norm_pow (by decide : 3 ≠ 0)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun t => ‖cutoff n f t - f t‖ ^ 3) volume :=
    ((cutoff_memLp hf n).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 3
  have hbound (n : ℕ) : ∀ᵐ t ∂volume, ‖‖cutoff n f t - f t‖ ^ 3‖ ≤ ‖f t‖ ^ 3 := by
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ Icc (-(n : ℝ)) n
    · simp [cutoff, ht]
    · simp [cutoff, ht]
  have hlim : ∀ᵐ t ∂volume, Tendsto (fun n => ‖cutoff n f t - f t‖ ^ 3)
      atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro t
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_cutoff_eq f t] with n hn
    simp [hn]
  have hconv := tendsto_integral_of_dominated_convergence (fun t => ‖f t‖ ^ 3)
    hm hi hbound hlim
  simp only [integral_zero] at hconv
  have hp := hconv.rpow_const (p := (3 : ℝ)⁻¹) (Or.inr (by positivity))
  have hp' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp
  convert hp' using 1
  · funext n
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((cutoff_memLp hf n).sub hf)]
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_natCast]
    simp only [Function.comp_apply, Pi.sub_apply, Real.rpow_ofNat]
  · norm_num

/-- A pointwise localization principle: the omitted tails tend to zero and
are independent of the small singular cutoff. -/
theorem localization {f g : ℝ → ℝ} {fs gs tails : ℕ → ℝ → ℝ}
    (hpv : ∀ n, IsHilbertPVAe (fs n) (gs n))
    (hgs : ∀ᵐ x ∂volume, Tendsto (fun n => gs n x) atTop (𝓝 (g x)))
    (htails : ∀ x, Tendsto (fun n => tails n x) atTop (𝓝 0))
    (hsplit : ∀ x, ∀ᶠ n in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      hilbertTrunc ε f x = hilbertTrunc ε (fs n) x + tails n x) :
    IsHilbertPVAe f g := by
  filter_upwards [ae_all_iff.mpr hpv, hgs] with x hpv hx
  obtain ⟨m, hm⟩ := (hsplit x).exists
  have hbase : Tendsto (fun ε => hilbertTrunc ε f x) (𝓝[>] 0)
      (𝓝 (gs m x + tails m x)) :=
    ((hpv m).add_const _).congr' (EventuallyEq.symm hm)
  have heq : ∀ᶠ n in atTop, gs n x + tails n x = gs m x + tails m x := by
    filter_upwards [hsplit x] with n hn
    exact tendsto_nhds_unique (((hpv n).add_const _).congr' (EventuallyEq.symm hn)) hbase
  have hlim := hx.add (htails x)
  simp only [add_zero] at hlim
  have hvalue := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (EventuallyEq.symm heq))
  rwa [← hvalue] at hbase

def awayKernel (x y : ℝ) : ℝ := if 1 < |x-y| then (x-y)⁻¹ else 0

theorem awayKernel_memLp (x : ℝ) : MemLp (awayKernel x) (3/2 : ℝ≥0∞) volume := by
  have hp : IntegrableOn (fun y : ℝ => ‖y⁻¹‖ ^ (3/2 : ℝ)) (Ioi 1) volume := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (- (3/2 : ℝ)) < -1)
      (by norm_num : (0 : ℝ) < 1)).congr_fun _ measurableSet_Ioi
    intro y hy
    dsimp only
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (lt_trans (by norm_num) hy),
      Real.rpow_neg_eq_inv_rpow]
  have hn : IntegrableOn (fun y : ℝ => ‖y⁻¹‖ ^ (3/2 : ℝ)) (Iio (-1)) volume := by
    have ht := ((volume.measurePreserving_neg).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hp
    simpa [Function.comp_def] using ht
  have hu : {y : ℝ | 1 < |y|} = Ioi 1 ∪ Iio (-1) := by
    ext y
    simp only [mem_ofPred_eq, mem_union, mem_Ioi, mem_Iio, lt_abs]
    constructor <;> rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hi : IntegrableOn (fun y : ℝ => ‖y⁻¹‖ ^ (3/2 : ℝ))
      {y : ℝ | 1 < |y|} volume := by
    rw [hu]
    exact integrableOn_union.mpr ⟨hp, hn⟩
  have hs : MeasurableSet {y : ℝ | 1 < |y|} :=
    isOpen_lt continuous_const continuous_abs |>.measurableSet
  have hb : MemLp ({y : ℝ | 1 < |y|}.indicator (fun y => y⁻¹))
      (3/2 : ℝ≥0∞) volume := by
    apply (integrable_norm_rpow_iff (f := {y : ℝ | 1 < |y|}.indicator (fun y => y⁻¹))
      ((measurable_id.inv).indicator hs).aestronglyMeasurable
      (by norm_num) (by finiteness)).mp
    have he : (fun y : ℝ => ‖({y : ℝ | 1 < |y|}.indicator (fun y => y⁻¹)) y‖ ^
        (3/2 : ℝ≥0∞).toReal) =
        {y : ℝ | 1 < |y|}.indicator (fun y => ‖y⁻¹‖ ^ (3/2 : ℝ)) := by
      funext y
      by_cases hy : 1 < |y| <;> simp [hy]
    change Integrable (fun y : ℝ => ‖({y : ℝ | 1 < |y|}.indicator (fun y => y⁻¹)) y‖ ^
      (3/2 : ℝ≥0∞).toReal) volume
    rw [he]
    exact hi.integrable_indicator hs
  have hc := hb.comp_measurePreserving (volume.measurePreserving_sub_left x)
  convert hc using 1
  funext y
  simp only [Function.comp_apply, awayKernel, indicator_apply, mem_ofPred_eq]

theorem awayKernel_mul_integrable {f : ℝ → ℝ} (hf : MemLp f 3 volume) (x : ℝ) :
    Integrable (fun y => awayKernel x y * f y) volume := by
  let : ENNReal.HolderTriple (3/2) 3 1 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by simp)).mp
    norm_num [ENNReal.toReal_add]⟩
  exact (awayKernel_memLp x).integrable_mul hf

def tailIntegrand (n : ℕ) (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (Icc (-(n : ℝ)) n)ᶜ.indicator (fun y => awayKernel x y * f y) y

def tail (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ y, tailIntegrand n f x y

theorem tailIntegrand_integrable {f : ℝ → ℝ} (hf : MemLp f 3 volume) (x : ℝ) (n : ℕ) :
    Integrable (tailIntegrand n f x) volume :=
  (awayKernel_mul_integrable hf x).indicator measurableSet_Icc.compl

theorem tail_tendsto {f : ℝ → ℝ} (hf : MemLp f 3 volume) (x : ℝ) :
    Tendsto (fun n => tail n f x) atTop (𝓝 0) := by
  have hi := awayKernel_mul_integrable hf x
  have hm (n : ℕ) := (tailIntegrand_integrable hf x n).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ y ∂volume, ‖tailIntegrand n f x y‖ ≤ ‖awayKernel x y * f y‖ :=
    Eventually.of_forall fun y => norm_indicator_le_norm_self _ _
  have hl : ∀ᵐ y ∂volume, Tendsto (fun n => tailIntegrand n f x y) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro y
    obtain ⟨N, hN⟩ := exists_nat_gt |y|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hy : y ∈ Icc (-(n : ℝ)) n :=
      abs_le.mp (le_trans hN.le (by exact_mod_cast hn))
    simp [tailIntegrand, hy]
  have ht := tendsto_integral_of_dominated_convergence (fun y => ‖awayKernel x y * f y‖)
    hm hi.norm hb hl
  simpa only [integral_zero, mul_zero, tail] using ht.const_mul Real.pi⁻¹

theorem one_lt_abs_sub_of_outside {n : ℕ} {x y : ℝ}
    (hn : |x| + 1 < (n : ℝ)) (hy : y ∉ Icc (-(n : ℝ)) n) : 1 < |x-y| := by
  have hy' : (n : ℝ) < |y| := lt_of_not_ge (fun h => hy (abs_le.mp h))
  have htriangle : |y| ≤ |x| + |x-y| := by
    have h := abs_sub_le y x 0
    simpa only [sub_zero, abs_sub_comm y x, add_comm] using h
  linarith

theorem hilbertTrunc_cutoff_split {f : ℝ → ℝ} (hf : MemLp f 3 volume)
    (n : ℕ) (x : ℝ) (hn : |x| + 1 < (n : ℝ)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    hilbertTrunc ε f x = hilbertTrunc ε (cutoff n f) x + tail n f x := by
  have hci : Integrable (cutoff n f) volume := by
    apply memLp_one_iff_integrable.mp
    exact (cutoff_memLp_two hf n).mono_exponent_of_measure_support_ne_top
      (s := Icc (-(n : ℝ)) n) (fun y hy => indicator_of_notMem hy f)
      measure_Icc_lt_top.ne (by norm_num)
  have hc := hilbertTrunc_integrable hci hε x
  simp only [smul_eq_mul] at hc
  have ht := tailIntegrand_integrable hf x n
  have he : (fun y => (x-y)⁻¹ * f y) =
      fun y => (x-y)⁻¹ * cutoff n f y + tailIntegrand n f x y := by
    funext y
    by_cases hy : y ∈ Icc (-(n : ℝ)) n
    · simp [cutoff, tailIntegrand, hy]
    · have hy' := one_lt_abs_sub_of_outside hn hy
      simp [cutoff, tailIntegrand, awayKernel, hy, hy']
  have htail : (∫ y in {y : ℝ | ε < |x-y|}, tailIntegrand n f x y) =
      ∫ y, tailIntegrand n f x y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_cases hy' : y ∈ Icc (-(n : ℝ)) n
    · simp [tailIntegrand, hy']
    · exact (hy (lt_trans hε1 (one_lt_abs_sub_of_outside hn hy'))).elim
  simp only [hilbertTrunc, smul_eq_mul, tail]
  rw [he, integral_add hc ht.integrableOn, htail]
  ring

/-- Every bounded L³ realization agreeing on L² ∩ L³ with an actual
principal-value L² operator is itself a principal-value realization.
No norm bound, Fourier identity, or external Hilbert-transform assertion is
assumed beyond the two explicitly displayed realization/compatibility hypotheses. -/
theorem isHilbertPVAe_of_L2_agreement
    (U : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 volume)
    (R : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 volume)
    (hU : ∀ (f : ℝ → ℝ) (hf : MemLp f 2 volume),
      IsHilbertPVAe f (U (hf.toLp f)))
    (hAgree : ∀ (f : ℝ → ℝ) (hf2 : MemLp f 2 volume) (hf3 : MemLp f 3 volume),
      (U (hf2.toLp f) : ℝ → ℝ) =ᵐ[volume] (R (hf3.toLp f) : ℝ → ℝ))
    (f : ℝ → ℝ) (hf : MemLp f 3 volume) :
    IsHilbertPVAe f (R (hf.toLp f)) := by
  have hconv := (R.continuous.tendsto (hf.toLp f)).comp (cutoff_tendsto_three hf)
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  apply localization
    (fs := fun n => cutoff (ns n) f)
    (gs := fun n => (R ((cutoff_memLp hf (ns n)).toLp (cutoff (ns n) f)) : ℝ → ℝ))
    (tails := fun n => tail (ns n) f)
  · intro n
    filter_upwards [hU (cutoff (ns n) f) (cutoff_memLp_two hf (ns n)),
      hAgree (cutoff (ns n) f) (cutoff_memLp_two hf (ns n)) (cutoff_memLp hf (ns n))]
      with x hx he
    rwa [he] at hx
  · exact hpoint
  · intro x
    exact (tail_tendsto hf x).comp hns.tendsto_atTop
  · intro x
    have hn := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hns.tendsto_atTop).eventually
      (eventually_gt_atTop (|x| + 1))
    filter_upwards [hn] with n hn
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
    exact hilbertTrunc_cutoff_split hf (ns n) x hn hε.1 hε.2

end HilbertUMD.HilbertThreePV
