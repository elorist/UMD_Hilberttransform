import HilbertUMD.Interfaces.HilbertPV
import HilbertUMD.Hilbert.HilbertTwoKernel
import HilbertUMD.Hilbert.HilbertThreePV
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Function.Holder

/-! Recover the scalar L2 principal value from a lower-exponent realization.
Smooth multiplication gives compatibility on compactly supported L2 inputs;
localization then removes the compact-support restriction. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace HilbertUMD.HilbertTwoFromThreeHalves

local instance : Fact ((1 : ℝ≥0∞) ≤ 3 / 2) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
local instance : ENNReal.HolderTriple (6 : ℝ≥0∞) 2 (3 / 2) := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]⟩
local instance : ENNReal.HolderConjugate (3 / 2 : ℝ≥0∞) 3 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]⟩

variable (R : Lp ℝ (3 / 2) (volume : Measure ℝ) →L[ℝ] Lp ℝ (3 / 2) volume)
  (hR : ∀ (f : ℝ → ℝ) (hf : MemLp f (3 / 2) volume),
    IsHilbertPVAe f (R (hf.toLp f)))

include hR

theorem agrees_test (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    R ((hilbertTest_memLp hf hc (3 / 2)).toLp f) =ᵐ[volume]
      realHilbertL2 ((hilbertTest_memLp hf hc 2).toLp f) := by
  obtain ⟨g, hg, hpv, heq⟩ := Interfaces.real_scalar_pv_fourier f hf hc
  have he := hg.coeFn_toLp.symm
  rw [heq] at he
  exact ((hR f _).unique hpv.ae).trans he

/-- Multiplication by a fixed smooth compact cutoff permits density in L2
while also controlling the lower exponent. -/
theorem agrees_mul_test (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hcψ : HasCompactSupport ψ) (f : RealL2) :
    R (((Lp.memLp f).mul' (hilbertTest_memLp hψ hcψ 6)).toLp (fun x => ψ x * f x))
      =ᵐ[volume]
    realHilbertL2 (((Lp.memLp f).mul' (hilbertTest_memLp hψ hcψ ⊤)).toLp
      (fun x => ψ x * f x)) := by
  let Mq : RealL2 →L[ℝ] Lp ℝ (3 / 2) volume :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL volume 6 2 (3 / 2)
      ((hilbertTest_memLp hψ hcψ 6).toLp ψ)
  let M2 : RealL2 →L[ℝ] RealL2 :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL volume ⊤ 2 2
      ((hilbertTest_memLp hψ hcψ ⊤).toLp ψ)
  have hMq (u : RealL2) : Mq u =ᵐ[volume] fun x => ψ x * u x := by
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 3 / 2)
      ((hilbertTest_memLp hψ hcψ 6).toLp ψ) u,
      (hilbertTest_memLp hψ hcψ 6).coeFn_toLp] with x hx hψx
    simpa [Mq, hψx] using hx
  have hM2 (u : RealL2) : M2 u =ᵐ[volume] fun x => ψ x * u x := by
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
      ((hilbertTest_memLp hψ hcψ ⊤).toLp ψ) u,
      (hilbertTest_memLp hψ hcψ ⊤).coeFn_toLp] with x hx hψx
    simpa [M2, hψx] using hx
  have heMq : Mq f = ((Lp.memLp f).mul' (hilbertTest_memLp hψ hcψ 6)).toLp
      (fun x => ψ x * f x) := Lp.ext ((hMq f).trans (MemLp.coeFn_toLp _).symm)
  have heM2 : M2 f = ((Lp.memLp f).mul' (hilbertTest_memLp hψ hcψ ⊤)).toLp
      (fun x => ψ x * f x) := Lp.ext ((hM2 f).trans (MemLp.coeFn_toLp _).symm)
  rw [← heMq, ← heM2]
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (Fact.out : (1 : ℝ≥0∞) ≤ 3 / 2))
    ((Lp.memLp _).locallyIntegrable (by norm_num))
  intro φ hφ hcφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  let Bq := (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume : Measure ℝ) (3 / 2) 3
  let B2 := (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume : Measure ℝ) 2 2
  let φq := (hilbertTest_memLp hφ1 hcφ 3).toLp φ
  let φ2 := (hilbertTest_memLp hφ1 hcφ 2).toLp φ
  have he : Bq (R (Mq f)) φq = B2 (realHilbertL2 (M2 f)) φ2 := by
    apply congrFun (Continuous.ext_on
      (Lp.dense_hasCompactSupport_contDiff (E := ℝ) (F := ℝ) (μ := volume)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      (((Bq.flip φq).continuous.comp R.continuous).comp Mq.continuous)
      (((B2.flip φ2).continuous.comp realHilbertL2.continuous).comp M2.continuous) ?_) f
    rintro u ⟨v, huv, hcv, hv⟩
    have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
    have hp := hψ.mul hv1
    have hc : HasCompactSupport (fun x => ψ x * v x) := hcψ.mul_right
    have heq : Mq u = (hilbertTest_memLp hp hc (3 / 2)).toLp (fun x => ψ x * v x) := by
      apply Lp.ext
      filter_upwards [hMq u, huv, (hilbertTest_memLp hp hc (3 / 2)).coeFn_toLp]
        with x hx hu hvx
      simp only [hx, hu, hvx]
    have he2 : M2 u = (hilbertTest_memLp hp hc 2).toLp (fun x => ψ x * v x) := by
      apply Lp.ext
      filter_upwards [hM2 u, huv, (hilbertTest_memLp hp hc 2).coeFn_toLp]
        with x hx hu hvx
      simp only [hx, hu, hvx]
    change Bq (R (Mq u)) φq = B2 (realHilbertL2 (M2 u)) φ2
    rw [heq, he2, ContinuousLinearMap.lpPairing_eq_integral,
      ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [agrees_test R hR _ hp hc,
      (hilbertTest_memLp hφ1 hcφ 3).coeFn_toLp,
      (hilbertTest_memLp hφ1 hcφ 2).coeFn_toLp] with x hx hq h2
    change R _ x * φq x = realHilbertL2 _ x * φ2 x
    simp [φq, φ2, hx, hq, h2]
  rw [ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.lpPairing_eq_integral] at he
  have hl : (∫ x, R (Mq f) x * φq x) = ∫ x, φ x • R (Mq f) x := by
    apply integral_congr_ae
    filter_upwards [(hilbertTest_memLp hφ1 hcφ 3).coeFn_toLp] with x hx
    simp [φq, hx, mul_comm]
  have hr : (∫ x, realHilbertL2 (M2 f) x * φ2 x) =
      ∫ x, φ x • realHilbertL2 (M2 f) x := by
    apply integral_congr_ae
    filter_upwards [(hilbertTest_memLp hφ1 hcφ 2).coeFn_toLp] with x hx
    simp [φ2, hx, mul_comm]
  exact hl.symm.trans (he.trans hr)

open HilbertThreePV

omit hR in
theorem cutoff_memLp_three_halves {f : ℝ → ℝ} (hf : MemLp f 2 volume) (n : ℕ) :
    MemLp (cutoff n f) (3 / 2) volume := by
  apply (cutoff_memLp hf n).mono_exponent_of_measure_support_ne_top
    (s := Icc (-(n : ℝ)) n) (fun t ht => indicator_of_notMem ht f)
    measure_Icc_lt_top.ne
  exact ENNReal.div_le_of_le_mul (by norm_num)

theorem cutoff_pv {f : ℝ → ℝ} (hf : MemLp f 2 volume) (n : ℕ) :
    IsHilbertPVAe (cutoff n f)
      (realHilbertL2 ((cutoff_memLp hf n).toLp (cutoff n f))) := by
  let ψ : ContDiffBump (0 : ℝ) := ⟨n + 1, n + 2, by positivity, by linarith⟩
  let u := (cutoff_memLp hf n).toLp (cutoff n f)
  have hmul : (fun x => ψ x * u x) =ᵐ[volume] cutoff n f := by
    filter_upwards [(cutoff_memLp hf n).coeFn_toLp] with x hx
    rw [show u x = cutoff n f x from hx]
    by_cases hxn : x ∈ Icc (-(n : ℝ)) n
    · have hψx : ψ x = 1 := ψ.one_of_mem_closedBall (by
        simpa [Metric.mem_closedBall, Real.dist_eq, ψ] using
          (show |x| ≤ (n : ℝ) + 1 by linarith [abs_le.mpr hxn]))
      rw [hψx, one_mul]
    · simp [cutoff, hxn]
  have hq : ((Lp.memLp u).mul' (hilbertTest_memLp ψ.contDiff ψ.hasCompactSupport 6)).toLp
      (fun x => ψ x * u x) = (cutoff_memLp_three_halves hf n).toLp (cutoff n f) :=
    Lp.ext ((MemLp.coeFn_toLp _).trans (hmul.trans (MemLp.coeFn_toLp _).symm))
  have h2 : ((Lp.memLp u).mul' (hilbertTest_memLp ψ.contDiff ψ.hasCompactSupport ⊤)).toLp
      (fun x => ψ x * u x) = u :=
    Lp.ext ((MemLp.coeFn_toLp _).trans (hmul.trans (MemLp.coeFn_toLp _).symm))
  have ha := agrees_mul_test R hR ψ ψ.contDiff ψ.hasCompactSupport u
  rw [hq, h2] at ha
  exact (hR _ (cutoff_memLp_three_halves hf n)).congr_output ha

omit hR in
theorem cutoff_tendsto_two {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun n => (cutoff_memLp hf n).toLp (cutoff n f)) atTop
      (𝓝 (hf.toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  have hi := hf.integrable_norm_pow (by decide : 2 ≠ 0)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun t => ‖cutoff n f t - f t‖ ^ 2) volume :=
    ((cutoff_memLp hf n).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2
  have hbound (n : ℕ) : ∀ᵐ t ∂volume, ‖‖cutoff n f t - f t‖ ^ 2‖ ≤ ‖f t‖ ^ 2 := by
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ Icc (-(n : ℝ)) n <;> simp [cutoff, ht, sq_nonneg]
  have hlim : ∀ᵐ t ∂volume, Tendsto (fun n => ‖cutoff n f t - f t‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro t
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_cutoff_eq f t] with n hn
    simp [hn]
  have hconv := tendsto_integral_of_dominated_convergence (fun t => ‖f t‖ ^ 2)
    hm hi hbound hlim
  simp only [integral_zero] at hconv
  have hp := hconv.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by positivity))
  have hp' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp
  convert hp' using 1
  · funext n
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((cutoff_memLp hf n).sub hf)]
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_natCast]
    simp only [Function.comp_apply, Pi.sub_apply, Real.rpow_ofNat]
  · norm_num

omit hR

theorem awayKernel_memLp_two (x : ℝ) : MemLp (awayKernel x) 2 volume := by
  have hs : MeasurableSet {y : ℝ | 1 < |x-y|} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hm : MemLp ({y : ℝ | 1 < |x-y|}.indicator (fun y => (x-y)⁻¹)) 2 volume :=
    (memLp_indicator_iff_restrict hs).mpr
    (hilbertKernel_memLp_two (by norm_num : (0 : ℝ) < 1) x)
  apply hm.ae_eq
  exact Eventually.of_forall fun y => by simp [awayKernel, indicator_apply]

theorem awayKernel_mul_integrable_two {f : ℝ → ℝ} (hf : MemLp f 2 volume) (x : ℝ) :
    Integrable (fun y => awayKernel x y * f y) volume :=
  (awayKernel_memLp_two x).integrable_mul hf

theorem tailIntegrand_integrable_two {f : ℝ → ℝ} (hf : MemLp f 2 volume) (x : ℝ) (n : ℕ) :
    Integrable (tailIntegrand n f x) volume :=
  (awayKernel_mul_integrable_two hf x).indicator measurableSet_Icc.compl

theorem tail_tendsto_two {f : ℝ → ℝ} (hf : MemLp f 2 volume) (x : ℝ) :
    Tendsto (fun n => tail n f x) atTop (𝓝 0) := by
  have hi := awayKernel_mul_integrable_two hf x
  have hm (n : ℕ) := (tailIntegrand_integrable_two hf x n).aestronglyMeasurable
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

theorem hilbertTrunc_cutoff_split_two {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (n : ℕ) (x : ℝ) (hn : |x| + 1 < (n : ℝ)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    hilbertTrunc ε f x = hilbertTrunc ε (cutoff n f) x + tail n f x := by
  have hci : Integrable (cutoff n f) volume := by
    apply memLp_one_iff_integrable.mp
    exact (cutoff_memLp hf n).mono_exponent_of_measure_support_ne_top
      (s := Icc (-(n : ℝ)) n) (fun y hy => indicator_of_notMem hy f)
      measure_Icc_lt_top.ne (by norm_num)
  have hc := hilbertTrunc_integrable hci hε x
  simp only [smul_eq_mul] at hc
  have ht := tailIntegrand_integrable_two hf x n
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

include hR in
theorem pv_all (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    IsHilbertPVAe f (realHilbertL2 (hf.toLp f)) := by
  have hconv := (realHilbertL2.continuous.tendsto (hf.toLp f)).comp (cutoff_tendsto_two hf)
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  apply localization
    (fs := fun n => cutoff (ns n) f)
    (gs := fun n => (realHilbertL2
      ((cutoff_memLp hf (ns n)).toLp (cutoff (ns n) f)) : ℝ → ℝ))
    (tails := fun n => tail (ns n) f)
  · intro n
    exact cutoff_pv R hR hf (ns n)
  · exact hpoint
  · intro x
    exact (tail_tendsto_two hf x).comp hns.tendsto_atTop
  · intro x
    have hn := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hns.tendsto_atTop).eventually
      (eventually_gt_atTop (|x| + 1))
    filter_upwards [hn] with n hn
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
    exact hilbertTrunc_cutoff_split_two hf (ns n) x hn hε.1 hε.2

end HilbertUMD.HilbertTwoFromThreeHalves
