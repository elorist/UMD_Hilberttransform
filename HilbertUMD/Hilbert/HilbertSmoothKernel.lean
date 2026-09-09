import HilbertUMD.Hilbert.HilbertPVFourier
import HilbertUMD.Analysis.LebesgueDecayApproximation
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! Smooth, even test kernels and their classical Hilbert transforms. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace HilbertUMD.HilbertSmoothKernel

def pv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ y, hilbertDifference f x y

theorem isHilbertPV_pv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hi : Integrable f) :
    IsHilbertPV f (pv f) := isHilbertPV_difference hf hi

theorem difference_le {f : ℝ → ℝ} {L : ℝ≥0} (hl : LipschitzWith L f) (x y : ℝ) :
    ‖hilbertDifference f x y‖ ≤ 2 * L := by
  rw [hilbertDifference, norm_smul, Real.norm_eq_abs, abs_inv]
  have hh := hl.norm_sub_le (x - y) (x + y)
  have he : ‖(x - y) - (x + y)‖ = 2 * |y| := by
    rw [show (x - y) - (x + y) = -2 * y by ring, norm_mul]
    norm_num [Real.norm_eq_abs]
  rw [he] at hh
  by_cases hy : y = 0
  · simp [hy]
  calc
    _ ≤ |y|⁻¹ * (L * (2 * |y|)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by field_simp

theorem norm_pv_le {f : ℝ → ℝ} {L : ℝ≥0} (hi : Integrable f)
    (hl : LipschitzWith L f) (x : ℝ) :
    ‖pv f x‖ ≤ (2 * Real.pi)⁻¹ * (4 * L + 2 * ∫ y, ‖f y‖) := by
  let b : ℝ → ℝ := (closedBall 0 1).indicator (fun _ : ℝ => 2 * (L : ℝ))
  have hb : Integrable b := by
    apply (integrable_indicator_iff measurableSet_closedBall).mpr
    exact integrableOn_const (measure_closedBall_lt_top.ne)
  have hbint : (∫ y, b y) = 4 * L := by
    dsimp [b]
    rw [integral_indicator measurableSet_closedBall, integral_const, measureReal_def,
      Measure.restrict_apply_univ, Real.volume_closedBall]
    norm_num [smul_eq_mul]
    ring
  have hbnd (y : ℝ) : ‖hilbertDifference f x y‖ ≤ b y + (‖f (x - y)‖ + ‖f (x + y)‖) := by
    by_cases hy : y ∈ closedBall (0 : ℝ) 1
    · dsimp [b]
      rw [indicator_of_mem hy]
      exact (difference_le hl x y).trans (le_add_of_nonneg_right (by positivity))
    · have hya : 1 ≤ |y| := by
        simp only [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hy
        exact hy.le
      have hyi : |y|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hya
      dsimp [b]
      rw [indicator_of_notMem hy, zero_add]
      change ‖hilbertDifference f x y‖ ≤ _
      rw [hilbertDifference, norm_smul, Real.norm_eq_abs, abs_inv]
      exact (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans
        (by simpa using mul_le_mul_of_nonneg_right hyi (show 0 ≤ ‖f (x - y)‖ + ‖f (x + y)‖ by positivity))
  have hbound : Integrable (fun y => b y + (‖f (x - y)‖ + ‖f (x + y)‖)) :=
    hb.add ((hi.comp_sub_left x).norm.add (hi.comp_add_left x).norm)
  calc
    ‖pv f x‖ = (2 * Real.pi)⁻¹ * ‖∫ y, hilbertDifference f x y‖ := by
      rw [pv, norm_mul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (2 * Real.pi)⁻¹ * ∫ y, ‖hilbertDifference f x y‖ := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ ≤ (2 * Real.pi)⁻¹ * ∫ y, b y + (‖f (x - y)‖ + ‖f (x + y)‖) := by
      exact mul_le_mul_of_nonneg_left
        (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hbound
          (Eventually.of_forall hbnd)) (by positivity)
    _ = _ := by
      rw [integral_add (f := b) (g := fun y => ‖f (x - y)‖ + ‖f (x + y)‖)
          hb ((hi.comp_sub_left x).norm.add (hi.comp_add_left x).norm),
        integral_add (hi.comp_sub_left x).norm (hi.comp_add_left x).norm,
        hbint, integral_sub_left_eq_self (fun y => ‖f y‖) volume x,
        integral_add_left_eq_self (fun y => ‖f y‖) x]
      ring

theorem pv_odd {f : ℝ → ℝ} (he : ∀ y, f (-y) = f y) (x : ℝ) :
    pv f (-x) = -pv f x := by
  have hd (y : ℝ) : hilbertDifference f (-x) y = -hilbertDifference f x y := by
    rw [hilbertDifference, hilbertDifference, show -x - y = -(x + y) by ring,
      show -x + y = -(x - y) by ring, he, he]
    simp only [smul_eq_mul]
    ring
  simp only [pv, hd, integral_neg, mul_neg]

def bump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def test : SchwartzMap ℝ ℝ :=
  (bump.hasCompactSupport_normed (μ := volume)).toSchwartzMap bump.contDiff_normed

theorem test_nonneg (y : ℝ) : 0 ≤ test y := bump.nonneg_normed y

theorem test_even (y : ℝ) : test (-y) = test y := bump.normed_neg y

theorem test_integral : (∫ y, test y) = 1 := bump.integral_normed

theorem test_support : Function.support (test : ℝ → ℝ) ⊆ closedBall 0 (1 / 2) := by
  change Function.support (bump.normed volume) ⊆ _
  rw [bump.support_normed_eq]
  exact ball_subset_closedBall

theorem test_lipschitz : ∃ L : ℝ≥0, LipschitzWith L test := by
  let d := SchwartzMap.derivCLM ℝ ℝ test
  refine ⟨⟨SchwartzMap.seminorm ℝ 0 0 d, apply_nonneg _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le ((test.smooth 1).differentiable (by norm_num))
  intro x
  have hd := SchwartzMap.norm_le_seminorm ℝ d x
  change ‖deriv test x‖ ≤ SchwartzMap.seminorm ℝ 0 0 d
  simpa only [d, SchwartzMap.derivCLM_apply] using hd

private theorem dist_from_support {x y : ℝ} (hy : |y| ≤ 1 / 2) :
    |x| - 1 / 2 ≤ |x - y| := by
  have h := abs_add_le (x - y) y
  rw [sub_add_cancel] at h
  linarith

theorem test_kernel_integrable {x : ℝ} (hx : 1 / 2 < |x|) :
    Integrable (fun y => (x - y)⁻¹ * test y) := by
  let ε := (|x| - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hs : MeasurableSet {y : ℝ | ε < |x - y|} := by measurability
  have hh := (integrable_indicator_iff hs).mpr (hilbertTrunc_integrable test.integrable hε x)
  apply hh.congr
  filter_upwards with y
  by_cases hy : test y = 0
  · simp [hy, indicator]
  · have hym := test_support (show y ∈ Function.support (test : ℝ → ℝ) from hy)
    have hya : |y| ≤ 1 / 2 := by simpa [Real.dist_eq] using hym
    have he : ε < |x - y| := by have := dist_from_support (x := x) hya; dsimp [ε]; linarith
    simp only [indicator, mem_ofPred_eq, he, ↓reduceIte, smul_eq_mul]

theorem pv_test_off_support {x : ℝ} (hx : 1 / 2 < |x|) :
    pv test x = Real.pi⁻¹ * ∫ y, (x - y)⁻¹ * test y := by
  apply tendsto_nhds_unique (isHilbertPV_pv (test.smooth 1) test.integrable x)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT (show 0 < |x| - 1 / 2 by linarith)] with ε hε
  rw [hilbertTrunc]
  simp only [smul_eq_mul]
  congr 1
  have hs : MeasurableSet {y : ℝ | ε < |x - y|} := by measurability
  rw [← integral_indicator hs]
  congr 1
  funext y
  by_cases hy : test y = 0
  · simp [hy, indicator]
  · have hym := test_support (show y ∈ Function.support (test : ℝ → ℝ) from hy)
    have hya : |y| ≤ 1 / 2 := by simpa [Real.dist_eq] using hym
    have he : ε < |x - y| := hε.2.trans_le (dist_from_support hya)
    simp only [indicator, mem_ofPred_eq, he, ↓reduceIte]

private theorem reciprocal_error_le {x y : ℝ} (hx : 1 ≤ |x|) (hy : |y| ≤ 1 / 2) :
    |(x - y)⁻¹ - x⁻¹| ≤ 1 / |x| ^ 2 := by
  have hxy : |x| / 2 ≤ |x - y| := by have := dist_from_support (x := x) hy; linarith
  have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx
  have hxy0 : x - y ≠ 0 := by intro h; simp [h] at hxy; linarith [abs_nonneg x]
  have he : (x - y)⁻¹ - x⁻¹ = y / ((x - y) * x) := by field_simp; ring
  rw [he, abs_div, abs_mul]
  calc
    |y| / (|x - y| * |x|) ≤ (1 / 2) / ((|x| / 2) * |x|) := by gcongr
    _ = 1 / |x| ^ 2 := by field_simp

theorem pv_test_tail {x : ℝ} (hx : 1 ≤ |x|) :
    ‖pv test x - Real.pi⁻¹ * x⁻¹‖ ≤ Real.pi⁻¹ / |x| ^ 2 := by
  have hx' : 1 / 2 < |x| := by linarith
  have he : pv test x - Real.pi⁻¹ * x⁻¹ =
      Real.pi⁻¹ * ∫ y, ((x - y)⁻¹ - x⁻¹) * test y := by
    rw [pv_test_off_support hx']
    simp_rw [sub_mul]
    rw [integral_sub (test_kernel_integrable hx') (test.integrable.const_mul _),
      integral_const_mul, test_integral]
    ring
  have hb (y : ℝ) : ‖((x - y)⁻¹ - x⁻¹) * test y‖ ≤ (1 / |x| ^ 2) * test y := by
    by_cases hy : test y = 0
    · simp [hy]
    · have hym := test_support (show y ∈ Function.support (test : ℝ → ℝ) from hy)
      rw [norm_mul, Real.norm_of_nonneg (test_nonneg y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (reciprocal_error_le hx (by simpa [Real.dist_eq] using hym))
        (test_nonneg y)
  rw [he, norm_mul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ Real.pi⁻¹ * ∫ y, ‖((x - y)⁻¹ - x⁻¹) * test y‖ := by
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ Real.pi⁻¹ * ∫ y, (1 / |x| ^ 2) * test y := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (test.integrable.const_mul _) (Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul, test_integral]; ring

theorem measurable_pv {f : ℝ → ℝ} (hf : Measurable f) : Measurable (pv f) := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => hilbertDifference f p.1 p.2) := by
    apply Measurable.stronglyMeasurable
    dsimp [hilbertDifference]
    fun_prop
  exact measurable_const.mul hm.integral_prod_right'.measurable

def scaled (ε x y : ℝ) : ℝ := ε⁻¹ * test ((x - y) / ε)

theorem scaled_contDiff (ε x : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scaled ε x) := by
  have ht := test.smooth ⊤
  unfold scaled
  fun_prop

theorem scaled_compact {ε : ℝ} (hε : 0 < ε) (x : ℝ) : HasCompactSupport (scaled ε x) := by
  let e : ℝ ≃ₜ ℝ := (Homeomorph.subLeft x).trans (Homeomorph.smulOfNeZero ε⁻¹ (by positivity))
  have hc : HasCompactSupport (test : ℝ → ℝ) := bump.hasCompactSupport_normed (μ := volume)
  have he : (test : ℝ → ℝ) ∘ e = fun y => test ((x - y) / ε) := by
    funext y
    simp [e, div_eq_mul_inv, mul_comm]
  have hh := hc.comp_homeomorph e
  rw [he] at hh
  exact hh.smul_left (f := fun _ => ε⁻¹)

def scaledTest {ε : ℝ} (hε : 0 < ε) (x : ℝ) : SchwartzMap ℝ ℝ :=
  (scaled_compact hε x).toSchwartzMap (scaled_contDiff ε x)

theorem integral_scaled {ε : ℝ} (hε : 0 < ε) (x : ℝ) : (∫ y, scaled ε x y) = 1 := by
  simp only [scaled]
  rw [integral_const_mul,
    integral_sub_left_eq_self (fun t => test (t / ε)) volume x,
    Measure.integral_comp_div, test_integral]
  simp [abs_of_pos hε, hε.ne']

theorem scaled_support {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Function.support (scaled ε x) ⊆ closedBall x ε := by
  intro y hy
  have ht : test ((x - y) / ε) ≠ 0 := by
    intro ht
    apply hy
    simp [scaled, ht]
  have hs := test_support ht
  have ha : |x - y| / ε ≤ 1 / 2 := by
    simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hε] using hs
  rw [mem_closedBall, Real.dist_eq, abs_sub_comm]
  have := (div_le_iff₀ hε).mp ha
  linarith

theorem scaled_bound {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    |scaled ε x y| ≤ (2 * SchwartzMap.seminorm ℝ 0 0 test) /
      volume.real (closedBall x ε) := by
  rw [scaled, abs_mul, abs_inv, abs_of_pos hε, measureReal_def, Real.volume_closedBall,
    ENNReal.toReal_ofReal (by positivity)]
  calc
    ε⁻¹ * |test ((x - y) / ε)| ≤ ε⁻¹ * SchwartzMap.seminorm ℝ 0 0 test :=
      mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ test _) (by positivity)
    _ = _ := by field_simp

theorem pv_scaled {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    pv (scaled ε x) y = -ε⁻¹ * pv test ((x - y) / ε) := by
  have hd (t : ℝ) : hilbertDifference (scaled ε x) y t =
      -(ε⁻¹ * ε⁻¹) * hilbertDifference test ((x - y) / ε) (t / ε) := by
    have hm : (x - (y - t)) / ε = (x - y) / ε + t / ε := by ring
    have hp : (x - (y + t)) / ε = (x - y) / ε - t / ε := by ring
    simp only [hilbertDifference, scaled, smul_eq_mul, hm, hp, inv_div]
    field_simp
    ring
  simp only [pv, hd]
  rw [integral_const_mul, Measure.integral_comp_div]
  simp only [abs_of_pos hε, smul_eq_mul]
  field_simp

def error (y : ℝ) : ℝ :=
  (if 1 < |y| then Real.pi⁻¹ * y⁻¹ else 0) - pv test y

theorem measurable_error : Measurable error := by
  apply Measurable.sub
  · exact Measurable.ite (by measurability) (by fun_prop) measurable_const
  · exact measurable_pv test.continuous.measurable

theorem error_odd (y : ℝ) : error (-y) = -error y := by
  rw [error, error, pv_odd test_even]
  by_cases hy : 1 < |y|
  · simp [hy]
    ring
  · simp [hy]

theorem exists_error_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y,
    ‖error y‖ ≤ if |y| ≤ 1 then C else C / |y| ^ 2 := by
  obtain ⟨L, hL⟩ := test_lipschitz
  let B : ℝ := (2 * Real.pi)⁻¹ * (4 * L + 2 * ∫ y, ‖test y‖)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B + Real.pi⁻¹, by positivity, ?_⟩
  intro y
  by_cases hy : |y| ≤ 1
  · rw [if_pos hy, error, if_neg (not_lt.mpr hy), zero_sub, norm_neg]
    exact (norm_pv_le test.integrable hL y).trans (le_add_of_nonneg_right (by positivity))
  · rw [if_neg hy, error, if_pos (lt_of_not_ge hy), norm_sub_rev]
    exact (pv_test_tail (le_of_lt (lt_of_not_ge hy))).trans (by gcongr; exact le_add_of_nonneg_left hB)

theorem error_integrable : Integrable error := by
  obtain ⟨C, hC, hb⟩ := exists_error_bound
  refine ⟨measurable_error.aestronglyMeasurable, ?_⟩
  have hm (r : ℝ) (hr : 0 < r) : LebesgueDecayApproximation.mean (fun _ => 1) 0 r ≤ 1 := by
    unfold LebesgueDecayApproximation.mean
    rw [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_closedBall,
      ENNReal.toReal_ofReal (by positivity)]
    simp only [smul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ (by positivity : 2 * r ≠ 0)]
  have hh := LebesgueDecayApproximation.lintegral_decay_bound
    (fun _ => (zero_le_one : (0 : ℝ) ≤ 1)) (locallyIntegrable_const 1) hC
    (show (0 : ℝ) < 1 by norm_num) hm (v := error) (fun y => by simpa using hb y)
  exact hh.trans_lt ENNReal.ofReal_lt_top

theorem integral_error : (∫ y, error y) = 0 := by
  have h : (∫ y, error y) = -(∫ y, error y) := by
    calc
      _ = ∫ y, error (-y) := (integral_neg_eq_self error volume).symm
      _ = _ := by simp only [error_odd, integral_neg]
  linarith

theorem ae_scaled_tendsto {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    ∀ᵐ x ∂volume, Tendsto (fun ε => ∫ y, scaled ε x y * g y) (𝓝[>] 0) (𝓝 (g x)) := by
  filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average_norm_sub hg] with x hx
  have hlim := hx.comp (Besicovitch.tendsto_filterAt volume x)
  apply tendsto_integral_smul_of_tendsto_average_norm_sub
    (2 * SchwartzMap.seminorm ℝ 0 0 test) hlim
  · filter_upwards with ε
    exact hg.integrableOn_isCompact (isCompact_closedBall _ _)
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_scaled hε x).symm
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact scaled_support hε x
  · filter_upwards [self_mem_nhdsWithin] with ε hε y
    exact scaled_bound hε x y

def scaledError (ε x y : ℝ) : ℝ := ε⁻¹ * error ((x - y) / ε)

theorem scaledError_integrable {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Integrable (scaledError ε x) :=
  ((error_integrable.comp_div hε.ne').comp_sub_left x).const_mul _

theorem integral_scaledError {ε : ℝ} (_hε : 0 < ε) (x : ℝ) :
    (∫ y, scaledError ε x y) = 0 := by
  simp only [scaledError]
  rw [integral_const_mul, integral_sub_left_eq_self (fun t => error (t / ε)) volume x,
    Measure.integral_comp_div, integral_error]
  simp

theorem scaledError_eq {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    scaledError ε x y =
      (if ε < |x - y| then Real.pi⁻¹ * (x - y)⁻¹ else 0) -
        ε⁻¹ * pv test ((x - y) / ε) := by
  simp only [scaledError, error, abs_div, abs_of_pos hε]
  have he : (1 : ℝ) < |x - y| / ε ↔ ε < |x - y| := by
    rw [lt_div_iff₀ hε, one_mul]
  simp only [he]
  by_cases hy : ε < |x - y|
  · rw [if_pos hy, if_pos hy, inv_div]
    field_simp
  · simp [hy]

theorem scaledError_bound {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ y, ‖error y‖ ≤ if |y| ≤ 1 then C else C / |y| ^ 2)
    {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    ‖scaledError ε x y‖ ≤
      if |x - y| ≤ ε then C / ε else C * ε / |x - y| ^ 2 := by
  rw [scaledError, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
  have he : |(x - y) / ε| ≤ 1 ↔ |x - y| ≤ ε := by
    rw [abs_div, abs_of_pos hε, div_le_iff₀ hε, one_mul]
  have hh := mul_le_mul_of_nonneg_left (hb ((x - y) / ε)) (inv_nonneg.mpr hε.le)
  simp only [he] at hh
  by_cases hy : |x - y| ≤ ε
  · simpa only [hy, ↓reduceIte, div_eq_inv_mul] using hh
  · rw [if_neg hy] at hh ⊢
    have hid : ε⁻¹ * (C / |(x - y) / ε| ^ 2) = C * ε / |x - y| ^ 2 := by
      rw [abs_div, abs_of_pos hε]
      field_simp
    exact hh.trans_eq hid

end HilbertUMD.HilbertSmoothKernel
