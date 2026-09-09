import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic

/-!
# Elementary interpolation between L2 and L4

Clipping, rather than a disjoint amplitude split, keeps the interpolation
constant below six when the endpoint bounds are one and five halves.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace HilbertUMD.TwoFourInterpolation

/-- Clip a real scalar at height `a`. -/
def clip (a x : ℝ) : ℝ := max (-a) (min a x)

theorem abs_clip {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : |clip a x| = min a |x| := by
  rcases le_total 0 x with hx | hx
  · rw [clip, max_eq_right (le_min (by linarith) (by linarith)),
      abs_of_nonneg (le_min ha hx), abs_of_nonneg hx]
  · rw [clip, min_eq_right (hx.trans ha), abs_of_nonpos (max_le (by linarith) hx),
      abs_of_nonpos hx, ← min_neg_neg, neg_neg]

theorem abs_sub_clip {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    |x - clip a x| = max (|x| - a) 0 := by
  rcases le_total 0 x with hx | hx
  · rw [clip, max_eq_right (le_min (by linarith) (by linarith)),
      abs_of_nonneg (sub_nonneg.mpr (min_le_right _ _)), abs_of_nonneg hx,
      ← max_sub_sub_left, sub_self]
  · rw [clip, min_eq_right (hx.trans ha),
      abs_of_nonpos (sub_nonpos.mpr (le_max_right _ _)), abs_of_nonpos hx]
    rw [neg_sub, ← max_sub_sub_right, sub_self]
    congr 1
    ring

theorem clip_mem_two {f : ℝ → ℝ} (hf : MemLp f 2 volume) {a : ℝ} (ha : 0 ≤ a) :
    MemLp (fun x => clip a (f x)) 2 volume := by
  apply hf.of_le ((continuous_const.max (continuous_const.min continuous_id)).comp_aestronglyMeasurable hf.1)
  filter_upwards with x
  exact (abs_clip ha (f x)).le.trans (min_le_right _ _)

theorem clip_mem_four {f : ℝ → ℝ} (hf : MemLp f 2 volume) {a : ℝ} (ha : 0 ≤ a) :
    MemLp (fun x => clip a (f x)) 4 volume := by
  have hm := (clip_mem_two hf ha).1
  apply (integrable_norm_rpow_iff hm (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  apply ((hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul (a ^ 2)).mono'
    (hm.norm.pow 4)
  filter_upwards with x
  change ‖‖clip a (f x)‖ ^ 4‖ ≤ a ^ 2 * ‖f x‖ ^ 2
  rw [Real.norm_of_nonneg (by positivity)]
  have hab : ‖clip a (f x)‖ ≤ a := (abs_clip ha _).le.trans (min_le_left _ _)
  have hfb : ‖clip a (f x)‖ ≤ ‖f x‖ := (abs_clip ha _).le.trans (min_le_right _ _)
  calc
    ‖clip a (f x)‖ ^ 4 = ‖clip a (f x)‖ ^ 2 * ‖clip a (f x)‖ ^ 2 := by ring
    _ ≤ a ^ 2 * ‖f x‖ ^ 2 := by gcongr

/-- The integral of the squared unclipped remainder. -/
theorem lintegral_remainder (r : ℝ) (hr : 0 ≤ r) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((max (r - t / 20) 0) ^ 2) =
      ENNReal.ofReal ((20 / 3 : ℝ) * r ^ 3) := by
  have h20 : 0 ≤ 20 * r := by positivity
  rw [← Ioc_union_Ioi_eq_Ioi h20, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have htail : (∫⁻ t in Ioi (20 * r), ENNReal.ofReal ((max (r - t / 20) 0) ^ 2)) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [max_eq_right (by linarith [show 20 * r < t from ht])]
    simp
  rw [htail, add_zero]
  have he : (fun t => ENNReal.ofReal ((max (r - t / 20) 0) ^ 2))
      =ᵐ[volume.restrict (Ioc 0 (20 * r))] fun t => ENNReal.ofReal ((r - t / 20) ^ 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    rw [max_eq_left (by linarith [ht.2])]
  rw [lintegral_congr_ae he, ← ofReal_integral_eq_lintegral_ofReal
    ((by fun_prop : Continuous (fun t : ℝ => (r - t / 20) ^ 2)).intervalIntegrable _ _).1
    (Eventually.of_forall fun t => sq_nonneg _), ← intervalIntegral.integral_of_le h20]
  congr 1
  calc
    (∫ t in 0..20 * r, (r - t / 20) ^ 2) =
        ∫ t in 0..20 * r, r ^ 2 - (r / 10) * t + (1 / 400 : ℝ) * t ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, integral_id, integral_pow]
      simp only [smul_eq_mul]
      ring

/-- The weighted fourth moment of the clipped part. -/
theorem lintegral_clipped (r : ℝ) (hr : 0 ≤ r) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((min (t / 20) r) ^ 4 / t ^ 2) =
      ENNReal.ofReal (r ^ 3 / 15) := by
  rcases hr.eq_or_lt with rfl | hr
  · apply (lintegral_eq_zero_of_ae_eq_zero ?_).trans (by simp)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [min_eq_right (by linarith [show 0 < t from ht])]
    simp
  have h20 : 0 < 20 * r := by positivity
  rw [← Ioc_union_Ioi_eq_Ioi h20.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have hhead : (∫⁻ t in Ioc 0 (20 * r), ENNReal.ofReal ((min (t / 20) r) ^ 4 / t ^ 2)) =
      ENNReal.ofReal (r ^ 3 / 60) := by
    have he : (fun t => ENNReal.ofReal ((min (t / 20) r) ^ 4 / t ^ 2))
        =ᵐ[volume.restrict (Ioc 0 (20 * r))] fun t => ENNReal.ofReal (t ^ 2 / 160000) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      rw [min_eq_left (by linarith [ht.2])]
      congr 1
      field_simp
      nlinarith [ht.1]
    rw [lintegral_congr_ae he, ← ofReal_integral_eq_lintegral_ofReal
      ((by fun_prop : Continuous (fun t : ℝ => t ^ 2 / 160000)).intervalIntegrable _ _).1
      (Eventually.of_forall fun t => by positivity), ← intervalIntegral.integral_of_le h20.le,
      intervalIntegral.integral_div, integral_pow]
    congr 1
    ring
  have htail : (∫⁻ t in Ioi (20 * r), ENNReal.ofReal ((min (t / 20) r) ^ 4 / t ^ 2)) =
      ENNReal.ofReal (r ^ 3 / 20) := by
    have he : (fun t => ENNReal.ofReal ((min (t / 20) r) ^ 4 / t ^ 2))
        =ᵐ[volume.restrict (Ioi (20 * r))] fun t => ENNReal.ofReal (r ^ 4 * t ^ (-2 : ℝ)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [min_eq_right (by linarith [show 20 * r < t from ht]), Real.rpow_neg (by linarith [show 20 * r < t from ht] : 0 ≤ t),
        Real.rpow_two, div_eq_mul_inv]
    rw [lintegral_congr_ae he, ← ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) h20).const_mul (r ^ 4))
      (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have ht0 : 0 ≤ t := h20.le.trans (le_of_lt ht)
        positivity), integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) h20]
    congr 1
    norm_num [Real.rpow_neg_one]
    field_simp
  rw [hhead, htail, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The nonnegative integral of a natural power of the absolute value. -/
def moment (f : ℝ → ℝ) (p : ℕ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p)

theorem moment_congr {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) (p : ℕ) :
    moment f p = moment g p := by
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem eLpNorm_pow_eq_moment (f : ℝ → ℝ) {p : ℕ} (hp : p ≠ 0) :
    eLpNorm f p volume ^ p = moment f p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hp) (by finiteness)]
  simp only [ENNReal.toReal_natCast]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    one_div_mul_cancel (by exact_mod_cast hp : (p : ℝ) ≠ 0), ENNReal.rpow_one]
  apply lintegral_congr
  intro x
  rw [ENNReal.rpow_natCast, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem measure_norm_ge_le {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    {p : ℕ} (hp : p ≠ 0) {t : ℝ} (ht : 0 < t) :
    volume {x | t ≤ ‖f x‖} ≤ ENNReal.ofReal (t⁻¹ ^ p) * moment f p := by
  have h := meas_ge_le_mul_pow_eLpNorm_enorm volume
    (show (p : ℝ≥0∞) ≠ 0 by exact_mod_cast hp)
    (show (p : ℝ≥0∞) ≠ ∞ by finiteness) hf
    (show ENNReal.ofReal t ≠ 0 by positivity) (by simp)
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast, eLpNorm_pow_eq_moment f hp,
    ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] at h
  rwa [← ENNReal.ofReal_inv_of_pos ht, ← ENNReal.ofReal_pow (by positivity)] at h

theorem moment_cube_layercake {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume) :
    moment f 3 = 3 * ∫⁻ t in Ioi (0 : ℝ), volume {x | t ≤ ‖f x‖} * ENNReal.ofReal (t ^ 2) := by
  have h := lintegral_rpow_eq_lintegral_meas_le_mul volume
    (Eventually.of_forall fun x => norm_nonneg (f x)) hf.norm.aemeasurable
    (by norm_num : (0 : ℝ) < 3)
  simpa only [moment, Real.rpow_ofNat, ENNReal.ofReal_ofNat, show (3 : ℝ) - 1 = 2 by norm_num] using h

theorem integrated_remainder {f : ℝ → ℝ} (hf : Measurable f) :
    (∫⁻ t in Ioi (0 : ℝ), moment (fun x => f x - clip (t / 20) (f x)) 2) =
      ENNReal.ofReal (20 / 3 : ℝ) * moment f 3 := by
  have he : (fun t => moment (fun x => f x - clip (t / 20) (f x)) 2)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => ∫⁻ x, ENNReal.ofReal ((max (‖f x‖ - t / 20) 0) ^ 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    apply lintegral_congr
    intro x
    rw [Real.norm_eq_abs, abs_sub_clip (by linarith [show 0 < t from ht])]
    rfl
  rw [lintegral_congr_ae he, lintegral_lintegral_swap]
  · simp_rw [lintegral_remainder _ (norm_nonneg _), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20 / 3)]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · apply Measurable.aemeasurable
    fun_prop

theorem integrated_clipped {f : ℝ → ℝ} (hf : Measurable f) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t⁻¹ ^ 2) *
      moment (fun x => clip (t / 20) (f x)) 4) =
        ENNReal.ofReal (1 / 15 : ℝ) * moment f 3 := by
  have he : (fun t => ENNReal.ofReal (t⁻¹ ^ 2) * moment (fun x => clip (t / 20) (f x)) 4)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => ∫⁻ x, ENNReal.ofReal ((min (t / 20) ‖f x‖) ^ 4 / t ^ 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [moment, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    rw [Real.norm_eq_abs, abs_clip (by linarith [show 0 < t from ht]),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_eq_mul_inv, inv_pow, mul_comm]
    rfl
  rw [lintegral_congr_ae he, lintegral_lintegral_swap]
  · simp_rw [lintegral_clipped _ (norm_nonneg _), div_eq_mul_inv, mul_comm _ (15 : ℝ)⁻¹,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 15⁻¹)]
    simp only [ENNReal.ofReal_one, mul_one]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · apply Measurable.aemeasurable
    fun_prop

private theorem measure_norm_add_ge {f g h : ℝ → ℝ} (he : h =ᵐ[volume] f + g) (t : ℝ) :
    volume {x | t ≤ ‖h x‖} ≤ volume {x | t / 2 ≤ ‖f x‖} + volume {x | t / 2 ≤ ‖g x‖} := by
  calc
    _ ≤ volume ({x | t / 2 ≤ ‖f x‖} ∪ {x | t / 2 ≤ ‖g x‖}) := by
      apply measure_mono_ae
      filter_upwards [he] with x hx
      intro hxt
      change t / 2 ≤ ‖f x‖ ∨ t / 2 ≤ ‖g x‖
      by_contra! hn
      change t ≤ ‖h x‖ at hxt
      have ht : t ≤ ‖f x + g x‖ := by simpa only [hx, Pi.add_apply] using hxt
      linarith [norm_add_le (f x) (g x)]
    _ ≤ _ := measure_union_le _ _

variable (U : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 volume)
  (hU2 : ∀ g : Lp ℝ 2 volume, moment (U g) 2 ≤ moment g 2)
  (hU4 : ∀ (g : ℝ → ℝ) (h2 : MemLp g 2 volume) (_h4 : MemLp g 4 volume),
    moment (U (h2.toLp g)) 4 ≤ ENNReal.ofReal (625 / 16 : ℝ) * moment g 4)

include hU2 hU4

private theorem weighted_tail_le (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    {t : ℝ} (ht : 0 < t) :
    volume {x | t ≤ ‖U (hf.toLp f) x‖} * ENNReal.ofReal (t ^ 2) ≤
      4 * moment (fun x => f x - clip (t / 20) (f x)) 2 +
      625 * (ENNReal.ofReal (t⁻¹ ^ 2) * moment (fun x => clip (t / 20) (f x)) 4) := by
  have ha : 0 ≤ t / 20 := by positivity
  let small : ℝ → ℝ := fun x => clip (t / 20) (f x)
  let big : ℝ → ℝ := f - small
  have hs2 : MemLp small 2 volume := clip_mem_two hf ha
  have hs4 : MemLp small 4 volume := clip_mem_four hf ha
  have hb2 : MemLp big 2 volume := hf.sub hs2
  have he : hf.toLp f = hb2.toLp big + hs2.toLp small := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards with x
    simp [big]
  have hu : U (hf.toLp f) =ᵐ[volume] (U (hb2.toLp big) : ℝ → ℝ) + U (hs2.toLp small) := by
    rw [he, map_add]
    exact Lp.coeFn_add _ _
  have hb : moment (U (hb2.toLp big)) 2 ≤ moment big 2 :=
    (hU2 _).trans_eq (moment_congr hb2.coeFn_toLp 2)
  have hs := hU4 small hs2 hs4
  have htail := (measure_norm_add_ge hu t).trans (add_le_add
    ((measure_norm_ge_le (Lp.memLp _).1 (by norm_num : (2 : ℕ) ≠ 0) (half_pos ht)).trans
      (mul_le_mul_right hb _))
    ((measure_norm_ge_le (Lp.memLp _).1 (by norm_num : (4 : ℕ) ≠ 0) (half_pos ht)).trans
      (mul_le_mul_right hs _)))
  have hc2 : ENNReal.ofReal ((t / 2)⁻¹ ^ 2) * ENNReal.ofReal (t ^ 2) = 4 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have he2 : (t / 2)⁻¹ ^ 2 * t ^ 2 = 4 := by field_simp; ring
    rw [he2]
    norm_num
  have hc4 : ENNReal.ofReal ((t / 2)⁻¹ ^ 4) * ENNReal.ofReal (625 / 16 : ℝ) *
      ENNReal.ofReal (t ^ 2) = 625 * ENNReal.ofReal (t⁻¹ ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have he4 : (t / 2)⁻¹ ^ 4 * (625 / 16) * t ^ 2 = 625 * (t⁻¹ ^ 2) := by field_simp; ring
    rw [he4, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 625), ENNReal.ofReal_ofNat]
  calc
    _ ≤ (ENNReal.ofReal ((t / 2)⁻¹ ^ 2) * moment big 2 +
      ENNReal.ofReal ((t / 2)⁻¹ ^ 4) * (ENNReal.ofReal (625 / 16 : ℝ) * moment small 4)) *
        ENNReal.ofReal (t ^ 2) := mul_le_mul_left htail _
    _ = (ENNReal.ofReal ((t / 2)⁻¹ ^ 2) * ENNReal.ofReal (t ^ 2)) * moment big 2 +
      (ENNReal.ofReal ((t / 2)⁻¹ ^ 4) * ENNReal.ofReal (625 / 16 : ℝ) * ENNReal.ofReal (t ^ 2)) *
        moment small 4 := by ring
    _ = _ := by
      rw [hc2, hc4]
      simp only [big, small, mul_assoc]
      rfl

/-- Clipping gives the cubic constant 205 for endpoint constants 1 and 5/2. -/
theorem moment_cube_le_measurable (f : ℝ → ℝ) (hf : MemLp f 2 volume) (hm : Measurable f) :
    moment (U (hf.toLp f)) 3 ≤ 205 * moment f 3 := by
  have hm1 : Measurable (fun t => moment (fun x => f x - clip (t / 20) (f x)) 2) := by
    apply Measurable.lintegral_prod_right
    unfold clip
    fun_prop
  rw [moment_cube_layercake (Lp.memLp _).1]
  calc
    _ ≤ 3 * ∫⁻ t in Ioi (0 : ℝ),
        4 * moment (fun x => f x - clip (t / 20) (f x)) 2 +
        625 * (ENNReal.ofReal (t⁻¹ ^ 2) * moment (fun x => clip (t / 20) (f x)) 4) := by
      apply mul_le_mul_right
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact weighted_tail_le U hU2 hU4 f hf ht
    _ = _ := by
      rw [lintegral_add_left (show Measurable (fun t => (4 : ℝ≥0∞) *
          moment (fun x => f x - clip (t / 20) (f x)) 2) from measurable_const.mul hm1),
        lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ∞),
        lintegral_const_mul' _ _ (by norm_num : (625 : ℝ≥0∞) ≠ ∞),
        integrated_remainder hm, integrated_clipped hm]
      have he : (3 : ℝ≥0∞) * (4 * ENNReal.ofReal (20 / 3 : ℝ) +
          625 * ENNReal.ofReal (1 / 15 : ℝ)) = 205 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by norm_num)).mp
        rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
        norm_num
      calc
        _ = (3 * (4 * ENNReal.ofReal (20 / 3 : ℝ) +
          625 * ENNReal.ofReal (1 / 15 : ℝ))) * moment f 3 := by ring
        _ = _ := by rw [he]

/-- The cubic estimate is insensitive to the chosen measurable representative. -/
theorem moment_cube_le (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    moment (U (hf.toLp f)) 3 ≤ 205 * moment f 3 := by
  let g := hf.1.mk f
  have he : f =ᵐ[volume] g := hf.1.ae_eq_mk
  have hg : MemLp g 2 volume := hf.ae_eq he
  have hc : hf.toLp f = hg.toLp g := MemLp.toLp_congr hf hg he
  rw [hc, moment_congr he 3]
  exact moment_cube_le_measurable U hU2 hU4 g hg hf.1.stronglyMeasurable_mk.measurable

/-- Endpoint bounds 1 and 5/2 imply the L3 bound 6, with no prior L3 membership assumption. -/
theorem eLpNorm_three_le (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    eLpNorm (U (hf.toLp f)) 3 volume ≤ 6 * eLpNorm f 3 volume := by
  have he (g : ℝ → ℝ) : eLpNorm g 3 volume ^ 3 = moment g 3 := by
    simpa only [Nat.cast_ofNat] using eLpNorm_pow_eq_moment g (by norm_num : (3 : ℕ) ≠ 0)
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [mul_pow, he, he]
  exact (moment_cube_le U hU2 hU4 f hf).trans
    (mul_le_mul_left (by norm_num : (205 : ℝ≥0∞) ≤ 6 ^ 3) _)

theorem memLp_three (f : ℝ → ℝ) (hf : MemLp f 2 volume) (h3 : MemLp f 3 volume) :
    MemLp (fun x => U (hf.toLp f) x) 3 volume := by
  refine ⟨(Lp.memLp _).1, ?_⟩
  exact (eLpNorm_three_le U hU2 hU4 f hf).trans_lt
    (ENNReal.mul_lt_top (by norm_num) h3.2)

end HilbertUMD.TwoFourInterpolation
