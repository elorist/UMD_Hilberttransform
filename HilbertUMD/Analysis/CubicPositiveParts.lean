import HilbertUMD.Analysis.CubicLp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The L³ norms of the two positive parts share the original cubic mass. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace HilbertUMD.CubicLp

variable {S ι E : Type*} [MeasurableSpace S] [Fintype ι]
  [NormedAddCommGroup E] (μ : Measure S)

theorem integrable_norm_cube (f : Lp E 3 μ) : Integrable (fun x => ‖f x‖ ^ 3) μ := by
  have h := (Lp.memLp f).norm_rpow (by norm_num) (by finiteness)
  rw [memLp_one_iff_integrable] at h
  simpa using h

theorem integral_norm_cube (f : Lp E 3 μ) : (∫ x, ‖f x‖ ^ 3 ∂μ) = ‖f‖ ^ 3 := by
  have he : eLpNorm (fun x => ‖f x‖ ^ (3 : ℝ)) 1 μ = eLpNorm f 3 μ ^ 3 := by
    rw [eLpNorm_norm_rpow _ (by norm_num)]
    norm_num [ENNReal.rpow_natCast]
  have hm : AEStronglyMeasurable (fun x => ‖f x‖ ^ (3 : ℝ)) μ := by
    simpa using (integrable_norm_cube μ f).aestronglyMeasurable
  have hi := lpNorm_one_eq_integral_norm hm
  rw [← toReal_eLpNorm hm, he, ENNReal.toReal_pow, ← Lp.norm_def] at hi
  simpa only [Real.rpow_ofNat, norm_pow, norm_norm] using hi.symm

theorem l1Norm_positiveParts_cube (f : Space (ι := ι) μ 3) :
    l1Norm μ 3 (positivePartLp μ f) ^ 3 +
      l1Norm μ 3 (positivePartLp μ (-f)) ^ 3 ≤ l1Norm μ 3 f ^ 3 := by
  let p := (toL1 (ι := ι)).compLpL 3 μ (positivePartLp μ f)
  let q := (toL1 (ι := ι)).compLpL 3 μ (positivePartLp μ (-f))
  let a := (toL1 (ι := ι)).compLpL 3 μ f
  change ‖p‖ ^ 3 + ‖q‖ ^ 3 ≤ ‖a‖ ^ 3
  rw [← integral_norm_cube μ p, ← integral_norm_cube μ q, ← integral_norm_cube μ a,
    ← integral_add (integrable_norm_cube μ p) (integrable_norm_cube μ q)]
  apply integral_mono_ae ((integrable_norm_cube μ p).add (integrable_norm_cube μ q))
    (integrable_norm_cube μ a)
  filter_upwards [(toL1 (ι := ι)).coeFn_compLpL (positivePartLp μ f),
    (toL1 (ι := ι)).coeFn_compLpL (positivePartLp μ (-f)),
    (toL1 (ι := ι)).coeFn_compLpL f, coeFn_positivePartLp μ f,
    coeFn_positivePartLp μ (-f), Lp.coeFn_neg f,
    nonnegative_positivePartLp μ f, nonnegative_positivePartLp μ (-f)]
    with x hp hq ha hpf hqf hn hpp hqp
  have he : ‖p x‖ + ‖q x‖ = ‖a x‖ := by
    change ‖(toL1 (ι := ι)).compLpL 3 μ (positivePartLp μ f) x‖ +
      ‖(toL1 (ι := ι)).compLpL 3 μ (positivePartLp μ (-f)) x‖ =
        ‖(toL1 (ι := ι)).compLpL 3 μ f x‖
    rw [hp, hq, ha, norm_toL1, norm_toL1, norm_toL1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_of_nonneg (hpp i), abs_of_nonneg (hqp i), hpf, hqf, hn]
    simp only [Pi.neg_apply, abs_neg]
    ring
  dsimp only [Pi.add_apply]
  rw [← he]
  nlinarith [mul_nonneg (sq_nonneg ‖p x‖) (norm_nonneg (q x)),
    mul_nonneg (norm_nonneg (p x)) (sq_nonneg ‖q x‖)]

/-- A rational upper bound for 2^(2/3), sufficient for the paper's rounded constants. -/
theorem l1Norm_positiveParts_sum (f : Space (ι := ι) μ 3) :
    l1Norm μ 3 (positivePartLp μ f) + l1Norm μ 3 (positivePartLp μ (-f)) ≤
      (127 / 80 : ℝ) * l1Norm μ 3 f := by
  let a := l1Norm μ 3 (positivePartLp μ f)
  let b := l1Norm μ 3 (positivePartLp μ (-f))
  let c := l1Norm μ 3 f
  have ha : 0 ≤ a := apply_nonneg _ _
  have hb : 0 ≤ b := apply_nonneg _ _
  have hc : 0 ≤ c := apply_nonneg _ _
  have hcube : a ^ 3 + b ^ 3 ≤ c ^ 3 := l1Norm_positiveParts_cube μ f
  have hs : (a + b) ^ 3 ≤ 4 * c ^ 3 := by
    nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]
  change a + b ≤ (127 / 80 : ℝ) * c
  by_contra h
  have ht : (127 / 80 : ℝ) * c < a + b := lt_of_not_ge h
  have hp := pow_lt_pow_left₀ ht (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
  nlinarith [pow_nonneg hc 3]

end HilbertUMD.CubicLp
