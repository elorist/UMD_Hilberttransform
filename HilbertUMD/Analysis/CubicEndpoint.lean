import HilbertUMD.Analysis.CubicPositiveParts
import HilbertUMD.Analysis.MixedLpNorming

/-! The original cubic argument through its L³ endpoint. The finite-coordinate
Lp norming formula, restriction to nonnegative tests, square-norm identity,
and rescaling are all checked without admitted dependencies.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD.CubicLp

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S)

/-- The positive unit-ball L³ endpoint of Lemma 3.2. -/
theorem positive_unit_endpoint
    (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ u, Nonnegative μ u → energy μ V u ≤ B * l1Norm μ 3 u ^ 3)
    (f : Space (ι := ι) μ 3) (hf : Nonnegative μ f) (hfp : l1Norm μ 3 f ≤ 1) :
    ‖V f‖ ≤ Real.sqrt (9 * B) := by
  have hs : ‖squareLp μ (V f)‖ ≤ 9 * B := by
    apply CubicLp.norm_le_of_l1_unit_tests μ (p := 3 / 2) (q := 3)
      (by apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp; norm_num)
      (by finiteness) (by norm_num) (by simp) _ _ (by positivity)
    intro g hg
    exact (abs_pair_square_le μ (V f) g).trans
      (mixed_integral_le_nine μ V B hB hE f (absLp μ g) hf (nonnegative_absLp μ g)
        hfp (by simpa only [l1Norm_absLp] using hg))
  rw [norm_squareLp] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa only [Real.sq_sqrt (show 0 ≤ 9 * B by positivity)] using hs

/-- Homogeneity removes the unit-ball restriction without requiring B>0. -/
theorem positive_endpoint
    (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ u, Nonnegative μ u → energy μ V u ≤ B * l1Norm μ 3 u ^ 3)
    (f : Space (ι := ι) μ 3) (hf : Nonnegative μ f) :
    ‖V f‖ ≤ Real.sqrt (9 * B) * l1Norm μ 3 f := by
  by_cases hz : l1Norm μ 3 f = 0
  · have hfz : f = 0 := norm_eq_zero.mp (le_antisymm ((norm_le_l1Norm μ f).trans_eq hz) (norm_nonneg _))
    simp [hfz]
  have hp : 0 < l1Norm μ 3 f := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hz)
  have hs := positive_unit_endpoint μ V B hB hE ((l1Norm μ 3 f)⁻¹ • f)
    (hf.smul μ (inv_nonneg.mpr hp.le)) (by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hz])
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)] at hs
  have hh := mul_le_mul_of_nonneg_left hs hp.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hz, one_mul, mul_comm] using hh

/-- Splitting into positive and negative real parts uses their shared cubic mass. -/
theorem real_endpoint
    (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ u, Nonnegative μ u → energy μ V u ≤ B * l1Norm μ 3 u ^ 3)
    (f : Space (ι := ι) μ 3) :
    ‖V f‖ ≤ ((127 / 80) * Real.sqrt (9 * B)) * l1Norm μ 3 f := by
  have hp := positive_endpoint μ V B hB hE (positivePartLp μ f) (nonnegative_positivePartLp μ f)
  have hn := positive_endpoint μ V B hB hE (positivePartLp μ (-f)) (nonnegative_positivePartLp μ (-f))
  have hpn := mul_le_mul_of_nonneg_left (l1Norm_positiveParts_sum μ f) (Real.sqrt_nonneg (9 * B))
  have hv : V f = V (positivePartLp μ f) - V (positivePartLp μ (-f)) := by
    rw [← map_sub, positivePartLp_sub]
  rw [hv]
  exact (norm_sub_le _ _).trans (by nlinarith)

end HilbertUMD.CubicLp
