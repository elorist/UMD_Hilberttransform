import HilbertUMD.Foundations.OperatorSpaces
import HilbertUMD.UMD.DyadicMartingale

/-!
# Completed bounds toward the p=2 main theorem

The UMD assertion for Y_n is proved with lower bound 2n/3 and upper bound
n+1. These results use the full sigma-finite UMD definition with sample
spaces in universe zero. No external citation is admitted in these proofs.
The other three comparisons are assembled in the neighboring main-theorem modules.
-/

noncomputable section
open scoped ENNReal NNReal

namespace HilbertUMD

/-- Both sides of the manuscript's UMD comparison for Y_n, with explicit
constants independent of n and of the real or complex scalar field. -/
theorem ySpace_umd_bounds (𝕜 : Type*) [RCLike 𝕜] (n : ℕ)
    [NormedSpace ℝ (HSpace 𝕜 n)] [NormedSpace ℝ (YSpace 𝕜 n)] :
    ENNReal.ofReal (2 * (n : ℝ) / 3) ≤
        umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ∧
      umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ≤ (n : ℝ≥0∞) + 1 := by
  constructor
  · calc
      ENNReal.ofReal (2 * (n : ℝ) / 3) ≤
          umdConstant.{0} 2 (signedDyadicOperator (𝕜 := 𝕜) n) :=
        signedDyadic_umdConstant_lower n
      _ ≤ umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) :=
        umdConstant_signedDyadic_le_ySpace
  · exact umdConstant_two_graphSpace_le (signedDyadic_transferAssumptions n)

theorem ySpace_umd_bounds_real (n : ℕ) :
    ENNReal.ofReal (2 * (n : ℝ) / 3) ≤
        umdConstant.{0} 2 (ContinuousLinearMap.id ℝ (YSpace ℝ n)) ∧
      umdConstant.{0} 2 (ContinuousLinearMap.id ℝ (YSpace ℝ n)) ≤ (n : ℝ≥0∞) + 1 :=
  ySpace_umd_bounds ℝ n

theorem ySpace_umd_bounds_complex (n : ℕ) :
    ENNReal.ofReal (2 * (n : ℝ) / 3) ≤
        umdConstant.{0} 2 (ContinuousLinearMap.id ℂ (YSpace ℂ n)) ∧
      umdConstant.{0} 2 (ContinuousLinearMap.id ℂ (YSpace ℂ n)) ≤ (n : ℝ≥0∞) + 1 :=
  ySpace_umd_bounds ℂ n

end HilbertUMD
