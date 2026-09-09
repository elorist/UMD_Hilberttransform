import HilbertUMD.Hilbert.HilbertConstant
import HilbertUMD.UMD.UMD
import HilbertUMD.Foundations.Spaces

/-! Internal n+1 bounds and quantitative estimates. The literal n/sqrt(n)
statement of the fixed paper is in Main/PaperStatement.lean. -/

noncomputable section
open scoped ENNReal
namespace HilbertUMD

/-- All four comparisons, using actual principal-value Hilbert and full UMD
constants. The UMD sample-space universe is zero, as in the main lower bound.
The existential comparison constants do not assert the numerical values in
Remark 1.2 of the fixed paper. -/
structure P2MainBounds (𝕜 : Type*) [RCLike 𝕜] (n : ℕ)
    [NormedSpace ℝ (XSpace 𝕜 n)] [NormedSpace ℝ (YSpace 𝕜 n)] (c C : ℝ) : Prop where
  x_hilbert_lower : ENNReal.ofReal (c * ((n : ℝ)+1)) ≤
    hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n))
  x_hilbert_upper : hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) ≤
    ENNReal.ofReal (C * ((n : ℝ)+1))
  x_umd_lower : ENNReal.ofReal (c * Real.sqrt ((n : ℝ)+1)) ≤
    umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n))
  x_umd_upper : umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) ≤
    ENNReal.ofReal (C * Real.sqrt ((n : ℝ)+1))
  y_umd_lower : ENNReal.ofReal (c * ((n : ℝ)+1)) ≤
    umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n))
  y_umd_upper : umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ≤
    ENNReal.ofReal (C * ((n : ℝ)+1))
  y_hilbert_lower : ENNReal.ofReal (c * Real.sqrt ((n : ℝ)+1)) ≤
    hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n))
  y_hilbert_upper : hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ≤
    ENNReal.ofReal (C * Real.sqrt ((n : ℝ)+1))

/-- The numerical form of the four comparisons, retaining the individual
coefficients and both alternatives in the square-root upper bounds.
The coefficients are supplied by the checked Lean estimates; this structure
does not prescribe the sharper values in the manuscript's numerical remark. -/
structure P2QuantitativeBounds (𝕜 : Type*) [RCLike 𝕜] (n : ℕ)
    [NormedSpace ℝ (XSpace 𝕜 n)] [NormedSpace ℝ (YSpace 𝕜 n)]
    (cH cU cY CU CH : ℝ) : Prop where
  x_hilbert_lower : ENNReal.ofReal (cH * ((n : ℝ) + 1)) ≤
    hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n))
  x_hilbert_upper : hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) ≤
    (n : ℝ≥0∞) + 1
  x_umd_lower : ENNReal.ofReal (cU * Real.sqrt ((n : ℝ) + 1)) ≤
    umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n))
  x_umd_upper : umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) ≤
    min ((n : ℝ≥0∞) + 1) (ENNReal.ofReal (CU * Real.sqrt ((n : ℝ) + 1)))
  y_umd_lower : ENNReal.ofReal (2 * (n : ℝ) / 3) ≤
    umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n))
  y_umd_upper : umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ≤
    (n : ℝ≥0∞) + 1
  y_hilbert_lower : ENNReal.ofReal (cY * Real.sqrt ((n : ℝ) + 1)) ≤
    hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n))
  y_hilbert_upper : hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ≤
    min ((n : ℝ≥0∞) + 1) (ENNReal.ofReal (CH * Real.sqrt ((n : ℝ) + 1)))

end HilbertUMD
