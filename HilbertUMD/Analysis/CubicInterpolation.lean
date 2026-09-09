import HilbertUMD.Analysis.CubicEndpoint
import HilbertUMD.Analysis.CubicComplex
import HilbertUMD.Analysis.Interpolation

/-! Compatibility and four-part complexification in the cubic argument.
The dual endpoint is an explicit hypothesis. The required midpoint interpolation
is proved in `HilbertUMD.Analysis.Interpolation`, with no admitted dependencies.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD.CubicLp

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S)

/-- Interpolate compatible real endpoints after their checked complexification.
The output is the given L² realization, not an unidentified extension. -/
theorem interpolate_real_endpoints
    (Vhalf : Space (ι := ι) μ (3 / 2) →L[ℝ] Space (ι := ι) μ (3 / 2))
    (Vtwo : Space (ι := ι) μ 2 →L[ℝ] Space (ι := ι) μ 2)
    (Vthree : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    (hTwoHalf : ∀ (f : Space (ι := ι) μ 2) (g : Space (ι := ι) μ (3 / 2)),
      f =ᵐ[μ] g → Vtwo f =ᵐ[μ] Vhalf g)
    (hTwoThree : ∀ (f : Space (ι := ι) μ 2) (g : Space (ι := ι) μ 3),
      f =ᵐ[μ] g → Vtwo f =ᵐ[μ] Vthree g)
    (M : ℝ) (hM : 0 ≤ M)
    (hHalf : ∀ f, ‖Vhalf f‖ ≤ M * l1Norm μ (3 / 2) f)
    (hThree : ∀ f, ‖Vthree f‖ ≤ M * l1Norm μ 3 f)
    (f : ComplexSpace (ι := ι) μ 2) :
    ‖complexify μ Vtwo f‖ ≤ (2 * M) * complexL1Norm μ 2 f :=
  HilbertUMD.riesz_thorin_l1_linf_two μ (complexify μ Vhalf) (complexify μ Vtwo)
    (complexify μ Vthree) (complexify_ae_eq μ Vtwo Vhalf hTwoHalf)
    (complexify_ae_eq μ Vtwo Vthree hTwoThree) (2 * M) (by positivity)
    (complexify_bound μ Vhalf M hM hHalf) (complexify_bound μ Vthree M hM hThree) f

/-- Real restriction of the same interpolated bound, checked through the
isometric real embedding and exact l¹ norm preservation. -/
theorem real_bound_of_complexified_bound
    (V : Space (ι := ι) μ 2 →L[ℝ] Space (ι := ι) μ 2)
    (K : ℝ) (hK : ∀ f, ‖complexify μ V f‖ ≤ K * complexL1Norm μ 2 f)
    (f : Space (ι := ι) μ 2) : ‖V f‖ ≤ K * l1Norm μ 2 f := by
  have hh := hK (ofRealLp μ 2 f)
  simpa only [complexify_ofRealLp, norm_ofRealLp, complexL1Norm_ofRealLp] using hh

/-- Intermediate cubic conclusion, with the dual endpoint explicitly exposed.
No part of this operator conclusion is directly admitted. -/
theorem cubic_two_complex_of_dual_endpoint
    (V : CompatibleRealOperator (ι := ι) μ)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ u, Nonnegative μ u → energy μ V.atThree u ≤ B * l1Norm μ 3 u ^ 3)
    (Vhalf : Space (ι := ι) μ (3 / 2) →L[ℝ] Space (ι := ι) μ (3 / 2))
    (hHalf : ∀ f, ‖Vhalf f‖ ≤ ((127 / 80) * Real.sqrt (9 * B)) * l1Norm μ (3 / 2) f)
    (hAgree : ∀ (f : Space (ι := ι) μ 2) (g : Space (ι := ι) μ (3 / 2)),
      f =ᵐ[μ] g → V.atTwo f =ᵐ[μ] Vhalf g)
    (f : ComplexSpace (ι := ι) μ 2) :
    ‖complexify μ V.atTwo f‖ ≤ ((127 / 40) * Real.sqrt (9 * B)) * complexL1Norm μ 2 f := by
  have hh := interpolate_real_endpoints μ Vhalf V.atTwo V.atThree hAgree V.agree
    ((127 / 80) * Real.sqrt (9 * B)) (by positivity) hHalf (real_endpoint μ V.atThree B hB hE) f
  convert hh using 1
  ring

end HilbertUMD.CubicLp
