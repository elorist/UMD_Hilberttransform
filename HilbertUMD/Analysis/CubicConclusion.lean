import HilbertUMD.Analysis.CubicInterpolation
import HilbertUMD.Analysis.CubicDual

/-!
# The compatible-operator L² consequence of the cubic lemma

This applies the real L³ endpoint of Lemma 3.2 to compatible real L²/L³
operators and their actual complexifications, on every sigma-finite measure
and every finite coordinate index. The general real L³ estimate is in CubicEndpoint.
The original energy argument, positive restriction, four-part decomposition,
skew dual endpoint, and compatibility are proved in the preceding local modules.

The dual endpoint uses the proved isometric dual representation.
Finite-coordinate norming and the required Riesz--Thorin midpoint estimate are
proved locally.
No assertion of the original
cubic lemma is directly admitted.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace HilbertUMD.CubicLp

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S) [SigmaFinite μ]

/-- The complexified L² consequence, with explicit uniform constant. -/
theorem cubic_two_complex
    (V : CompatibleRealOperator (ι := ι) μ)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ u, Nonnegative μ u → energy μ V.atThree u ≤ B * l1Norm μ 3 u ^ 3)
    (f : ComplexSpace (ι := ι) μ 2) :
    ‖complexify μ V.atTwo f‖ ≤ ((127 / 40) * Real.sqrt (9 * B)) * complexL1Norm μ 2 f := by
  obtain ⟨W, hW, hAgree⟩ := exists_dual_endpoint μ V
    (show 0 ≤ (127 / 80) * Real.sqrt (9 * B) by positivity) (real_endpoint μ V.atThree B hB hE)
  exact cubic_two_complex_of_dual_endpoint μ V B hB hE W hW hAgree f

/-- The L² consequence for the original real realization. -/
theorem cubic_two_real
    (V : CompatibleRealOperator (ι := ι) μ)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ u, Nonnegative μ u → energy μ V.atThree u ≤ B * l1Norm μ 3 u ^ 3)
    (f : Space (ι := ι) μ 2) :
    ‖V.atTwo f‖ ≤ ((127 / 40) * Real.sqrt (9 * B)) * l1Norm μ 2 f :=
  real_bound_of_complexified_bound μ V.atTwo ((127 / 40) * Real.sqrt (9 * B))
    (cubic_two_complex μ V B hB hE) f

end HilbertUMD.CubicLp
