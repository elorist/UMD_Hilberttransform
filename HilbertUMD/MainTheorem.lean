import HilbertUMD.Main.Assembly
import HilbertUMD.Main.UpperBounds
import HilbertUMD.Matrices.SummationUpper
import HilbertUMD.Main.QuantitativeConstants
import HilbertUMD.Main.PaperStatement

/-!
# The p=2 main theorem over both scalar fields

All eight inequalities in manuscript Theorem 1.1 are derived here, with
common positive finite constants quantified before the depth and scalar
field. There are no remaining hypotheses about the manuscript's lemmas.
`theorem_1_1` below uses the fixed paper's notation, dimensions, and n/sqrt(n)
growth rates. `main_theorem_p2` retains the internal n+1 formulation.
The quantitative companion below includes the numerical coefficients 1/7,
285 over R, 448 over C, and 57 over either field, retaining the manuscript's
minimum form for the square-root upper bounds and the Y_n UMD lower bound
2n/3. The two sharper square-root
lower coefficients of Remark 1.2 and p≠2 extrapolation remain outside its
statement. Only Theorem 1.1 is the manuscript certification target.

All analytic interfaces have checked proofs. The complete dependency closure
uses only the standard foundational axioms, with no admitted proofs.

The quantitative real UMD bound uses the real Paley-Walsh reduction directly.

The UMD definition tests all sigma-finite sample spaces and filtrations in
any chosen sample-space universe, with all real or complex unimodular coefficients.
`theorem_1_1` is universe-polymorphic, using the proved equality of p=2 UMD
constants across universes. The internal and quantitative companions retain
universe zero; the same equality transports their bounds without loss.
-/

noncomputable section
open scoped ENNReal NNReal
namespace HilbertUMD

universe uΩ

/-- The full p=2 main theorem: one pair of universal constants works for
both R and C and for every n≥1. Each `P2MainBounds` contains all eight
inequalities, using the actual Hilbert and UMD constants. -/
theorem main_theorem_p2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      P2MainBounds ℝ n c C ∧ P2MainBounds ℂ n c C := by
  obtain ⟨A, hA⟩ := exists_summation_umdConstant_upper_complex
  exact p2_main_of_uniform_matrix_bounds A signedDyadicUpperConstant
    (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hA
    signedDyadic_hilbert_sqrt_upper_real signedDyadic_hilbert_sqrt_upper_complex

/-- Theorem 1.1 of the fixed 9 September 2026 paper: the two spaces have
dimension 2^n, and one pair of positive universal constants gives all four
comparisons with n and sqrt(n), simultaneously over the real and complex fields.
The sample-space universe is arbitrary, and changing it preserves the constants. -/
theorem theorem_1_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Paper.Theorem11Bounds.{uΩ} ℝ n c C ∧ Paper.Theorem11Bounds.{uΩ} ℂ n c C := by
  obtain ⟨c, C, hc, hC, h⟩ := main_theorem_p2
  refine ⟨c, 2 * C, hc, mul_pos (by norm_num) hC, ?_⟩
  intro n hn
  exact ⟨(Paper.theorem11Bounds_of_p2 hc.le hC.le hn (h n hn).1).changeUniverse,
    (Paper.theorem11Bounds_of_p2 hc.le hC.le hn (h n hn).2).changeUniverse⟩

/-- The real UMD upper coefficient established by the Lean estimates. -/
def xUMDUpperConstantReal : ℝ := 285

/-- The complex UMD upper coefficient established by the Lean estimates. -/
def xUMDUpperConstant : ℝ := 448

/-- Explicit Hilbert graph coefficient supplied by the signed matrix bound. -/
def yHilbertUpperConstant : ℝ := 57

/-- The quantitative companion to the main theorem. It has the form of the
manuscript's numerical remark, with the constants actually proved in Lean. -/
theorem main_theorem_p2_quantitative (n : ℕ) (hn : 1 ≤ n) :
    P2QuantitativeBounds ℝ n (1 / 7) xUMDLowerConstant
      yHilbertLowerConstant xUMDUpperConstantReal yHilbertUpperConstant ∧
    P2QuantitativeBounds ℂ n (1 / 7) xUMDLowerConstant
      yHilbertLowerConstant xUMDUpperConstant yHilbertUpperConstant := by
  have hxUR := xSpace_umd_upper_285_real n
  have hxUC : umdConstant.{0} 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) ≤
      ENNReal.ofReal (xUMDUpperConstant * Real.sqrt ((n : ℝ) + 1)) :=
    xSpace_umd_upper_448_complex n
  have hyHR : hilbertConstant 2 (ContinuousLinearMap.id ℝ (YSpace ℝ n)) ≤
      ENNReal.ofReal (yHilbertUpperConstant * Real.sqrt ((n : ℝ) + 1)) :=
    ySpace_hilbert_upper_57_real n
  have hyHC : hilbertConstant 2 (ContinuousLinearMap.id ℂ (YSpace ℂ n)) ≤
      ENNReal.ofReal (yHilbertUpperConstant * Real.sqrt ((n : ℝ) + 1)) :=
    ySpace_hilbert_upper_57_complex n
  constructor
  · exact {
      x_hilbert_lower := by
        simpa only [one_div_mul_eq_div] using xSpace_hilbert_lower_seventh_real n
      x_hilbert_upper := xSpace_hilbert_linear_upper_real n
      x_umd_lower := xSpace_umd_sqrt_lower_real n hn
      x_umd_upper := le_min (umdConstant_two_graphSpace_le (summation_transferAssumptions n))
        hxUR
      y_umd_lower := (ySpace_umd_bounds_real n).1
      y_umd_upper := (ySpace_umd_bounds_real n).2
      y_hilbert_lower := ySpace_hilbert_sqrt_lower_real n hn
      y_hilbert_upper := le_min
        (hilbertConstant_two_real_graph_le (signedDyadic_transferAssumptions n)) hyHR }
  · exact {
      x_hilbert_lower := by
        simpa only [one_div_mul_eq_div] using xSpace_hilbert_lower_seventh_complex n
      x_hilbert_upper := xSpace_hilbert_linear_upper_complex n
      x_umd_lower := xSpace_umd_sqrt_lower_complex n hn
      x_umd_upper := le_min (umdConstant_two_graphSpace_le (summation_transferAssumptions n)) hxUC
      y_umd_lower := (ySpace_umd_bounds_complex n).1
      y_umd_upper := (ySpace_umd_bounds_complex n).2
      y_hilbert_lower := ySpace_hilbert_sqrt_lower_complex n hn
      y_hilbert_upper := le_min
        (hilbertConstant_two_complex_graph_le (signedDyadic_transferAssumptions n)) hyHC }

end HilbertUMD
