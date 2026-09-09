import HilbertUMD.Main.LowerBounds
import HilbertUMD.Main.Transfer
import HilbertUMD.LowerBounds.HilbertLowerConstants
import HilbertUMD.Matrices.SummationUpperConstants
import HilbertUMD.Matrices.SignedDyadicUpperConstants

/-! The four requested numerical alignments after transfer to X_n and Y_n. -/

noncomputable section
open scoped ENNReal
namespace HilbertUMD

private theorem round_graph_coefficient (n : ℕ) {x : ℝ≥0∞} {A C : ℝ}
    (hx : x ≤ ENNReal.ofReal (Real.sqrt (A ^ 2 + 2) * Real.sqrt ((n : ℝ) + 1)))
    (hC : 0 ≤ C) (hAC : A ^ 2 + 2 ≤ C ^ 2) :
    x ≤ ENNReal.ofReal (C * Real.sqrt ((n : ℝ) + 1)) :=
  hx.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_iff.mpr ⟨hC, hAC⟩) (Real.sqrt_nonneg _)))

theorem xSpace_hilbert_lower_seventh_real (n : ℕ) :
    ENNReal.ofReal (((n : ℝ) + 1) / 7) ≤
      hilbertConstant 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) :=
  (summation_hilbertConstant_seventh (𝕜 := ℝ) n).trans
    (hilbertConstant_matrix_le_graphSpace (summation_transferAssumptions n) (summation_le_l1 n) 2)

theorem xSpace_hilbert_lower_seventh_complex (n : ℕ) :
    ENNReal.ofReal (((n : ℝ) + 1) / 7) ≤
      hilbertConstant 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) :=
  (summation_hilbertConstant_seventh (𝕜 := ℂ) n).trans
    (hilbertConstant_matrix_le_graphSpace (summation_transferAssumptions n) (summation_le_l1 n) 2)

theorem xSpace_umd_upper_285_real (n : ℕ) :
    umdConstant.{0} 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) ≤
      ENNReal.ofReal (285 * Real.sqrt ((n : ℝ) + 1)) :=
  round_graph_coefficient n
    (xSpace_umd_sqrt_upper_of_matrix_real n 284 (by norm_num) (summation_umdConstant_real_284 n))
    (by norm_num) (by norm_num)

theorem xSpace_umd_upper_448_complex (n : ℕ) :
    umdConstant.{0} 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) ≤
      ENNReal.ofReal (448 * Real.sqrt ((n : ℝ) + 1)) :=
  round_graph_coefficient n
    (xSpace_umd_sqrt_upper_of_matrix_complex n (44799 / 100) (by norm_num)
      (summation_umdConstant_complex_44799 n)) (by norm_num) (by norm_num)

theorem ySpace_hilbert_upper_57_real (n : ℕ) :
    hilbertConstant 2 (ContinuousLinearMap.id ℝ (YSpace ℝ n)) ≤
      ENNReal.ofReal (57 * Real.sqrt ((n : ℝ) + 1)) :=
  round_graph_coefficient n
    (ySpace_hilbert_sqrt_upper_of_matrix_real n 56 (by norm_num) (signedDyadic_hilbertConstant_real_56 n))
    (by norm_num) (by norm_num)

theorem ySpace_hilbert_upper_57_complex (n : ℕ) :
    hilbertConstant 2 (ContinuousLinearMap.id ℂ (YSpace ℂ n)) ≤
      ENNReal.ofReal (57 * Real.sqrt ((n : ℝ) + 1)) :=
  round_graph_coefficient n
    (ySpace_hilbert_sqrt_upper_of_matrix_complex n 56 (by norm_num) (signedDyadic_hilbertConstant_complex_56 n))
    (by norm_num) (by norm_num)

end HilbertUMD
