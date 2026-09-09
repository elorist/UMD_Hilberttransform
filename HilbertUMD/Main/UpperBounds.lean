import HilbertUMD.Matrices.SignedDyadicUpper

/-! Actual sharp graph-space upper bounds, derived from the proved matrix
bounds. The scalar analytic interfaces and both matrix bounds are proved. -/

noncomputable section
open scoped ENNReal NNReal
namespace HilbertUMD

theorem coe_nnreal_sqrt_depth (A : ℝ≥0) (n : ℕ) :
    ((A * NNReal.sqrt (n+1) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal ((A : ℝ) * Real.sqrt ((n : ℝ)+1)) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp only [NNReal.coe_mul, Real.coe_sqrt, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]

theorem signedDyadic_hilbert_sqrt_upper_real (n : ℕ) :
    hilbertConstant 2 (signedDyadicOperator (𝕜 := ℝ) n) ≤
      ENNReal.ofReal ((signedDyadicUpperConstant : ℝ) * Real.sqrt ((n : ℝ)+1)) := by
  rw [← coe_nnreal_sqrt_depth]
  exact signedDyadic_hilbertConstant_upper_real n

theorem signedDyadic_hilbert_sqrt_upper_complex (n : ℕ) :
    hilbertConstant 2 (signedDyadicOperator (𝕜 := ℂ) n) ≤
      ENNReal.ofReal ((signedDyadicUpperConstant : ℝ) * Real.sqrt ((n : ℝ)+1)) := by
  rw [← coe_nnreal_sqrt_depth]
  exact signedDyadic_hilbertConstant_upper_complex n

end HilbertUMD
