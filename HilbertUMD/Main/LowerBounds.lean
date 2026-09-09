import HilbertUMD.Main.UMDBounds
import HilbertUMD.LowerBounds.SummationLower
import HilbertUMD.LowerBounds.SignedDyadicLower
import HilbertUMD.LowerBounds.BinaryLogit
import HilbertUMD.LowerBounds.HilbertLower
import HilbertUMD.Hilbert.HilbertGraphBounds

/-!
# Direct lower bounds for the main theorem

The X_n UMD lower estimate uses the actual finite dyadic witness. The Y_n
Hilbert lower estimate uses the logarithmic step witness and the checked
binary coefficient estimate. No Hilbert/UMD quadratic comparison is used.
-/

noncomputable section
open scoped ENNReal

namespace HilbertUMD

def xUMDLowerConstant : ℝ := 1 / (4 * Real.sqrt 2)

theorem xUMDLowerConstant_pos : 0 < xUMDLowerConstant := by
  unfold xUMDLowerConstant
  positivity

def yHilbertLowerConstant : ℝ := BinaryLogit.delta / Real.sqrt 2

theorem yHilbertLowerConstant_pos : 0 < yHilbertLowerConstant :=
  div_pos BinaryLogit.delta_pos (Real.sqrt_pos.mpr (by norm_num))

theorem sqrt_depth_div_sqrt_two_le (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt ((n : ℝ) + 1) / Real.sqrt 2 ≤ Real.sqrt (n : ℝ) := by
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num),
    Real.sq_sqrt (Nat.cast_nonneg n)]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Direct logarithmic-step lower bound, using the scalar principal-value
formula and the smooth-test extension. -/
theorem ySpace_hilbert_sqrt_lower_direct {𝕜 : Type*} [RCLike 𝕜]
    (n : ℕ) (hn : 1 ≤ n) [NormedSpace ℝ (YSpace 𝕜 n)]
    [IsScalarTower ℝ 𝕜 (YSpace 𝕜 n)] :
    ENNReal.ofReal (yHilbertLowerConstant * Real.sqrt ((n : ℝ) + 1)) ≤
      hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) := by
  have hs : yHilbertLowerConstant * Real.sqrt ((n : ℝ) + 1) ≤
      BinaryLogit.delta * Real.sqrt (n : ℝ) := by
    dsimp [yHilbertLowerConstant]
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (sqrt_depth_div_sqrt_two_le n hn) BinaryLogit.delta_pos.le
  exact (ENNReal.ofReal_le_ofReal hs).trans
    ((BinaryLogit.G_lower n).trans (ySpace_G_norm_le_hilbertConstant (𝕜 := 𝕜) n))

theorem ySpace_hilbert_sqrt_lower_real (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (yHilbertLowerConstant * Real.sqrt ((n : ℝ) + 1)) ≤
      hilbertConstant 2 (ContinuousLinearMap.id ℝ (YSpace ℝ n)) :=
  ySpace_hilbert_sqrt_lower_direct n hn

theorem ySpace_hilbert_sqrt_lower_complex (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (yHilbertLowerConstant * Real.sqrt ((n : ℝ) + 1)) ≤
      hilbertConstant 2 (ContinuousLinearMap.id ℂ (YSpace ℂ n)) :=
  ySpace_hilbert_sqrt_lower_direct n hn

/-- The interval witness and finite-dimensional L2 extension give the linear
Hilbert lower bound for the real graph space. -/
theorem xSpace_hilbert_linear_lower_real (n : ℕ) :
    ENNReal.ofReal (summationHilbertLowerConstant * ((n : ℝ) + 1)) ≤
      hilbertConstant 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) := by
  exact (summation_hilbertConstant_lower (𝕜 := ℝ) n).trans
    (hilbertConstant_matrix_le_graphSpace (summation_transferAssumptions n)
      (summation_le_l1 n) 2)

/-- Complex counterpart, with the same universal coefficient. -/
theorem xSpace_hilbert_linear_lower_complex (n : ℕ) :
    ENNReal.ofReal (summationHilbertLowerConstant * ((n : ℝ) + 1)) ≤
      hilbertConstant 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) := by
  exact (summation_hilbertConstant_lower (𝕜 := ℂ) n).trans
    (hilbertConstant_matrix_le_graphSpace (summation_transferAssumptions n)
      (summation_le_l1 n) 2)

/-- Direct finite-dyadic lower bound, with no admitted dependencies. -/
theorem xSpace_umd_sqrt_lower_real (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (xUMDLowerConstant * Real.sqrt ((n : ℝ) + 1)) ≤
      umdConstant.{0} 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) := by
  simpa only [xUMDLowerConstant, div_eq_mul_inv, one_mul, mul_comm] using
    xSpace_umdConstant_sqrt_depth_lower_direct (𝕜 := ℝ) n hn

/-- Complex counterpart, using the full unimodular UMD definition. -/
theorem xSpace_umd_sqrt_lower_complex (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (xUMDLowerConstant * Real.sqrt ((n : ℝ) + 1)) ≤
      umdConstant.{0} 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) := by
  simpa only [xUMDLowerConstant, div_eq_mul_inv, one_mul, mul_comm] using
    xSpace_umdConstant_sqrt_depth_lower_direct (𝕜 := ℂ) n hn

end HilbertUMD
