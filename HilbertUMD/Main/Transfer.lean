import HilbertUMD.UMD.SharpUMDTransfer
import HilbertUMD.Hilbert.SharpHilbertTransfer

/-! Checked numerical transfer of square-root matrix bounds to graph spaces. -/

noncomputable section
open scoped ENNReal
namespace HilbertUMD

/-- The extended-real square-root transfer also handles infinite constants
correctly: the assumed finite matrix bound forces the graph constant finite. -/
theorem ennreal_sharp_sqrt_transfer (x y : ℝ≥0∞) (A d : ℝ)
    (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hxy : x^2 ≤ y^2 + 2 * ENNReal.ofReal d)
    (hy : y ≤ ENNReal.ofReal (A * Real.sqrt d)) :
    x ≤ ENNReal.ofReal (Real.sqrt (A^2 + 2) * Real.sqrt d) := by
  have hs : x^2 ≤ ENNReal.ofReal ((A^2 + 2) * d) := by
    calc
      _ ≤ y^2 + 2 * ENNReal.ofReal d := hxy
      _ ≤ (ENNReal.ofReal (A * Real.sqrt d))^2 + 2 * ENNReal.ofReal d :=
        add_le_add (pow_le_pow_left' hy 2) le_rfl
      _ = ENNReal.ofReal ((A * Real.sqrt d)^2 + 2*d) := by
        rw [ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (by norm_num) hd),
          ENNReal.ofReal_pow (mul_nonneg hA (Real.sqrt_nonneg d)), ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
        norm_num
      _ = _ := by congr 1; rw [mul_pow, Real.sq_sqrt hd]; ring
  have hx : x ≠ ∞ := by intro hx; simp [hx] at hs
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at hreal
  have hroot : (Real.sqrt (A^2+2) * Real.sqrt d)^2 = (A^2+2)*d := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hd]
  have hnonneg : 0 ≤ Real.sqrt (A^2+2) * Real.sqrt d := by positivity
  calc
    x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [ENNReal.toReal_nonneg (a := x)])

theorem xSpace_umd_sqrt_upper_of_matrix_complex (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (h : umdConstant.{0} 2 (summationOperator (𝕜 := ℂ) n) ≤
      ENNReal.ofReal (A * Real.sqrt ((n : ℝ)+1))) :
    umdConstant.{0} 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) ≤
      ENNReal.ofReal (Real.sqrt (A^2+2) * Real.sqrt ((n : ℝ)+1)) := by
  apply ennreal_sharp_sqrt_transfer _ _ A ((n : ℝ)+1) hA (by positivity) _ h
  simpa only [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ)≤1),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, XSpace, summationOperator] using
    umdConstant_sharp_graph_complex (summation_transferAssumptions n) (summation_le_l1 n)

theorem xSpace_umd_sqrt_upper_of_matrix_real (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (h : umdConstant.{0} 2 (summationOperator (𝕜 := ℝ) n) ≤
      ENNReal.ofReal (A * Real.sqrt ((n : ℝ)+1))) :
    umdConstant.{0} 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) ≤
      ENNReal.ofReal (Real.sqrt (A^2+2) * Real.sqrt ((n : ℝ)+1)) := by
  apply ennreal_sharp_sqrt_transfer _ _ A ((n : ℝ)+1) hA (by positivity) _ h
  simpa only [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ)≤1),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, XSpace, summationOperator] using
    umdConstant_sharp_graph (summation_transferAssumptions (𝕜 := ℝ) n) (summation_le_l1 n)

theorem ySpace_hilbert_sqrt_upper_of_matrix_real (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (h : hilbertConstant 2 (signedDyadicOperator (𝕜 := ℝ) n) ≤
      ENNReal.ofReal (A * Real.sqrt ((n : ℝ)+1))) :
    hilbertConstant 2 (ContinuousLinearMap.id ℝ (YSpace ℝ n)) ≤
      ENNReal.ofReal (Real.sqrt (A^2+2) * Real.sqrt ((n : ℝ)+1)) := by
  apply ennreal_sharp_sqrt_transfer _ _ A ((n : ℝ)+1) hA (by positivity) _ h
  simpa only [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ)≤1),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, YSpace, signedDyadicOperator] using
    hilbertConstant_sharp_graph_real (signedDyadic_transferAssumptions n) (signedDyadic_le_l1 n)

theorem ySpace_hilbert_sqrt_upper_of_matrix_complex (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (h : hilbertConstant 2 (signedDyadicOperator (𝕜 := ℂ) n) ≤
      ENNReal.ofReal (A * Real.sqrt ((n : ℝ)+1))) :
    hilbertConstant 2 (ContinuousLinearMap.id ℂ (YSpace ℂ n)) ≤
      ENNReal.ofReal (Real.sqrt (A^2+2) * Real.sqrt ((n : ℝ)+1)) := by
  apply ennreal_sharp_sqrt_transfer _ _ A ((n : ℝ)+1) hA (by positivity) _ h
  simpa only [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ)≤1),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, YSpace, signedDyadicOperator] using
    hilbertConstant_sharp_graph_complex (signedDyadic_transferAssumptions n) (signedDyadic_le_l1 n)

end HilbertUMD
