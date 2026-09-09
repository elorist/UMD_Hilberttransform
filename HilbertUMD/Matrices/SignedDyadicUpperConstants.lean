import HilbertUMD.Matrices.SignedDyadicUpper
import HilbertUMD.Hilbert.HilbertMatrixDataSharp

/-! The Hilbert matrix bound uses the complex cubic estimate directly,
preserving its constant when the diagonal term is added. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD
namespace SignedHilbert

theorem amplification_complexify {n : ℕ} (f : CubicLp.ComplexSpace (ι := Leaf n) volume 2) :
    L2Transfer.amplification volume hilbertL2.toContinuousLinearMap f =
      CubicLp.complexify volume (L2Transfer.amplification volume realHilbertL2CLM) f := by
  conv_lhs => rw [← complex_reconstruction f]
  rw [map_add, map_smul, amplification_ofRealLp, amplification_ofRealLp]
  rfl

theorem action_complex_eq_tree_add (n : ℕ) (f : CubicLp.ComplexSpace (ι := Leaf n) volume 2) :
    action n hilbertL2.toContinuousLinearMap f =
      CubicLp.complexify volume
        (MatrixCompatible.action volume 1 (fun k => (-1 : ℝ)^k) n 2 realHilbertL2CLM) f +
          L2Transfer.amplification volume hilbertL2.toContinuousLinearMap f := by
  rw [action_complexify, amplification_complexify]
  simp only [CubicLp.complexify_apply, CubicLp.complexifyReal_apply,
    action_eq_tree_add, map_add, smul_add]
  abel

theorem sharp_matrix_coefficient (n : ℕ) :
    matrixUpperConstant n (11 / 4) 9 + Real.sqrt ((n : ℝ) + 1) ≤
      56 * Real.sqrt ((n : ℝ) + 1) := by
  have hm := matrixUpperConstant_le_mul_sqrt_succ n (11 / 4) 9
  norm_num only [show (9 : ℝ) * (2 * (11 / 4) ^ 2 + 2 * 9) = 2385 / 8 by norm_num] at hm
  have hr : Real.sqrt (2385 / 8 : ℝ) ≤ 173 / 10 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num
  have hmul := mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg ((n : ℝ) + 1))
  nlinarith [Real.sqrt_nonneg ((n : ℝ) + 1)]

theorem action_complex_bound_56 (n : ℕ) (f : CubicLp.ComplexSpace (ι := Leaf n) volume 2) :
    ‖action n hilbertL2.toContinuousLinearMap f‖ ≤
      (56 * Real.sqrt ((n : ℝ) + 1)) * CubicLp.complexL1Norm volume 2 f := by
  have htree := ScalarMatrixData.matrix_bound_complex volume hilbertMatrixDataSharp
    (by norm_num) (by norm_num) (by norm_num) (fun k => (-1 : ℝ)^k)
    (fun k => by rw [← pow_mul, Nat.mul_comm k 2, pow_mul]; norm_num) n realHilbertL2CLM
    (fun f h2 h3 => (realHilbertThree_agrees_two f h2 h3).symm)
    (fun f g => by simpa [realHilbertL2] using realHilbertL2_integral_skew f g) f
  have hdiag := L2Transfer.amplification_norm_le_sqrt hilbertL2.toContinuousLinearMap
    (fun z => (hilbertL2.norm_map z).le) f
  have heq : L2Transfer.fibreNorm volume (L2Transfer.toL1 (𝕜 := ℂ) (n := n)) f =
      CubicLp.complexL1Norm volume 2 f := rfl
  rw [heq] at hdiag
  rw [action_complex_eq_tree_add]
  apply (norm_add_le _ _).trans
  have hc := mul_le_mul_of_nonneg_right (sharp_matrix_coefficient n)
    (apply_nonneg (CubicLp.complexL1Norm volume 2) f)
  nlinarith

theorem action_real_bound_56 (n : ℕ) (f : CubicLp.Space (ι := Leaf n) volume 2) :
    ‖action n realHilbertL2CLM f‖ ≤
      (56 * Real.sqrt ((n : ℝ) + 1)) * CubicLp.l1Norm volume 2 f := by
  have h := action_complex_bound_56 n (CubicLp.ofRealLp volume 2 f)
  simpa only [action_ofRealLp, CubicLp.norm_ofRealLp, CubicLp.complexL1Norm_ofRealLp] using h

end SignedHilbert

theorem signedDyadic_hilbertBound_real_56 (n : ℕ) :
    HilbertBound 2 (signedDyadicOperator (𝕜 := ℝ) n)
      ⟨56 * Real.sqrt ((n : ℝ) + 1), by positivity⟩ := by
  have hpv : L2Transfer.ScalarPV realHilbertL2CLM := Interfaces.real_scalar_pv_fourier
  apply hpv.hilbertBound_of_mixed (signedDyadic_le_l1 n)
  exact SignedHilbert.action_real_bound_56 n

theorem signedDyadic_hilbertBound_complex_56 (n : ℕ) :
    HilbertBound 2 (signedDyadicOperator (𝕜 := ℂ) n)
      ⟨56 * Real.sqrt ((n : ℝ) + 1), by positivity⟩ := by
  have hpv : L2Transfer.ScalarPV hilbertL2.toContinuousLinearMap := Interfaces.complex_scalar_pv_fourier
  apply hpv.hilbertBound_of_mixed (signedDyadic_le_l1 n)
  exact SignedHilbert.action_complex_bound_56 n

theorem signedDyadic_hilbertConstant_real_56 (n : ℕ) :
    hilbertConstant 2 (signedDyadicOperator (𝕜 := ℝ) n) ≤
      ENNReal.ofReal (56 * Real.sqrt ((n : ℝ) + 1)) := by
  let C : ℝ≥0 := ⟨56 * Real.sqrt ((n : ℝ) + 1), by positivity⟩
  change _ ≤ ENNReal.ofReal (C : ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  exact hilbertConstant_le (signedDyadic_hilbertBound_real_56 n)

theorem signedDyadic_hilbertConstant_complex_56 (n : ℕ) :
    hilbertConstant 2 (signedDyadicOperator (𝕜 := ℂ) n) ≤
      ENNReal.ofReal (56 * Real.sqrt ((n : ℝ) + 1)) := by
  let C : ℝ≥0 := ⟨56 * Real.sqrt ((n : ℝ) + 1), by positivity⟩
  change _ ≤ ENNReal.ofReal (C : ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  exact hilbertConstant_le (signedDyadic_hilbertBound_complex_56 n)

end HilbertUMD
