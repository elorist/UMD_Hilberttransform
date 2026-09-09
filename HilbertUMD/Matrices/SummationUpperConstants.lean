import HilbertUMD.Matrices.SummationUpper

/-! Separate real and complex summation estimates with the coefficients
proved in Lean. These differ from Remark 1.2 of the fixed paper. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace HilbertUMD

theorem cubicL1Norm_leafToLp (d n : ℕ) (f : Leaf d → Vec ℝ n) :
    CubicLp.l1Norm (leafUniform d) 2 (leafToLpLinear d 2 f) =
      Real.sqrt ((2 : ℝ)⁻¹ ^ d) * finiteL2 (l1Norm n) f := by
  change ‖(CubicLp.toL1 (ι := Leaf n)).compLpL 2 (leafUniform d) (leafToLpLinear d 2 f)‖ = _
  rw [norm_leafLp_two]
  have h := eq_of_leaf_aeEq d ((CubicLp.toL1 (ι := Leaf n)).coeFn_compLpL (leafToLpLinear d 2 f))
  rw [h, leafToLpLinear_coe, leafL2Norm_eq_finiteL2 (𝕜 := ℝ)]
  congr 1
  unfold finiteL2
  congr 1
  funext x
  exact PiLp.norm_eq_of_L1 _

theorem dyadic_tree_real_finiteL2_le (d n : ℕ) (ε : Fin d → ℝ)
    (hε : ∀ k, |ε k| ≤ 1) (f : Leaf d → Vec ℝ n) :
    finiteL2 (normSeminorm ℝ (Vec ℝ n))
      (fun x => treeMatrix (-1) (fun _ => (-1 : ℝ)) n (coordinateAction (dyadicScalar d ε) f x)) ≤
        matrixUpperConstant n 2 1097 * finiteL2 (l1Norm n) f := by
  obtain ⟨R, hR, _⟩ := dyadic_scalarMatrixData d ε hε
  have ha : ∀ (g : Leaf d → ℝ) (hp : MemLp g 2 (leafUniform d)) (hq : MemLp g 3 (leafUniform d)),
      dyadicLpScalar d 2 ε (hp.toLp g) =ᵐ[leafUniform d] R.atThree (hq.toLp g) := by
    intro g hp hq
    rw [hR]
    exact dyadicLpScalar_compatible d ε 2 3 g hp hq
  have hs : ∀ (g h : Lp ℝ 2 (leafUniform d)),
      (∫ x, dyadicLpScalar d 2 ε g x * h x ∂leafUniform d) =
        -(-1 : ℝ) * ∫ x, g x * dyadicLpScalar d 2 ε h x ∂leafUniform d := by
    intro g h
    simpa using dyadicLpScalar_integral_pairing d ε g h
  have hm := R.matrix_bound_real (leafUniform d) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => (-1 : ℝ)) (by intro k; norm_num) n (dyadicLpScalar d 2 ε) ha hs (leafToLpLinear d 2 f)
  rw [norm_leafLp_two, dyadic_matrix_action_coe, leafToLpLinear_coe,
    leafL2Norm_eq_finiteL2 (𝕜 := ℝ), cubicL1Norm_leafToLp] at hm
  apply (mul_le_mul_iff_right₀ (show 0 < Real.sqrt ((2 : ℝ)⁻¹ ^ d) by positivity)).mp
  simpa only [mul_left_comm] using hm

theorem summation_real_matrix_coefficient (n : ℕ) :
    (matrixUpperConstant n 2 1097 + 2) / 2 ≤ 284 * Real.sqrt ((n : ℝ) + 1) := by
  have hm := matrixUpperConstant_le_mul_sqrt_succ n 2 1097
  norm_num only [show (9 : ℝ) * (2 * 2 ^ 2 + 2 * 1097) = 19818 by norm_num] at hm
  have hr : Real.sqrt (19818 : ℝ) ≤ 141 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num
  have hs : 1 ≤ Real.sqrt ((n : ℝ) + 1) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simp)
  have hmul := mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg ((n : ℝ) + 1))
  nlinarith

theorem summation_umdBound_real_284 (n : ℕ) :
    UMDBound.{0} 2 (summationOperator (𝕜 := ℝ) n)
      ⟨284 * Real.sqrt ((n : ℝ) + 1), by positivity⟩ := by
  apply Interfaces.umdBound_of_finiteDyadicTerminalBound
  apply finiteDyadicTerminal_summation_of_raw
  intro d ε hε f
  have he : ∀ k, ‖ε k‖ ≤ 1 := fun k => (hε k).le
  have ht := finiteL2_summation_of_tree_bound (dyadicScalar d ε)
    (dyadicScalar_contraction_le d ε he) (matrixUpperConstant n 2 1097)
    (dyadic_tree_real_finiteL2_le d n ε he) f
  exact ht.trans (mul_le_mul_of_nonneg_right (summation_real_matrix_coefficient n) (finiteL2_nonneg _ _))

theorem summation_umdConstant_real_284 (n : ℕ) :
    umdConstant.{0} 2 (summationOperator (𝕜 := ℝ) n) ≤
      ENNReal.ofReal (284 * Real.sqrt ((n : ℝ) + 1)) := by
  let C : ℝ≥0 := ⟨284 * Real.sqrt ((n : ℝ) + 1), by positivity⟩
  change _ ≤ ENNReal.ofReal (C : ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  exact umdConstant_le (summation_umdBound_real_284 n)

theorem summation_complex_matrix_coefficient (n : ℕ) :
    (2 * matrixUpperConstant n 2 1097 + 2) / 2 ≤
      (44799 / 100 : ℝ) * Real.sqrt ((n : ℝ) + 1) := by
  have hm := matrixUpperConstant_le_mul_sqrt_succ n 2 1097
  norm_num only [show (9 : ℝ) * (2 * 2 ^ 2 + 2 * 1097) = 19818 by norm_num] at hm
  have hr : Real.sqrt (19818 : ℝ) ≤ 56311 / 400 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num
  have hs : 1 ≤ Real.sqrt ((n : ℝ) + 1) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simp)
  have hmul := mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg ((n : ℝ) + 1))
  nlinarith

theorem summation_umdBound_complex_44799 (n : ℕ) :
    UMDBound.{0} 2 (summationOperator (𝕜 := ℂ) n)
      ⟨(44799 / 100 : ℝ) * Real.sqrt ((n : ℝ) + 1), by positivity⟩ := by
  apply Interfaces.complex_umdBound_of_finiteDyadicTerminalBound
  apply finiteDyadicTerminal_summation_of_raw
  intro d ε hε f
  have he : ∀ k, ‖ε k‖ ≤ 1 := fun k => (hε k).le
  have hP : ∀ (d : ℕ) (ε : Fin d → ℝ), (∀ k, |ε k| ≤ 1) →
      ∃ R : ScalarMatrixData (leafUniform d) (-1) 2 (1097 : ℝ≥0),
        R.atThree = dyadicLpScalar d 3 ε := by
    intro d ε hε
    obtain ⟨R, hR, _⟩ := dyadic_scalarMatrixData d ε hε
    exact ⟨R, hR⟩
  have ht := finiteL2_summation_of_tree_bound (dyadicScalar d ε)
    (dyadicScalar_contraction_le d ε he) (2 * matrixUpperConstant n 2 1097)
    (dyadic_tree_complex_finiteL2_le 1097 hP d n ε he) f
  exact ht.trans (mul_le_mul_of_nonneg_right (summation_complex_matrix_coefficient n)
    (finiteL2_nonneg _ _))

theorem summation_umdConstant_complex_44799 (n : ℕ) :
    umdConstant.{0} 2 (summationOperator (𝕜 := ℂ) n) ≤
      ENNReal.ofReal ((44799 / 100 : ℝ) * Real.sqrt ((n : ℝ) + 1)) := by
  let C : ℝ≥0 := ⟨(44799 / 100 : ℝ) * Real.sqrt ((n : ℝ) + 1), by positivity⟩
  change _ ≤ ENNReal.ofReal (C : ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  exact umdConstant_le (summation_umdBound_complex_44799 n)

end HilbertUMD
