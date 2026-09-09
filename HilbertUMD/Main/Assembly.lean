import HilbertUMD.Main.Statement
import HilbertUMD.Main.LowerBounds
import HilbertUMD.Main.Transfer
import HilbertUMD.UMD.RealComplexSpaces

/-! Choose common positive comparison constants and assemble the eight
inequalities from the lower bounds and the two sharp graph upper bounds. -/

noncomputable section
open scoped ENNReal
namespace HilbertUMD

def mainLowerConstant : ℝ := min summationHilbertLowerConstant
  (min xUMDLowerConstant (min yHilbertLowerConstant (1/3)))

theorem mainLowerConstant_pos : 0 < mainLowerConstant := by
  apply lt_min summationHilbertLowerConstant_pos
  exact lt_min xUMDLowerConstant_pos (lt_min yHilbertLowerConstant_pos (by norm_num))

theorem mainLowerConstant_le_hilbert : mainLowerConstant ≤ summationHilbertLowerConstant :=
  min_le_left _ _

theorem mainLowerConstant_le_umd : mainLowerConstant ≤ xUMDLowerConstant :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem mainLowerConstant_le_yHilbert : mainLowerConstant ≤ yHilbertLowerConstant :=
  ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)

theorem mainLowerConstant_le_yUMD : mainLowerConstant ≤ 1/3 :=
  ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)

theorem linear_level_upper (n : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    (n : ℝ≥0∞)+1 ≤ ENNReal.ofReal (C * ((n : ℝ)+1)) := by
  have he : ENNReal.ofReal ((n : ℝ)+1) = (n : ℝ≥0∞)+1 := by
    simp only [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ)≤1),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [← he]
  exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (by positivity) hC)

theorem assemble_p2_bounds (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) (hn : 1 ≤ n)
    [NormedSpace ℝ (XSpace 𝕜 n)] [NormedSpace ℝ (YSpace 𝕜 n)] (C : ℝ) (hC : 1 ≤ C)
    (hxHL : ENNReal.ofReal (summationHilbertLowerConstant * ((n : ℝ)+1)) ≤
      hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)))
    (hxHU : hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) ≤ (n : ℝ≥0∞)+1)
    (hxUL : ENNReal.ofReal (xUMDLowerConstant * Real.sqrt ((n : ℝ)+1)) ≤
      umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)))
    (hxUU : umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) ≤ ENNReal.ofReal (C * Real.sqrt ((n : ℝ)+1)))
    (hyUL : ENNReal.ofReal (2 * (n : ℝ) / 3) ≤ umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)))
    (hyUU : umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ≤ (n : ℝ≥0∞)+1)
    (hyHL : ENNReal.ofReal (yHilbertLowerConstant * Real.sqrt ((n : ℝ)+1)) ≤
      hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)))
    (hyHU : hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ≤ ENNReal.ofReal (C * Real.sqrt ((n : ℝ)+1))) :
    P2MainBounds 𝕜 n mainLowerConstant C where
  x_hilbert_lower := (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right mainLowerConstant_le_hilbert (by positivity))).trans hxHL
  x_hilbert_upper := hxHU.trans (linear_level_upper n C hC)
  x_umd_lower := (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right mainLowerConstant_le_umd (Real.sqrt_nonneg _))).trans hxUL
  x_umd_upper := hxUU
  y_umd_lower := (ENNReal.ofReal_le_ofReal (by
    have h := mul_le_mul_of_nonneg_right mainLowerConstant_le_yUMD
      (show 0 ≤ (n : ℝ)+1 by positivity)
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)).trans hyUL
  y_umd_upper := hyUU.trans (linear_level_upper n C hC)
  y_hilbert_lower := (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right mainLowerConstant_le_yHilbert (Real.sqrt_nonneg _))).trans hyHL
  y_hilbert_upper := hyHU

/-- Intermediate real assembly, with exactly the two sharp graph upper
bounds displayed. The six other inequalities are already supplied. -/
theorem p2_main_real_of_upper_bounds (n : ℕ) (hn : 1 ≤ n) (C : ℝ) (hC : 1 ≤ C)
    (hX : umdConstant.{0} 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) ≤
      ENNReal.ofReal (C * Real.sqrt ((n : ℝ)+1)))
    (hY : hilbertConstant 2 (ContinuousLinearMap.id ℝ (YSpace ℝ n)) ≤
      ENNReal.ofReal (C * Real.sqrt ((n : ℝ)+1))) : P2MainBounds ℝ n mainLowerConstant C :=
  assemble_p2_bounds ℝ n hn C hC (xSpace_hilbert_linear_lower_real n)
    (xSpace_hilbert_linear_upper_real n) (xSpace_umd_sqrt_lower_real n hn) hX
    (ySpace_umd_bounds_real n).1 (ySpace_umd_bounds_real n).2
    (ySpace_hilbert_sqrt_lower_real n hn) hY

/-- Intermediate complex assembly for the full unimodular UMD definition. -/
theorem p2_main_complex_of_upper_bounds (n : ℕ) (hn : 1 ≤ n) (C : ℝ) (hC : 1 ≤ C)
    (hX : umdConstant.{0} 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) ≤
      ENNReal.ofReal (C * Real.sqrt ((n : ℝ)+1)))
    (hY : hilbertConstant 2 (ContinuousLinearMap.id ℂ (YSpace ℂ n)) ≤
      ENNReal.ofReal (C * Real.sqrt ((n : ℝ)+1))) : P2MainBounds ℂ n mainLowerConstant C :=
  assemble_p2_bounds ℂ n hn C hC (xSpace_hilbert_linear_lower_complex n)
    (xSpace_hilbert_linear_upper_complex n) (xSpace_umd_sqrt_lower_complex n hn) hX
    (ySpace_umd_bounds_complex n).1 (ySpace_umd_bounds_complex n).2
    (ySpace_hilbert_sqrt_lower_complex n hn) hY

/-- Assemble the full theorem from the complex summation bound and the
real/complex signed-dyadic bounds. Restriction supplies the real UMD bound. -/
theorem p2_main_of_uniform_matrix_bounds (AC B : ℝ)
    (hAC : 0 ≤ AC) (hB : 0 ≤ B)
    (hXC : ∀ n, umdConstant.{0} 2 (summationOperator (𝕜 := ℂ) n) ≤
      ENNReal.ofReal (AC * Real.sqrt ((n : ℝ)+1)))
    (hYR : ∀ n, hilbertConstant 2 (signedDyadicOperator (𝕜 := ℝ) n) ≤
      ENNReal.ofReal (B * Real.sqrt ((n : ℝ)+1)))
    (hYC : ∀ n, hilbertConstant 2 (signedDyadicOperator (𝕜 := ℂ) n) ≤
      ENNReal.ofReal (B * Real.sqrt ((n : ℝ)+1))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      P2MainBounds ℝ n c C ∧ P2MainBounds ℂ n c C := by
  let C := 1 + Real.sqrt (AC^2+2) + Real.sqrt (B^2+2)
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [Real.sqrt_nonneg (AC^2+2), Real.sqrt_nonneg (B^2+2)]
  have hCC : Real.sqrt (AC^2+2) ≤ C := by
    dsimp [C]
    linarith [Real.sqrt_nonneg (B^2+2)]
  have hCB : Real.sqrt (B^2+2) ≤ C := by
    dsimp [C]
    linarith [Real.sqrt_nonneg (AC^2+2)]
  refine ⟨mainLowerConstant, C, mainLowerConstant_pos, lt_of_lt_of_le (by norm_num) hC, ?_⟩
  intro n hn
  constructor
  · apply p2_main_real_of_upper_bounds n hn C hC
    · exact (umdConstant_xSpace_real_le_complex n).trans
        ((xSpace_umd_sqrt_upper_of_matrix_complex n AC hAC (hXC n)).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _))))
    · exact (ySpace_hilbert_sqrt_upper_of_matrix_real n B hB (hYR n)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCB (Real.sqrt_nonneg _)))
  · apply p2_main_complex_of_upper_bounds n hn C hC
    · exact (xSpace_umd_sqrt_upper_of_matrix_complex n AC hAC (hXC n)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _)))
    · exact (ySpace_hilbert_sqrt_upper_of_matrix_complex n B hB (hYC n)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCB (Real.sqrt_nonneg _)))

end HilbertUMD
