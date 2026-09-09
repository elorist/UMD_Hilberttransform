import HilbertUMD.Matrices.MatrixEnergyCompatible
import HilbertUMD.Analysis.CubicConclusion

/-! The common matrix L² upper estimate follows from the energy bound and
the cubic lemma, including its proved duality and interpolation inputs.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD

def matrixUpperConstant (n : ℕ) (M P : ℝ) : ℝ :=
  (127 / 40) * Real.sqrt (9 * ((n : ℝ) * (2 * M ^ 2 + 2 * P)))

theorem matrixUpperConstant_nonneg (n : ℕ) (M P : ℝ) : 0 ≤ matrixUpperConstant n M P := by
  unfold matrixUpperConstant
  positivity

theorem matrixUpperConstant_eq_mul_sqrt (n : ℕ) (M P : ℝ) :
    matrixUpperConstant n M P = ((127 / 40) * Real.sqrt (9 * (2 * M ^ 2 + 2 * P))) * Real.sqrt n := by
  unfold matrixUpperConstant
  rw [show 9 * ((n : ℝ) * (2 * M ^ 2 + 2 * P)) =
    (n : ℝ) * (9 * (2 * M ^ 2 + 2 * P)) by ring,
    Real.sqrt_mul (Nat.cast_nonneg n)]
  ring

theorem matrixUpperConstant_le_mul_sqrt_succ (n : ℕ) (M P : ℝ) :
    matrixUpperConstant n M P ≤
      ((127 / 40) * Real.sqrt (9 * (2 * M ^ 2 + 2 * P))) * Real.sqrt ((n : ℝ) + 1) := by
  rw [matrixUpperConstant_eq_mul_sqrt]
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith))
  positivity

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [SigmaFinite μ]
  {η M P : ℝ}

/-- The common matrix estimate over the reals, on the actual given L² realization. -/
theorem ScalarMatrixData.matrix_bound_real
    (R : ScalarMatrixData μ η M P) (hη : η ^ 2 = 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (c : ℕ → ℝ) (hc : ∀ k, c k ^ 2 = 1) (n : ℕ)
    (Rtwo : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hAgree : ∀ (f : S → ℝ) (hp : MemLp f 2 μ) (hq : MemLp f 3 μ),
      Rtwo (hp.toLp f) =ᵐ[μ] R.atThree (hq.toLp f))
    (hSkew : ∀ (f g : Lp ℝ 2 μ), (∫ x, Rtwo f x * g x ∂μ) =
      (-η) * ∫ x, f x * Rtwo g x ∂μ)
    (f : CubicLp.Space (ι := Leaf n) μ 2) :
    ‖MatrixCompatible.action μ η c n 2 Rtwo f‖ ≤
      matrixUpperConstant n M P * CubicLp.l1Norm μ 2 f :=
  CubicLp.cubic_two_real μ (MatrixCompatible.compatible μ η c n hη Rtwo R.atThree hAgree hSkew)
    ((n : ℝ) * (2 * M ^ 2 + 2 * P)) (by positivity)
    (ScalarMatrixData.action_energy_bound μ R hη hM hP c hc n) f

/-- The same bound for the actual complex-linear complexification. -/
theorem ScalarMatrixData.matrix_bound_complex
    (R : ScalarMatrixData μ η M P) (hη : η ^ 2 = 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (c : ℕ → ℝ) (hc : ∀ k, c k ^ 2 = 1) (n : ℕ)
    (Rtwo : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hAgree : ∀ (f : S → ℝ) (hp : MemLp f 2 μ) (hq : MemLp f 3 μ),
      Rtwo (hp.toLp f) =ᵐ[μ] R.atThree (hq.toLp f))
    (hSkew : ∀ (f g : Lp ℝ 2 μ), (∫ x, Rtwo f x * g x ∂μ) =
      (-η) * ∫ x, f x * Rtwo g x ∂μ)
    (f : CubicLp.ComplexSpace (ι := Leaf n) μ 2) :
    ‖CubicLp.complexify μ (MatrixCompatible.action μ η c n 2 Rtwo) f‖ ≤
      matrixUpperConstant n M P * CubicLp.complexL1Norm μ 2 f :=
  CubicLp.cubic_two_complex μ (MatrixCompatible.compatible μ η c n hη Rtwo R.atThree hAgree hSkew)
    ((n : ℝ) * (2 * M ^ 2 + 2 * P)) (by positivity)
    (ScalarMatrixData.action_energy_bound μ R hη hM hP c hc n) f

end HilbertUMD
