import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# The cubic estimate: positive testing

This module proves the positive-testing step of manuscript Lemma 3.2.
Mixed-norm duality, endpoint realization compatibility and interpolation are
separate steps; the full cubic lemma is not asserted here.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace HilbertUMD

theorem weighted_square_domination {f g a b : ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    g * (a - b) ^ 2 ≤ 2 * (f + g) * a ^ 2 + 2 * g * b ^ 2 := by
  nlinarith [mul_nonneg hg (sq_nonneg (a + b)), mul_nonneg hf (sq_nonneg a)]

/-- Weighted testing with f + g/3 halves the cubic testing constant. -/
theorem weighted_square_domination_nine {f g a b : ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    g * (a - b / 3) ^ 2 ≤ (27 / 8 : ℝ) * (f + g / 3) * a ^ 2 + g * b ^ 2 := by
  have hy : (a - b / 3) ^ 2 ≤ (9 / 8 : ℝ) * a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (3 * a + 8 * b)]
  have h := mul_le_mul_of_nonneg_left hy hg
  nlinarith [mul_nonneg hf (sq_nonneg a)]

section Energy

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S)

/-- Hölder gives the integrability of each cubic summand at exponent three. -/
theorem integrable_mul_square_of_memLp_three {f v : S → ℝ}
    (hf : MemLp f 3 μ) (hv : MemLp v 3 μ) : Integrable (fun x => f x * (v x) ^ 2) μ := by
  have : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2) := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by simp)).mp
    norm_num [ENNReal.toReal_add]⟩
  have : ENNReal.HolderTriple (3 : ℝ≥0∞) (3 / 2) 1 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by norm_num)).mp
    norm_num [ENNReal.toReal_add]⟩
  have hvv : MemLp (v * v) (3 / 2) μ := hv.mul hv
  simp only [pow_two]
  change Integrable (f * (v * v)) μ
  exact hf.integrable_mul hvv

theorem integrable_weighted_square_of_memLp_three {f v : S → ι → ℝ}
    (hf : ∀ i, MemLp (fun x => f x i) 3 μ)
    (hv : ∀ i, MemLp (fun x => v x i) 3 μ) :
    Integrable (fun x => ∑ i, f x i * (v x i) ^ 2) μ := by
  exact integrable_finsetSum _ fun i _ => integrable_mul_square_of_memLp_three μ (hf i) (hv i)

def weightedSquareIntegral (f v : S → ι → ℝ) : ℝ :=
  ∫ x, ∑ i, f x i * (v x i) ^ 2 ∂μ

end Energy

end HilbertUMD
