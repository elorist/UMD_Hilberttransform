import HilbertUMD.LowerBounds.BinaryAverages
import HilbertUMD.LowerBounds.BinaryLogitIntegrals
import HilbertUMD.LowerBounds.BinaryLogitArithmetic

/-! The nonnegative decreasing scalar Rademacher coefficients of the logit. -/

noncomputable section
open MeasureTheory Set intervalIntegral

namespace HilbertUMD.BinaryLogit

def averaged : ℕ → ℝ → ℝ
  | 0 => g
  | n + 1 => average (averaged n)

def a (j : ℕ) : ℝ := coefficient (averaged j)

theorem averaged_intervalIntegrable (j : ℕ) : AllIntervalIntegrable (averaged j) := by
  induction j with
  | zero => exact intervalIntegrable_g
  | succ j ih => exact ih.average

theorem averaged_monotone (j : ℕ) : MonotoneOn (averaged j) (Ioo (0 : ℝ) 1) := by
  induction j with
  | zero => exact monotoneOn_g
  | succ j ih => exact monotoneOn_average ih

theorem a_nonneg (j : ℕ) : 0 ≤ a j :=
  coefficient_nonneg (averaged_intervalIntegrable j) (averaged_monotone j)

theorem a_antitone : Antitone a := by
  apply antitone_nat_of_succ_le
  intro j
  exact coefficient_average_le (averaged_intervalIntegrable j) (averaged_monotone j)

theorem a_zero : a 0 = first := first_coefficient

theorem a_one : a 1 = second := by
  change coefficient (average g) = second
  simp only [coefficient, integral_average intervalIntegrable_g]
  norm_num
  have h := second_coefficient
  change _ = 3 * Real.log (4 / 3) / Real.pi
  linarith

theorem a_alternating_lower (j : ℕ) : delta ≤ alternatingCoefficient a j :=
  delta_le_alternatingCoefficient a a_antitone a_nonneg a_zero a_one j

end HilbertUMD.BinaryLogit
