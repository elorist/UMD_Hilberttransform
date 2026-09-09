import HilbertUMD.LowerBounds.BinaryLogitDefs

/-! Integrability and exact elementary logarithmic integrals for the witness. -/

noncomputable section
open MeasureTheory Set intervalIntegral
open scoped ENNReal

namespace HilbertUMD.BinaryLogit

theorem g_eq_sub_logs_all (t : ℝ) :
    g t = Real.pi⁻¹ * (Real.log t - Real.log (1 - t)) := by
  by_cases h0 : t = 0
  · simp [h0, g]
  by_cases h1 : t = 1
  · simp [h1, g]
  rw [g, Real.log_div h0 (sub_ne_zero.mpr (Ne.symm h1))]

theorem intervalIntegrable_g (a b : ℝ) : IntervalIntegrable g volume a b := by
  have hsub : IntervalIntegrable (fun t : ℝ => Real.log (1 - t)) volume a b := by
    simpa only [sub_sub_cancel] using
      (intervalIntegrable_log' (a := 1 - a) (b := 1 - b)).comp_sub_left 1
  simpa only [← g_eq_sub_logs_all] using
    (intervalIntegrable_log'.sub hsub).const_mul Real.pi⁻¹

theorem integrable_g : Integrable g unitMeasure :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (intervalIntegrable_g 0 1)

def primitive (t : ℝ) : ℝ := Real.pi⁻¹ *
  (t * Real.log t + (1 - t) * Real.log (1 - t))

theorem integral_g (a b : ℝ) : ∫ t in a..b, g t = primitive b - primitive a := by
  simp_rw [g_eq_sub_logs_all]
  rw [intervalIntegral.integral_const_mul]
  have hsub : IntervalIntegrable (fun t : ℝ => Real.log (1 - t)) volume a b := by
    simpa only [sub_sub_cancel] using
      (intervalIntegrable_log' (a := 1 - a) (b := 1 - b)).comp_sub_left 1
  rw [intervalIntegral.integral_sub intervalIntegrable_log' hsub,
    intervalIntegral.integral_comp_sub_left, integral_log, integral_log]
  simp only [primitive]
  ring

@[simp] theorem primitive_zero : primitive 0 = 0 := by simp [primitive]
@[simp] theorem primitive_one : primitive 1 = 0 := by simp [primitive]

theorem primitive_half : primitive (1 / 2) = -Real.pi⁻¹ * Real.log 2 := by
  norm_num [primitive, Real.log_div]
  ring

theorem primitive_quarter :
    primitive (1 / 4) = Real.pi⁻¹ * ((3 / 4) * Real.log 3 - Real.log 4) := by
  norm_num [primitive, Real.log_div]
  ring

theorem primitive_one_sub (t : ℝ) : primitive (1 - t) = primitive t := by
  simp only [primitive, sub_sub_cancel]
  ring

theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  exact h

theorem first_coefficient :
    (∫ t in (1 / 2 : ℝ)..1, g t) - (∫ t in (0 : ℝ)..(1 / 2), g t) =
      2 * Real.log 2 / Real.pi := by
  rw [integral_g, integral_g, primitive_zero, primitive_one, primitive_half]
  ring

theorem second_coefficient :
    (∫ t in (1 / 4 : ℝ)..(1 / 2), g t) - (∫ t in (0 : ℝ)..(1 / 4), g t) +
      ((∫ t in (3 / 4 : ℝ)..1, g t) - (∫ t in (1 / 2 : ℝ)..(3 / 4), g t)) =
      3 * Real.log (4 / 3) / Real.pi := by
  simp only [integral_g, primitive_zero, primitive_one]
  rw [show (3 / 4 : ℝ) = 1 - 1 / 4 by norm_num, primitive_one_sub,
    primitive_half, primitive_quarter, Real.log_div (by norm_num) (by norm_num), log_four]
  ring

end HilbertUMD.BinaryLogit
