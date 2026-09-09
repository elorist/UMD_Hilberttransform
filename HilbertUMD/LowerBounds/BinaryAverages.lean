import HilbertUMD.LowerBounds.BinaryLogitDefs

/-! Binary transfer averages and monotonicity of Rademacher coefficients. -/

noncomputable section
open MeasureTheory Set intervalIntegral

namespace HilbertUMD.BinaryLogit

def average (h : ℝ → ℝ) (t : ℝ) : ℝ := (h (t / 2) + h ((t + 1) / 2)) / 2

def sign (t : ℝ) : ℝ := if t < 1 / 2 then -1 else 1

def coefficient (h : ℝ → ℝ) : ℝ :=
  (∫ t in (1 / 2 : ℝ)..1, h t) - (∫ t in (0 : ℝ)..(1 / 2), h t)

def AllIntervalIntegrable (h : ℝ → ℝ) : Prop := ∀ a b, IntervalIntegrable h volume a b

theorem AllIntervalIntegrable.add_right {h : ℝ → ℝ} (hh : AllIntervalIntegrable h)
    (c : ℝ) : AllIntervalIntegrable (fun t => h (t + c)) := by
  intro a b
  simpa using (hh (a + c) (b + c)).comp_add_right c

theorem AllIntervalIntegrable.half {h : ℝ → ℝ} (hh : AllIntervalIntegrable h) :
    AllIntervalIntegrable (fun t => h (t / 2)) := by
  intro a b
  convert (hh (a / 2) (b / 2)).comp_mul_left (c := 1 / 2) using 1 <;>
    simp [div_eq_mul_inv, mul_comm]

theorem AllIntervalIntegrable.average {h : ℝ → ℝ} (hh : AllIntervalIntegrable h) :
    AllIntervalIntegrable (average h) := by
  intro a b
  exact ((hh.half a b).add (hh.half.add_right 1 a b)).div_const 2

theorem monotoneOn_average {h : ℝ → ℝ} (hh : MonotoneOn h (Ioo (0 : ℝ) 1)) :
    MonotoneOn (average h) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  dsimp [average]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply add_le_add
  · exact hh ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)
  · exact hh ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)

theorem integral_average {h : ℝ → ℝ} (hh : AllIntervalIntegrable h) (a b : ℝ) :
    (∫ t in a..b, average h t) =
      (∫ t in a / 2..b / 2, h t) + (∫ t in (a + 1) / 2..(b + 1) / 2, h t) := by
  simp only [average]
  change (∫ t in a..b, (h (t / 2) + h ((t + 1) / 2)) * (2 : ℝ)⁻¹) = _
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add (hh.half a b) (hh.half.add_right 1 a b),
    intervalIntegral.integral_comp_add_right (fun t => h (t / 2)) 1,
    intervalIntegral.integral_comp_div h (by norm_num : (2 : ℝ) ≠ 0),
    intervalIntegral.integral_comp_div h (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [smul_eq_mul]
  ring

theorem coefficient_sub_average {h : ℝ → ℝ} (hh : AllIntervalIntegrable h) :
    coefficient h - coefficient (average h) =
      2 * ((∫ t in (1 / 2 : ℝ)..(3 / 4), h t) - (∫ t in (1 / 4 : ℝ)..(1 / 2), h t)) := by
  have hl := intervalIntegral.integral_add_adjacent_intervals (hh 0 (1 / 4)) (hh (1 / 4) (1 / 2))
  have hr := intervalIntegral.integral_add_adjacent_intervals (hh (1 / 2) (3 / 4)) (hh (3 / 4) 1)
  simp only [coefficient, integral_average hh]
  norm_num
  linarith

theorem coefficient_nonneg {h : ℝ → ℝ} (hh : AllIntervalIntegrable h)
    (hm : MonotoneOn h (Ioo (0 : ℝ) 1)) : 0 ≤ coefficient h := by
  have he : (∫ t in (0 : ℝ)..(1 / 2), h (t + 1 / 2)) = ∫ t in (1 / 2 : ℝ)..1, h t := by
    convert intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1 / 2) h (1 / 2) using 1
    norm_num
  apply sub_nonneg.mpr
  change (∫ t in (0 : ℝ)..(1 / 2), h t) ≤ ∫ t in (1 / 2 : ℝ)..1, h t
  rw [← he]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) (hh _ _) (hh.add_right _ _ _)
  intro t ht
  exact hm ⟨ht.1, by linarith [ht.2]⟩
    ⟨by linarith [ht.1], by linarith [ht.2]⟩ (by norm_num)

theorem coefficient_average_le {h : ℝ → ℝ} (hh : AllIntervalIntegrable h)
    (hm : MonotoneOn h (Ioo (0 : ℝ) 1)) : coefficient (average h) ≤ coefficient h := by
  have he : (∫ t in (1 / 4 : ℝ)..(1 / 2), h (t + 1 / 4)) =
      ∫ t in (1 / 2 : ℝ)..(3 / 4), h t := by
    convert intervalIntegral.integral_comp_add_right (a := (1 / 4 : ℝ)) (b := 1 / 2) h (1 / 4) using 1
    norm_num
  have hm' : (∫ t in (1 / 4 : ℝ)..(1 / 2), h t) ≤ ∫ t in (1 / 2 : ℝ)..(3 / 4), h t := by
    rw [← he]
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) (hh _ _) (hh.add_right _ _ _)
    intro t ht
    exact hm ⟨by linarith [ht.1], by linarith [ht.2]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ (by norm_num)
  have hid := coefficient_sub_average hh
  linarith

end HilbertUMD.BinaryLogit
