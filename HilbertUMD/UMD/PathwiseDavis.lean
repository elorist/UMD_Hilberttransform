import HilbertUMD.Analysis.MixedNorm

/-! A pathwise Davis inequality with an explicit bounded predictable coefficient. -/

noncomputable section
open scoped BigOperators
namespace HilbertUMD

private theorem davis_step_algebra (x s d r t R : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (hr2 : r ^ 2 = x ^ 2 + s ^ 2) (ht2 : t ^ 2 = s ^ 2 + d ^ 2)
    (hR2 : R ^ 2 = (x + d) ^ 2 + t ^ 2) :
    R ≤ r + (x / r) * d + (29 / 8 : ℝ) * (t - s) := by
  have ha := abs_nonneg d
  have ha2 := sq_abs d
  have hxr : |x| ≤ r := (sq_le_sq₀ (abs_nonneg _) hr).mp (by rw [sq_abs]; nlinarith)
  have hsr : s ≤ r := (sq_le_sq₀ hs hr).mp (by nlinarith [sq_nonneg x])
  have hst : s ≤ t := (sq_le_sq₀ hs ht).mp (by nlinarith [sq_nonneg d])
  have hxd : x * d ≤ r * |d| := by
    calc
      x * d ≤ |x * d| := le_abs_self _
      _ = |x| * |d| := abs_mul _ _
      _ ≤ r * |d| := mul_le_mul_of_nonneg_right hxr ha
  have hxd' : -(r * |d|) ≤ x * d := by
    have h := neg_abs_le (x * d)
    rw [abs_mul] at h
    nlinarith [mul_le_mul_of_nonneg_right hxr ha]
  by_cases hz : r = 0
  · subst r
    have hx : x = 0 := abs_nonpos_iff.mp (by simpa using hxr)
    have hs0 : s = 0 := le_antisymm hsr hs
    subst x; subst s
    have ht' : t = |d| := (sq_eq_sq₀ ht ha).mp (by nlinarith)
    simp only [zero_div, zero_mul, zero_add, sub_zero]
    nlinarith [sq_nonneg (R - 2 * t)]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hrpos).mp
    field_simp
    by_cases hd : |d| ≤ (12 / 5 : ℝ) * s
    · have hts : t ≤ (13 / 5 : ℝ) * s :=
        (sq_le_sq₀ ht (by positivity)).mp (by nlinarith)
      have hδ : d ^ 2 ≤ (18 / 5 : ℝ) * r * (t - s) := by
        have h₁ := mul_le_mul_of_nonneg_right (show t + s ≤ (18 / 5 : ℝ) * s by linarith)
          (sub_nonneg.mpr hst)
        have h₂ := mul_le_mul_of_nonneg_right hsr
          (show 0 ≤ (18 / 5 : ℝ) * (t - s) by linarith)
        nlinarith
      nlinarith [sq_nonneg (R - r), mul_nonneg hr (sub_nonneg.mpr hst)]
    · have hsd : (12 / 5 : ℝ) * s ≤ |d| := le_of_lt (lt_of_not_ge hd)
      have hta : t ≤ (13 / 12 : ℝ) * |d| :=
        (sq_le_sq₀ ht (by positivity)).mp (by nlinarith)
      have hδ : |d| ≤ (3 / 2 : ℝ) * (t - s) := by
        have h := mul_le_mul_of_nonneg_right
          (show t + s ≤ (3 / 2 : ℝ) * |d| by linarith)
          (sub_nonneg.mpr hst)
        nlinarith
      have hRR : R ≤ r + (17 / 12 : ℝ) * |d| :=
        (sq_le_sq₀ hR (by positivity)).mp (by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_left hδ hr,
        mul_le_mul_of_nonneg_left hRR hr,
        mul_nonneg hr (sub_nonneg.mpr hst)]

/-- The smoothed sign used in the pathwise inequality depends only on the past. -/
def davisCoefficient (x s : ℝ) : ℝ := x / Real.sqrt (x ^ 2 + s ^ 2)

theorem abs_davisCoefficient_le (x s : ℝ) : |davisCoefficient x s| ≤ 1 := by
  have h : |x| ≤ Real.sqrt (x ^ 2 + s ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg s]
  rw [davisCoefficient, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_one_of_le₀ h (Real.sqrt_nonneg _)

theorem davis_step (x s d : ℝ) (hs : 0 ≤ s) :
    Real.sqrt ((x + d) ^ 2 + (s ^ 2 + d ^ 2)) ≤
      Real.sqrt (x ^ 2 + s ^ 2) + davisCoefficient x s * d +
        (29 / 8) * (Real.sqrt (s ^ 2 + d ^ 2) - s) := by
  exact davis_step_algebra x s d _ _ _ hs (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sq_sqrt (by positivity))
    (Real.sq_sqrt (by positivity)) (by rw [Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)])

end HilbertUMD
