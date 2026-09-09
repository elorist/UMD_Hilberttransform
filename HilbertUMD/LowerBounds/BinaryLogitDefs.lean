import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! The scalar logarithmic diagonal witness for the signed dyadic matrix. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace HilbertUMD.BinaryLogit

def unitMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure unitMeasure := by
  constructor
  simp [unitMeasure]

def tau (t : ℝ) : ℝ := if t < 1 / 2 then 2 * t else 2 * t - 1

def g (t : ℝ) : ℝ := Real.pi⁻¹ * Real.log (t / (1 - t))

def G : ℕ → ℝ → ℝ
  | 0, t => g t
  | n + 1, t => G n (tau t) + (-1 : ℝ) ^ (n + 1) * (g t - g (tau t))

def delta : ℝ := 2 / Real.pi * Real.log (27 / 16)

theorem delta_pos : 0 < delta := by
  exact mul_pos (div_pos (by norm_num) Real.pi_pos)
    (Real.log_pos (by norm_num))

@[simp] theorem G_zero (t : ℝ) : G 0 t = g t := rfl

theorem G_succ (n : ℕ) (t : ℝ) :
    G (n + 1) t = G n (tau t) + (-1 : ℝ) ^ (n + 1) * (g t - g (tau t)) := rfl

theorem measurable_tau : Measurable tau := by
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.mul measurable_id)
    ((measurable_const.mul measurable_id).sub measurable_const)

theorem measurable_g : Measurable g := by
  exact measurable_const.mul
    (Real.measurable_log.comp (measurable_id.div (measurable_const.sub measurable_id)))

theorem measurable_G (n : ℕ) : Measurable (G n) := by
  induction n with
  | zero => exact measurable_g
  | succ n ih =>
    exact (ih.comp measurable_tau).add
      (measurable_const.mul (measurable_g.sub (measurable_g.comp measurable_tau)))

theorem g_eq_sub_logs {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    g t = Real.pi⁻¹ * (Real.log t - Real.log (1 - t)) := by
  rw [g, Real.log_div ht.1.ne' (sub_pos.mpr ht.2).ne']

theorem monotoneOn_g : MonotoneOn g (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [g_eq_sub_logs hx, g_eq_sub_logs hy]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.pi_pos.le)
  apply sub_le_sub
  · exact Real.log_le_log hx.1 hxy
  · exact Real.log_le_log (sub_pos.mpr hy.2) (by linarith)

end HilbertUMD.BinaryLogit
