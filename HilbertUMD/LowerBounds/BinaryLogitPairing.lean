import HilbertUMD.LowerBounds.BinaryLogitCoefficients
import HilbertUMD.LowerBounds.BinaryShift

/-! Identification of the scalar coefficient integrals with the witness. -/

noncomputable section
open MeasureTheory Set Filter intervalIntegral
open scoped ENNReal

namespace HilbertUMD.BinaryLogit

theorem averaged_integrable (j : ℕ) : Integrable (averaged j) unitMeasure :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (averaged_intervalIntegrable j 0 1)

theorem G_integrable (n : ℕ) : Integrable (G n) unitMeasure := by
  induction n with
  | zero => exact integrable_g
  | succ n ih =>
    exact (tau_measurePreserving.integrable_comp_of_integrable ih).add
      ((integrable_g.sub
        (tau_measurePreserving.integrable_comp_of_integrable integrable_g)).const_mul _)

theorem coefficient_eq_integral_sign {h : ℝ → ℝ} (hh : AllIntervalIntegrable h) :
    coefficient h = ∫ t, h t * sign t ∂unitMeasure := by
  have hlh : Integrable h (volume.restrict (Ioo (0 : ℝ) (1 / 2))) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
      (hh 0 (1 / 2))
  have hrh : Integrable h (volume.restrict (Ioo (1 / 2 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)).mp
      (hh (1 / 2) 1)
  have hl : (fun t => h t * sign t) =ᵐ[volume.restrict (Ioo (0 : ℝ) (1 / 2))] (fun t => -h t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [sign, if_pos ht.2, mul_neg_one]
  have hr : (fun t => h t * sign t) =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)] h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [sign, if_neg (not_lt.mpr ht.1.le), mul_one]
  rw [unitMeasure_split,
    integral_add_measure (hlh.neg.congr hl.symm) (hrh.congr hr.symm),
    integral_congr_ae hl, integral_congr_ae hr, MeasureTheory.integral_neg]
  simp only [coefficient, intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), integral_Ioc_eq_integral_Ioo]
  ring

theorem integrable_mul_sign_iterate {h : ℝ → ℝ} (hh : Integrable h unitMeasure)
    (j : ℕ) : Integrable (fun t => h t * sign ((tau^[j]) t)) unitMeasure := by
  have hm : Measurable sign :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  apply hh.mul_bdd (c := 1) (hm.comp (measurable_tau.iterate j)).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by dsimp [sign]; split_ifs <;> norm_num)

theorem integral_averaged_sign_iterate (k j : ℕ) :
    (∫ t, averaged k t * sign ((tau^[j]) t) ∂unitMeasure) = a (k + j) := by
  induction j generalizing k with
  | zero =>
    simpa only [Function.iterate_zero_apply, add_zero, a] using
      (coefficient_eq_integral_sign (averaged_intervalIntegrable k)).symm
  | succ j ih =>
    have hh : Integrable (fun t => averaged k t * sign ((tau^[j]) (tau t))) unitMeasure := by
      simpa only [Function.iterate_succ_apply] using
        integrable_mul_sign_iterate (averaged_integrable k) (j + 1)
    simp only [Function.iterate_succ_apply]
    rw [integral_adjoint (averaged k) (fun t => sign ((tau^[j]) t)) hh]
    change (∫ t, averaged (k + 1) t * sign ((tau^[j]) t) ∂unitMeasure) = _
    rw [ih]
    congr 1
    omega

theorem a_eq_integral_g_sign_iterate (j : ℕ) :
    a j = ∫ t, g t * sign ((tau^[j]) t) ∂unitMeasure := by
  simpa only [averaged, zero_add] using (integral_averaged_sign_iterate 0 j).symm

end HilbertUMD.BinaryLogit
