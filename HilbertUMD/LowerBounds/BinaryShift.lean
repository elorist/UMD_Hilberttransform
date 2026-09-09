import HilbertUMD.LowerBounds.BinaryAverages
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Measure and integral identities for the binary map on the unit interval. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace HilbertUMD.BinaryLogit

theorem unitMeasure_split :
    unitMeasure = volume.restrict (Ioo (0 : ℝ) (1/2)) +
      volume.restrict (Ioo (1/2 : ℝ) 1) := by
  simp only [unitMeasure, restrict_Ioo_eq_restrict_Ioc]
  have hu : Ioc (0 : ℝ) 1 = Ioc 0 (1/2) ∪ Ioc (1/2) 1 := by
    ext t
    simp only [mem_Ioc, mem_union]
    constructor
    · intro ht
      by_cases h : t ≤ 1/2
      · exact Or.inl ⟨ht.1, h⟩
      · exact Or.inr ⟨lt_of_not_ge h, ht.2⟩
    · rintro (ht | ht) <;> constructor <;> linarith [ht.1, ht.2]
  rw [hu, Measure.restrict_union]
  · exact disjoint_left.mpr (fun t ht hs => (not_lt_of_ge ht.2) hs.1)
  · exact measurableSet_Ioc

theorem map_affine_volume (a b : ℝ) (ha : a ≠ 0) :
    volume.map (fun t : ℝ => a*t+b) = ENNReal.ofReal |a⁻¹| • volume := by
  have hm : Measurable (fun t : ℝ => a*t) := by fun_prop
  have ht : Measurable (fun t : ℝ => t+b) := by fun_prop
  calc
    _ = (volume.map (fun t : ℝ => a*t)).map (fun t => t+b) := by
      rw [Measure.map_map ht hm]
      rfl
    _ = _ := by
      rw [Real.map_volume_mul_left ha, Measure.map_smul, map_add_right_eq_self]

theorem map_double_left :
    (volume.restrict (Ioo (0 : ℝ) (1/2))).map (fun t => 2*t) =
      (1/2 : ℝ≥0∞) • unitMeasure := by
  have he : (fun t : ℝ => 2*t) ⁻¹' Ioo (0 : ℝ) 1 = Ioo 0 (1/2) := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hf : Measurable (fun t : ℝ => 2*t) := by fun_prop
  rw [← he, ← Measure.restrict_map hf measurableSet_Ioo,
    Real.map_volume_mul_left (by norm_num : (2 : ℝ) ≠ 0), Measure.restrict_smul]
  norm_num [unitMeasure, ENNReal.ofReal_div_of_pos]

theorem map_double_right :
    (volume.restrict (Ioo (1/2 : ℝ) 1)).map (fun t => 2*t-1) =
      (1/2 : ℝ≥0∞) • unitMeasure := by
  have he : (fun t : ℝ => 2*t-1) ⁻¹' Ioo (0 : ℝ) 1 = Ioo (1/2) 1 := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hf : Measurable (fun t : ℝ => 2*t-1) := by fun_prop
  rw [← he, ← Measure.restrict_map hf measurableSet_Ioo]
  have hm : volume.map (fun t : ℝ => 2*t-1) = (1/2 : ℝ≥0∞) • volume := by
    simpa [sub_eq_add_neg, ENNReal.ofReal_div_of_pos] using map_affine_volume 2 (-1) (by norm_num)
  rw [hm, Measure.restrict_smul]
  rfl

theorem tau_measurePreserving : MeasurePreserving tau unitMeasure unitMeasure := by
  refine ⟨measurable_tau, ?_⟩
  conv_lhs => rw [unitMeasure_split]
  rw [Measure.map_add _ _ measurable_tau]
  have hl : (volume.restrict (Ioo (0 : ℝ) (1/2))).map tau =
      (1/2 : ℝ≥0∞) • unitMeasure := by
    rw [← map_double_left]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact if_pos ht.2
  have hr : (volume.restrict (Ioo (1/2 : ℝ) 1)).map tau =
      (1/2 : ℝ≥0∞) • unitMeasure := by
    rw [← map_double_right]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact if_neg (not_lt.mpr ht.1.le)
  rw [hl, hr, ← add_smul]
  rw [ENNReal.add_halves, one_smul]

theorem map_left_inverse :
    unitMeasure.map (fun t : ℝ => t/2) =
      (2 : ℝ≥0∞) • volume.restrict (Ioo (0 : ℝ) (1/2)) := by
  have he : (fun t : ℝ => t/2) ⁻¹' Ioo (0 : ℝ) (1/2) = Ioo 0 1 := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hf : Measurable (fun t : ℝ => t/2) := by fun_prop
  rw [unitMeasure, ← he, ← Measure.restrict_map hf measurableSet_Ioo]
  have hm : volume.map (fun t : ℝ => t/2) = (2 : ℝ≥0∞) • volume := by
    simpa [div_eq_mul_inv, mul_comm] using map_affine_volume (1/2) 0 (by norm_num)
  rw [hm, Measure.restrict_smul]

theorem map_right_inverse :
    unitMeasure.map (fun t : ℝ => (t+1)/2) =
      (2 : ℝ≥0∞) • volume.restrict (Ioo (1/2 : ℝ) 1) := by
  have he : (fun t : ℝ => (t+1)/2) ⁻¹' Ioo (1/2 : ℝ) 1 = Ioo 0 1 := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hf : Measurable (fun t : ℝ => (t+1)/2) := by fun_prop
  rw [unitMeasure, ← he, ← Measure.restrict_map hf measurableSet_Ioo]
  have hm : volume.map (fun t : ℝ => (t+1)/2) = (2 : ℝ≥0∞) • volume := by
    convert map_affine_volume (1/2) (1/2) (by norm_num) using 1 <;> norm_num
    congr 1
    funext t
    ring
  rw [hm, Measure.restrict_smul]

theorem measurableEmbedding_left_inverse : MeasurableEmbedding (fun t : ℝ => t/2) := by
  simpa only [div_eq_mul_inv] using
    (measurableEmbedding_mulRight₀ (by norm_num : (2 : ℝ)⁻¹ ≠ 0))

theorem measurableEmbedding_right_inverse : MeasurableEmbedding (fun t : ℝ => (t+1)/2) :=
  measurableEmbedding_left_inverse.comp (measurableEmbedding_addRight (1 : ℝ))

theorem integral_left_inverse (h : ℝ → ℝ) :
    (∫ t, h (t/2) ∂unitMeasure) = 2 * ∫ t in Ioo (0 : ℝ) (1/2), h t := by
  rw [← measurableEmbedding_left_inverse.integral_map, map_left_inverse, integral_smul_measure]
  norm_num

theorem integral_right_inverse (h : ℝ → ℝ) :
    (∫ t, h ((t+1)/2) ∂unitMeasure) = 2 * ∫ t in Ioo (1/2 : ℝ) 1, h t := by
  rw [← measurableEmbedding_right_inverse.integral_map, map_right_inverse, integral_smul_measure]
  norm_num

theorem integrable_left_inverse {h : ℝ → ℝ} (hh : Integrable h unitMeasure) :
    Integrable (fun t => h (t/2)) unitMeasure := by
  apply measurableEmbedding_left_inverse.integrable_map_iff.mp
  rw [map_left_inverse]
  apply Integrable.smul_measure _ (by norm_num)
  exact hh.mono_measure (Measure.restrict_mono (by intro t ht; exact ⟨ht.1, by linarith [ht.2]⟩) le_rfl)

theorem integrable_right_inverse {h : ℝ → ℝ} (hh : Integrable h unitMeasure) :
    Integrable (fun t => h ((t+1)/2)) unitMeasure := by
  apply measurableEmbedding_right_inverse.integrable_map_iff.mp
  rw [map_right_inverse]
  apply Integrable.smul_measure _ (by norm_num)
  exact hh.mono_measure (Measure.restrict_mono (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩) le_rfl)

theorem integral_unit_split_inverse {h : ℝ → ℝ} (hh : Integrable h unitMeasure) :
    (∫ t, h t ∂unitMeasure) =
      ((∫ t, h (t/2) ∂unitMeasure) + (∫ t, h ((t+1)/2) ∂unitMeasure)) / 2 := by
  have hs := hh
  rw [unitMeasure_split, integrable_add_measure] at hs
  rw [integral_left_inverse, integral_right_inverse]
  conv_lhs => rw [unitMeasure_split, integral_add_measure hs.1 hs.2]
  ring

theorem tau_left_inverse {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : tau (t/2) = t := by
  rw [tau, if_pos (by linarith [ht.2])]
  ring

theorem tau_right_inverse {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : tau ((t+1)/2) = t := by
  rw [tau, if_neg (by linarith [ht.1])]
  ring

theorem integral_comp_tau {h : ℝ → ℝ} (hh : Integrable h unitMeasure) :
    (∫ t, h (tau t) ∂unitMeasure) = ∫ t, h t ∂unitMeasure := by
  have hm : AEStronglyMeasurable h (unitMeasure.map tau) := by
    rw [tau_measurePreserving.map_eq]
    exact hh.aestronglyMeasurable
  rw [← integral_map measurable_tau.aemeasurable hm, tau_measurePreserving.map_eq]

theorem integral_adjoint (h v : ℝ → ℝ)
    (hh : Integrable (fun t => h t * v (tau t)) unitMeasure) :
    (∫ t, h t * v (tau t) ∂unitMeasure) = ∫ t, average h t * v t ∂unitMeasure := by
  have hl : (fun t => h (t/2) * v (tau (t/2))) =ᵐ[unitMeasure]
      (fun t => h (t/2) * v t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [tau_left_inverse ht]
  have hr : (fun t => h ((t+1)/2) * v (tau ((t+1)/2))) =ᵐ[unitMeasure]
      (fun t => h ((t+1)/2) * v t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [tau_right_inverse ht]
  have hil := (integrable_left_inverse hh).congr hl
  have hir := (integrable_right_inverse hh).congr hr
  rw [integral_unit_split_inverse hh, integral_congr_ae hl, integral_congr_ae hr]
  calc
    _ = ∫ t, (h (t/2) * v t + h ((t+1)/2) * v t) / 2 ∂unitMeasure := by
      rw [integral_div, integral_add hil hir]
    _ = _ := by congr 1; funext t; dsimp [average]; ring
end HilbertUMD.BinaryLogit
