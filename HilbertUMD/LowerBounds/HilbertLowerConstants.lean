import HilbertUMD.LowerBounds.HilbertLower
import HilbertUMD.Hilbert.HilbertTwoPV
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The paper's coefficient 1/7 from the existing uniform interval witness. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace HilbertUMD

private theorem scalar_interval_log_norm :
    eLpNorm (fun t : ℝ => Real.log |t / (t - 1)| / Real.pi) 2 volume = 1 := by
  let f : ℝ → ℝ := (Ico (0 : ℝ) 1).indicator (fun _ => 1)
  have hf : MemLp f 2 volume := memLp_indicator_const 2 measurableSet_Ico 1 (Or.inr (by simp))
  have hp := realHilbertL2_pv_all f hf
  have hi := Interfaces.interval_hilbert_pv ℝ 0 1 (by norm_num)
  have he : (realHilbertL2 (hf.toLp f) : ℝ → ℝ) =ᵐ[volume]
      (fun t : ℝ => Real.log |t / (t - 1)| / Real.pi) := by
    simpa only [sub_zero, RCLike.ofReal_real_eq_id, id_eq] using hp.unique hi
  rw [← eLpNorm_congr_ae he, ← Lp.enorm_def, realHilbertL2.enorm_map,
    Lp.enorm_def, eLpNorm_congr_ae hf.coeFn_toLp]
  simp [f, eLpNorm_indicator_const, measurableSet_Ico]

variable {𝕜 : Type*} [RCLike 𝕜]

theorem summation_HilbertBound_one_lower (n : ℕ) {C : ℝ≥0}
    (hC : HilbertBound 2 (summationOperator (𝕜 := 𝕜) n) C) : (1 : ℝ) ≤ C := by
  obtain ⟨g, hpv, _, hgn⟩ := Interfaces.HilbertBound.l2_pv_extension hC
    (uniformStep n) (uniformStep_memLp n 2)
  rw [eLpNorm_uniformStep_two, mul_one] at hgn
  have hN : 0 < 2 ^ n := by positivity
  let k : Leaf n := (leafEquivFin n).symm ⟨2 ^ n - 1, by omega⟩
  have hk : (leafEquivFin n k).val + 1 = 2 ^ n := by
    simp only [k, Equiv.apply_symm_apply]
    omega
  have he : (((leafEquivFin n k).val : ℝ) + 1) / (2 ^ n : ℕ) = 1 := by
    have h : ((leafEquivFin n k).val : ℝ) + 1 = (2 ^ n : ℕ) := by exact_mod_cast hk
    rw [h, div_self (by positivity)]
  have hd : eLpNorm (fun t : ℝ => Real.log |t / (t - 1)| / Real.pi) 2 volume ≤
      eLpNorm g 2 volume := by
    apply eLpNorm_mono_ae
    filter_upwards [summation_pv_coordinate n hpv k] with t ht
    calc
      _ = ‖g t k‖ := by rw [ht, he, RCLike.norm_ofReal, Real.norm_eq_abs]
      _ ≤ ‖g t‖ := norm_le_pi_norm _ _
  rw [scalar_interval_log_norm] at hd
  exact_mod_cast hd.trans hgn

theorem summation_pv_unit_lower (n : ℕ) {g : ℝ → Vec 𝕜 n}
    (hg : IsHilbertPVAe (fun t => summationOperator n (uniformStep n t)) g) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Ioo (0 : ℝ) 1 →
      (Real.log ((2 : ℝ)^n) + Real.log t) / Real.pi ≤ ‖g t‖ := by
  have hN : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have hc := ae_all_iff.mpr (fun i : Leaf n => summation_pv_coordinate n hg i)
  filter_upwards [hc, ae_ne_uniform_endpoint (2^n)] with t hc hgrid ht
  have ht0 : 0 < t := ht.1
  have hNt : 0 < ((2 ^ n : ℕ) : ℝ) * t := mul_pos hN ht0
  have hlog : Real.log ((2 : ℝ)^n) + Real.log t = Real.log ((2 ^ n : ℕ) * t) := by
    rw [Real.log_mul (by positivity) ht.1.ne']
    simp
  rw [hlog]
  by_cases hsmall : ((2 ^ n : ℕ) : ℝ) * t ≤ 1
  · exact (div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos hNt.le hsmall) Real.pi_pos.le).trans (norm_nonneg _)
  · let i : ℕ := ⌊((2 ^ n : ℕ) : ℝ) * t⌋₊
    have hi1 : 1 ≤ i := Nat.le_floor (by
      exact_mod_cast (le_of_lt (lt_of_not_ge hsmall)))
    have hiN : i < 2 ^ n := floor_mul_lt_of_unit_interval _ (by positivity) t ⟨ht.1.le, ht.2⟩
    have hile : (i : ℝ) ≤ (2 ^ n : ℕ) * t := Nat.floor_le hNt.le
    have hilt : (i : ℝ) < (2 ^ n : ℕ) * t := by
      apply lt_of_le_of_ne hile
      intro heq
      apply hgrid i
      apply (eq_div_iff hN.ne').mpr
      nlinarith
    have hiup : (2 ^ n : ℕ) * t < (i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hd : 0 < t - (i : ℝ) / (2 ^ n : ℕ) := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hN).mpr
      nlinarith
    have hmesh : (2 ^ n : ℕ) * (t - (i : ℝ) / (2 ^ n : ℕ)) ≤ 1 := by
      rw [mul_sub, mul_div_cancel₀ _ hN.ne']
      linarith
    have hl : Real.log ((2 ^ n : ℕ) * t) ≤
        Real.log (t / (t - (i : ℝ) / (2 ^ n : ℕ))) := by
      apply Real.log_le_log hNt
      apply (le_div_iff₀ hd).mpr
      nlinarith [mul_le_mul_of_nonneg_right hmesh ht.1.le]
    let k : Leaf n := (leafEquivFin n).symm ⟨i - 1, by omega⟩
    have hk : (leafEquivFin n k).val + 1 = i := by
      simp only [k, Equiv.apply_symm_apply]
      omega
    have he : ((leafEquivFin n k).val : ℝ) + 1 = i := by exact_mod_cast hk
    calc
      _ ≤ Real.log (t / (t - (i : ℝ) / (2 ^ n : ℕ))) / Real.pi :=
        div_le_div_of_nonneg_right hl Real.pi_pos.le
      _ ≤ ‖g t k‖ := by
        rw [hc k, he, RCLike.norm_ofReal, Real.log_abs]
        exact le_abs_self _
      _ ≤ ‖g t‖ := norm_le_pi_norm _ _

theorem summation_HilbertBound_unit_log_lower (n : ℕ) {C : ℝ≥0}
    (hC : HilbertBound 2 (summationOperator (𝕜 := 𝕜) n) C) :
    ((n : ℝ) * Real.log 2 - 1) / Real.pi ≤ C := by
  obtain ⟨g, hpv, hgp, hgn⟩ := Interfaces.HilbertBound.l2_pv_extension hC
    (uniformStep n) (uniformStep_memLp n 2)
  rw [eLpNorm_uniformStep_two, mul_one] at hgn
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  let : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hgm : MemLp g 2 μ := hgp.mono_measure Measure.restrict_le_self
  have hgi : Integrable g μ := hgm.integrable (by norm_num)
  have hl : Integrable Real.log μ :=
    (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).1.mono_set Ioo_subset_Ioc_self
  have hli : Integrable (fun t => (Real.log ((2 : ℝ)^n) + Real.log t) / Real.pi) μ :=
    (integrable_const _ |>.add hl).div_const _
  have hlogInt : ∫ t, Real.log t ∂μ = -1 := by
    change ∫ t in Ioo (0 : ℝ) 1, Real.log t = -1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
    norm_num [integral_log]
  have hInt : ∫ t, (Real.log ((2 : ℝ)^n) + Real.log t) / Real.pi ∂μ =
      ((n : ℝ) * Real.log 2 - 1) / Real.pi := by
    rw [integral_div, integral_add (integrable_const _) hl, integral_const, hlogInt]
    simp [Real.log_pow, sub_eq_add_neg]
  have hi : ((n : ℝ) * Real.log 2 - 1) / Real.pi ≤ ∫ t, ‖g t‖ ∂μ := by
    rw [← hInt]
    apply integral_mono_ae hli hgi.norm
    filter_upwards [ae_restrict_of_ae (summation_pv_unit_lower n hpv),
      self_mem_ae_restrict measurableSet_Ioo] with t ht hs
    exact ht hs
  have hnorm : eLpNorm g 1 μ ≤ (C : ℝ≥0∞) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) hgm.1).trans
      ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans hgn)
  have hr := ENNReal.toReal_mono (by simp : (C : ℝ≥0∞) ≠ ⊤) hnorm
  rw [toReal_eLpNorm hgm.1, lpNorm_one_eq_integral_norm hgm.1, ENNReal.coe_toReal] at hr
  exact hi.trans hr

theorem summation_HilbertBound_seventh (n : ℕ) {C : ℝ≥0}
    (hC : HilbertBound 2 (summationOperator (𝕜 := 𝕜) n) C) :
    ((n : ℝ) + 1) / 7 ≤ C := by
  by_cases hn : n ≤ 6
  · have hn' : (n : ℝ) ≤ 6 := by exact_mod_cast hn
    exact (by linarith : ((n : ℝ) + 1) / 7 ≤ 1).trans (summation_HilbertBound_one_lower n hC)
  · have hn' : (7 : ℝ) ≤ n := by exact_mod_cast (show 7 ≤ n by omega)
    have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hpi : Real.pi ≤ 22 / 7 := by linarith [Real.pi_lt_d4]
    have hnum := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)
    have hden := mul_le_mul_of_nonneg_right hpi (by positivity : 0 ≤ (n : ℝ) + 1)
    have h : ((n : ℝ) + 1) / 7 ≤ ((n : ℝ) * Real.log 2 - 1) / Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).mpr
      nlinarith
    exact h.trans (summation_HilbertBound_unit_log_lower n hC)

theorem summation_hilbertConstant_seventh (n : ℕ) :
    ENNReal.ofReal (((n : ℝ) + 1) / 7) ≤ hilbertConstant 2 (summationOperator (𝕜 := 𝕜) n) :=
  le_hilbertConstant (fun _ hC => ENNReal.ofReal_le_coe.mpr (summation_HilbertBound_seventh n hC))

end HilbertUMD
