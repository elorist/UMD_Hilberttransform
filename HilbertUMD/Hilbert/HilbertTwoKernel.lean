import HilbertUMD.Hilbert.HilbertConstant
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace HilbertUMD

theorem hilbertKernel_memLp_two {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    MemLp (fun y : ℝ => (x-y)⁻¹) 2
      (volume.restrict {y : ℝ | ε < |x-y|}) := by
  have hm : AEStronglyMeasurable (fun y : ℝ => (x-y)⁻¹)
      (volume.restrict {y : ℝ | ε < |x-y|}) := by fun_prop
  apply (memLp_two_iff_integrable_sq hm).2
  have hd := (integrable_inv_one_add_sq.comp_sub_left x).const_mul ((ε⁻¹)^2+1)
  apply hd.integrableOn.mono' (hm.pow 2)
  filter_upwards [ae_restrict_mem
    ((isOpen_lt continuous_const (by fun_prop)).measurableSet :
      MeasurableSet {y : ℝ | ε < |x-y|})] with y hy
  have hz : x-y ≠ 0 := abs_pos.mp (hε.trans hy)
  have hb : ((x-y)⁻¹)^2 ≤ (ε⁻¹)^2 := by
    have hi : |(x-y)⁻¹| ≤ ε⁻¹ := by
      rw [abs_inv]
      exact (inv_le_inv₀ (hε.trans hy) hε).2 hy.le
    nlinarith [sq_abs ((x-y)⁻¹), abs_nonneg ((x-y)⁻¹), inv_pos.mpr hε]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ((x-y)⁻¹)^2 ≤ ((ε⁻¹)^2+1) / (1+(x-y)^2)
  apply (le_div_iff₀ (by positivity : 0 < 1+(x-y)^2)).2
  rw [mul_add, mul_one, ← mul_pow, inv_mul_cancel₀ hz, one_pow]
  linarith

theorem hilbertTrunc_integrable_two {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Integrable (fun y => (x-y)⁻¹ * f y)
      (volume.restrict {y : ℝ | ε < |x-y|}) :=
  (hilbertKernel_memLp_two hε x).integrable_mul (hf.mono_measure Measure.restrict_le_self)

theorem hilbertTrunc_add_two {f g : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    hilbertTrunc ε (f+g) x = hilbertTrunc ε f x + hilbertTrunc ε g x := by
  simp only [hilbertTrunc, Pi.add_apply, smul_eq_mul, mul_add]
  rw [integral_add (hilbertTrunc_integrable_two hf hε x)
    (hilbertTrunc_integrable_two hg hε x), mul_add]

theorem hilbertTrunc_smul_real (c : ℝ) (f : ℝ → ℝ) (ε x : ℝ) :
    hilbertTrunc ε (c • f) x = c * hilbertTrunc ε f x := by
  simp only [hilbertTrunc, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm ((x-_)⁻¹) c, mul_assoc]
  rw [integral_const_mul]
  ring

theorem IsHilbertPVAe.add_two {f g F G : ℝ → ℝ}
    (hF : IsHilbertPVAe f F) (hG : IsHilbertPVAe g G)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    IsHilbertPVAe (f+g) (F+G) := by
  filter_upwards [hF,hG] with x hFx hGx
  apply (hFx.add hGx).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hilbertTrunc_add_two hf hg hε x).symm

theorem IsHilbertPVAe.smul_real {f F : ℝ → ℝ} (hF : IsHilbertPVAe f F) (c : ℝ) :
    IsHilbertPVAe (c • f) (c • F) := by
  filter_upwards [hF] with x hx
  simpa only [hilbertTrunc_smul_real, Pi.smul_apply, smul_eq_mul] using hx.const_mul c

theorem IsHilbertPVAe.congr_output {f F G : ℝ → ℝ}
    (hF : IsHilbertPVAe f F) (hFG : F =ᵐ[volume] G) : IsHilbertPVAe f G := by
  filter_upwards [hF,hFG] with x hx he
  rwa [← he]

end HilbertUMD
