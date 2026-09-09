import HilbertUMD.Hilbert.HilbertTwoKernel

/-!
# Truncated kernels on L(3/2)

Positive truncations are genuine integrals on every L(3/2) input. The
linearity statements here do not assume that their principal values exist.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace HilbertUMD

private instance : ENNReal.HolderTriple 3 (3 / 2) 1 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by simp)).mp
  norm_num [ENNReal.toReal_add]⟩

/-- Away from its pole, the Hilbert kernel belongs to L3. -/
theorem hilbertKernel_memLp_three {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    MemLp (fun y : ℝ => (x - y)⁻¹) 3
      (volume.restrict {y : ℝ | ε < |x - y|}) := by
  have htwo := hilbertKernel_memLp_two hε x
  apply (integrable_norm_rpow_iff htwo.1 (p := 3) (by norm_num) (by norm_num)).mp
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  have hi := (htwo.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul ε⁻¹
  apply hi.mono' (htwo.1.norm.pow 3)
  filter_upwards [ae_restrict_mem
    ((isOpen_lt continuous_const (by fun_prop)).measurableSet :
      MeasurableSet {y : ℝ | ε < |x - y|})] with y hy
  have hb : ‖(x - y)⁻¹‖ ≤ ε⁻¹ := by
    rw [Real.norm_eq_abs, abs_inv]
    exact (inv_le_inv₀ (hε.trans hy) hε).mpr hy.le
  change ‖‖(x - y)⁻¹‖ ^ (3 : ℕ)‖ ≤ ε⁻¹ * ‖(x - y)⁻¹‖ ^ 2
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖(x - y)⁻¹‖)
  nlinarith

/-- The integral defining a positive truncation exists for every L(3/2) input. -/
theorem hilbertTrunc_integrable_three_halves {f : ℝ → ℝ}
    (hf : MemLp f (3 / 2) volume) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Integrable (fun y => (x - y)⁻¹ * f y)
      (volume.restrict {y : ℝ | ε < |x - y|}) :=
  (hilbertKernel_memLp_three hε x).integrable_mul (hf.mono_measure Measure.restrict_le_self)

end HilbertUMD
