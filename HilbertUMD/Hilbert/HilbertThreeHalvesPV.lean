import HilbertUMD.Hilbert.HilbertThreeHalvesFromFour
import HilbertUMD.Hilbert.HilbertThreeHalvesKernel
import HilbertUMD.Hilbert.HilbertSmoothKernel

/-!
# Almost-everywhere principal values on L(3/2)

Duality identifies smooth averages of the independently constructed operator
with smooth Hilbert kernels. Their difference from the sharp kernel is odd,
integrable, and has quadratic decay. Lebesgue differentiation and the dyadic
estimate therefore identify the sharp principal value almost everywhere.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace HilbertUMD.HilbertThreeHalvesPV

open HilbertThreeHalvesFromFour HilbertSmoothKernel LebesgueDecayApproximation

private instance : ENNReal.HolderTriple 3 (3 / 2) 1 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by simp)).mp
  norm_num [ENNReal.toReal_add]⟩

theorem realHilbertThree_schwartz_pv (u : SchwartzMap ℝ ℝ) :
    realHilbertThree (u.toLp 3) =ᵐ[volume] pv u := by
  have he := realHilbertThree_agrees_two u (u.memLp 2) (u.memLp 3)
  have he3 : (u.memLp 3 volume).toLp (u : ℝ → ℝ) = u.toLp 3 := rfl
  have he2 : (u.memLp 2 volume).toLp (u : ℝ → ℝ) = u.toLp 2 := rfl
  rw [he3, he2] at he
  have hp := (HilbertFourBound.realHilbertFour_schwartz_pv u).unique
    (isHilbertPV_pv (u.smooth 1) u.integrable).ae
  filter_upwards [he, HilbertFourBound.realHilbertFour_schwartz u, hp] with y h3 h4 hP
  rw [h3, ← h4, hP]

theorem smooth_kernel_integrable {f : ℝ → ℝ} (hf : MemLp f (3 / 2) volume)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Integrable (fun y => (ε⁻¹ * pv test ((x - y) / ε)) * f y) := by
  let u := scaledTest hε x
  have hi := ((Lp.memLp (realHilbertThree (u.toLp 3))).integrable_mul hf).neg
  apply hi.congr
  filter_upwards [realHilbertThree_schwartz_pv u] with y hy
  change -(realHilbertThree (u.toLp 3) y * f y) = _
  rw [hy]
  have hu : (u : ℝ → ℝ) = scaled ε x := rfl
  rw [hu, pv_scaled hε]
  ring

/-- Smooth averages of the dual operator have the classical smooth Hilbert kernel. -/
theorem smooth_pairing {f : ℝ → ℝ} (hf : MemLp f (3 / 2) volume)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (∫ y, scaled ε x y * realHilbertThreeHalves (hf.toLp f) y) =
      ∫ y, (ε⁻¹ * pv test ((x - y) / ε)) * f y := by
  let u := scaledTest hε x
  calc
    _ = ∫ y, (u.toLp 3 : Lp ℝ 3 volume) y * realHilbertThreeHalves (hf.toLp f) y := by
      apply integral_congr_ae
      filter_upwards [u.coeFn_toLp 3] with y hy
      rw [hy]
      rfl
    _ = -(∫ y, realHilbertThree (u.toLp 3) y * hf.toLp f y) :=
      dual_pairing realHilbertThree _ _
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [realHilbertThree_schwartz_pv u, hf.coeFn_toLp] with y hy hfy
      rw [hy, hfy]
      have hu : (u : ℝ → ℝ) = scaled ε x := rfl
      rw [hu, pv_scaled hε]
      ring

private def sharp (ε x y : ℝ) : ℝ :=
  if ε < |x - y| then Real.pi⁻¹ * (x - y)⁻¹ else 0

private theorem sharp_integrable {f : ℝ → ℝ} (hf : MemLp f (3 / 2) volume)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) : Integrable (fun y => sharp ε x y * f y) := by
  have hs : MeasurableSet {y : ℝ | ε < |x - y|} := by measurability
  have hi := ((integrable_indicator_iff hs).mpr
    (hilbertTrunc_integrable_three_halves hf hε x)).const_mul Real.pi⁻¹
  apply hi.congr
  filter_upwards with y
  by_cases hy : ε < |x - y| <;> simp [sharp, indicator, hy, mul_assoc]

private theorem integral_sharp (f : ℝ → ℝ) (ε x : ℝ) :
    (∫ y, sharp ε x y * f y) = hilbertTrunc ε f x := by
  have hs : MeasurableSet {y : ℝ | ε < |x - y|} := by measurability
  rw [hilbertTrunc, ← integral_indicator hs]
  simp only [smul_eq_mul, ← integral_const_mul]
  congr 1
  funext y
  by_cases hy : ε < |x - y| <;> simp [sharp, indicator, hy, mul_assoc]

theorem truncation_sub_average {f : ℝ → ℝ} (hf : MemLp f (3 / 2) volume)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    hilbertTrunc ε f x - (∫ y, scaled ε x y * realHilbertThreeHalves (hf.toLp f) y) =
      ∫ y, scaledError ε x y * (f y - f x) := by
  have he (y : ℝ) : scaledError ε x y * f y =
      sharp ε x y * f y - (ε⁻¹ * pv test ((x - y) / ε)) * f y := by
    rw [scaledError_eq hε]
    simp only [sharp, sub_mul]
  have hi : Integrable (fun y => scaledError ε x y * f y) := by
    simp_rw [he]
    exact (sharp_integrable hf hε x).sub (smooth_kernel_integrable hf hε x)
  have hc := (scaledError_integrable hε x).mul_const (f x)
  calc
    _ = ∫ y, scaledError ε x y * f y := by
      simp_rw [he]
      rw [integral_sub (sharp_integrable hf hε x) (smooth_kernel_integrable hf hε x),
        integral_sharp, smooth_pairing hf hε x]
    _ = ∫ y, scaledError ε x y * (f y - f x) := by
      simp_rw [mul_sub]
      rw [integral_sub hi hc, integral_mul_const, integral_scaledError hε x]
      simp

/-- Sharp principal values realize the independent L(3/2) operator almost everywhere. -/
theorem realHilbertThreeHalves_pv {f : ℝ → ℝ} (hf : MemLp f (3 / 2) volume) :
    IsHilbertPVAe f (realHilbertThreeHalves (hf.toLp f)) := by
  obtain ⟨C, hC, hb⟩ := exists_error_bound
  filter_upwards [ae_mean_norm_sub hf CubicLp.factOneLeThreeHalves.out (by finiteness),
    ae_scaled_tendsto ((Lp.memLp (realHilbertThreeHalves (hf.toLp f))).locallyIntegrable
      CubicLp.factOneLeThreeHalves.out)] with x hx hRx
  obtain ⟨hlim, M, hM⟩ := hx
  have hu : LocallyIntegrable (fun y => ‖f y - f x‖) volume := by
    rw [← locallyIntegrableOn_univ]
    exact (((hf.locallyIntegrable CubicLp.factOneLeThreeHalves.out).sub
      (locallyIntegrable_const (f x))).locallyIntegrableOn univ).norm
  have hz : Tendsto (fun ε => ∫ y, scaledError ε x y * (f y - f x)) (𝓝[>] 0) (𝓝 0) := by
    apply integral_decay_tendsto_zero (fun y => norm_nonneg _) hu hC hM hlim
    intro ε hε y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (scaledError_bound hC hb hε x y) (norm_nonneg _)
  have ht := hRx.add hz
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he := truncation_sub_average hf hε x
  linarith

end HilbertUMD.HilbertThreeHalvesPV
