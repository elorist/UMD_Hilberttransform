import HilbertUMD.Analysis.MixedNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Norm-preserving finite Hilbert-space amplification on real L3, proved by
Gaussian averaging and Tonelli's theorem. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HilbertUMD

private theorem eLpNorm_three_pow {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (f : Ω → E) :
    eLpNorm f 3 μ ^ 3 = ∫⁻ t, ‖f t‖ₑ ^ 3 ∂μ := by
  simpa using (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ)
    (p := (3 : ℝ≥0)) (by norm_num))

private theorem gaussian_inner_eLpNorm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (x : E) :
    eLpNorm (fun y => ⟪x, y⟫) 3 (stdGaussian E) =
      ‖x‖ₑ * eLpNorm (id : ℝ → ℝ) 3 (gaussianReal 0 1) := by
  have hmap : (stdGaussian E).map (innerSL ℝ x) =
      (gaussianReal 0 1).map (fun t : ℝ => ‖x‖ * t) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, innerSL_apply_norm, gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    congr 1
    exact Real.toNNReal_of_nonneg (sq_nonneg _)
  calc
    _ = eLpNorm (id : ℝ → ℝ) 3 ((stdGaussian E).map (innerSL ℝ x)) :=
      (eLpNorm_map_measure (by fun_prop) (by fun_prop)).symm
    _ = eLpNorm (fun t : ℝ => ‖x‖ * t) 3 (gaussianReal 0 1) := by
      rw [hmap, eLpNorm_map_measure (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      change eLpNorm (‖x‖ • (id : ℝ → ℝ)) 3 (gaussianReal 0 1) = _
      rw [eLpNorm_const_smul, enorm_norm]

private theorem gaussian_three_ne_zero :
    eLpNorm (id : ℝ → ℝ) 3 (gaussianReal 0 1) ≠ 0 := by
  intro h
  have hzero := (eLpNorm_eq_zero_iff (by fun_prop) (by norm_num : (3 : ℝ≥0∞) ≠ 0)).mp h
  have hv := variance_congr hzero
  simp at hv

private theorem gaussian_average_three {ι : Type*} [Fintype ι]
    (f : ι → Lp ℝ 3 (volume : Measure ℝ)) :
    (∫⁻ y : EuclideanSpace ℝ ι,
      eLpNorm (fun t => ∑ i, f i t * y i) 3 volume ^ 3
        ∂stdGaussian (EuclideanSpace ℝ ι)) =
      mixedNorm 3 2 volume (fun t i => f i t) ^ 3 *
        eLpNorm (id : ℝ → ℝ) 3 (gaussianReal 0 1) ^ 3 := by
  classical
  conv_lhs => enter [2, y]; rw [eLpNorm_three_pow]
  rw [lintegral_lintegral_swap]
  · have hpoint (t : ℝ) :
        (∫⁻ y : EuclideanSpace ℝ ι, ‖∑ i, f i t * y i‖ₑ ^ 3
          ∂stdGaussian (EuclideanSpace ℝ ι)) =
        ‖(WithLp.toLp 2 (fun i => f i t) : EuclideanSpace ℝ ι)‖ₑ ^ 3 *
          eLpNorm (id : ℝ → ℝ) 3 (gaussianReal 0 1) ^ 3 := by
      have hx := congrArg (fun a : ℝ≥0∞ => a ^ 3)
        (gaussian_inner_eLpNorm (WithLp.toLp 2 (fun i => f i t) : EuclideanSpace ℝ ι))
      rw [eLpNorm_three_pow] at hx
      simpa only [mul_pow, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct, star_trivial, mul_comm (G := ℝ)] using hx
    simp_rw [hpoint]
    rw [lintegral_mul_const']
    · rw [← eLpNorm_three_pow]
      rfl
    · exact ENNReal.pow_ne_top (memLp_id_gaussianReal' 3 (by norm_num)).2.ne
  · exact (Finset.measurable_sum _ (fun i _ =>
      ((Lp.stronglyMeasurable (f i)).measurable.comp measurable_snd).mul
        ((by fun_prop : Measurable (fun y : EuclideanSpace ℝ ι => y i)).comp
          measurable_fst))).enorm.pow_const 3 |>.aemeasurable

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

private theorem eLpNorm_sum_mul {ι : Type*} [Fintype ι]
    (f : ι → Lp ℝ 3 (volume : Measure ℝ)) (a : ι → ℝ) :
    eLpNorm (fun t => ∑ i, f i t * a i) 3 volume = ‖∑ i, a i • f i‖ₑ := by
  classical
  rw [Lp.enorm_def]
  apply eLpNorm_congr_ae
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • f i)
  have hsmul := ae_all_iff.2 (fun i => Lp.coeFn_smul (a i) (f i))
  filter_upwards [hsum, hsmul] with t ht hst
  rw [ht]
  apply Finset.sum_congr rfl
  intro i _
  rw [hst i]
  simp [mul_comm]

/-- Applying one real scalar L3 operator to every coordinate preserves its
operator-norm bound for the finite Euclidean norm. -/
theorem scalar_operator_hilbert_extension_three_lp {ι : Type*} [Fintype ι]
    (R : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 (volume : Measure ℝ))
    (f : ι → Lp ℝ 3 (volume : Measure ℝ)) :
    mixedNorm 3 2 volume (fun t i => R (f i) t) ≤
      (‖R‖₊ : ℝ≥0∞) * mixedNorm 3 2 volume (fun t i => f i t) := by
  classical
  have hscalar (y : EuclideanSpace ℝ ι) :
      eLpNorm (fun t => ∑ i, R (f i) t * y i) 3 volume ≤
        (‖R‖₊ : ℝ≥0∞) * eLpNorm (fun t => ∑ i, f i t * y i) 3 volume := by
    rw [eLpNorm_sum_mul, eLpNorm_sum_mul]
    have hR : ∑ i, y i • R (f i) = R (∑ i, y i • f i) := by simp
    rw [hR]
    change (‖R (∑ i, y i • f i)‖₊ : ℝ≥0∞) ≤
      (‖R‖₊ : ℝ≥0∞) * (‖∑ i, y i • f i‖₊ : ℝ≥0∞)
    rw [← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact_mod_cast R.le_opNorm (∑ i, y i • f i)
  have havg := lintegral_mono (μ := stdGaussian (EuclideanSpace ℝ ι))
    (fun y => ENNReal.pow_le_pow_left (n := 3) (hscalar y))
  simp_rw [mul_pow] at havg
  rw [lintegral_const_mul' _ _ (by finiteness),
    gaussian_average_three, gaussian_average_three, ← mul_assoc] at havg
  have hc0 := pow_ne_zero 3 gaussian_three_ne_zero
  have hct := ENNReal.pow_ne_top (n := 3)
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 3 (by norm_num)).2.ne
  have hpow := (ENNReal.mul_le_mul_iff_left hc0 hct).mp havg
  rw [← mul_pow] at hpow
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hpow

end HilbertUMD
