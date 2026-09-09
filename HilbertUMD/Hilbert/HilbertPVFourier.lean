import HilbertUMD.Hilbert.HilbertPVPointwise
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Scalar principal values and the Fourier Hilbert transform

The symmetric frequency cutoff of `-i sign` has inverse transform
`(1 - cos (2πRx)) / (πx)`. The symmetrized difference quotient is integrable
for C¹ integrable inputs. Riemann–Lebesgue identifies the pointwise limit of
these cutoffs with the principal value; Plancherel and an a.e. convergent
subsequence identify the same limit with `hilbertL2`.

The argument uses only mathlib and the proved pointwise Hilbert integral
calculus. It also proves agreement of the integral and L² Fourier transforms
on their common domain, via their actions on Schwartz test functions.
-/

noncomputable section

open MeasureTheory Filter Set FourierTransform
open scoped Topology Real SchwartzMap ENNReal NNReal

namespace HilbertUMD

theorem integral_fourier_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  simpa only [ContinuousLinearMap.mul_apply', Real.instFourierTransform,
    FourierTransform.fourier,
    show (innerₗ ℝ).flip = innerₗ ℝ from by ext; simp] using
    (VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar
      (by fun_prop : Continuous (fun p : ℝ × ℝ => innerₗ ℝ p.1 p.2)) hf hg)

theorem integral_fourierInv_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕⁻ f x * g x) = ∫ x, f x * 𝓕⁻ g x := by
  simpa only [ContinuousLinearMap.mul_apply', Real.instFourierTransformInv,
    FourierTransformInv.fourierInv,
    show (-innerₗ ℝ).flip = -innerₗ ℝ from by ext; simp] using
    (VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (L := -innerₗ ℝ) (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2)) hf hg)

/-- The integral and Plancherel Fourier transforms agree on their common domain. -/
theorem fourier_toLp_ae {f : ℝ → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2) :
    (𝓕 (hf₂.toLp f) : ComplexL2) =ᵐ[volume] 𝓕 f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num))
    ((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).locallyIntegrable)
  intro g hgd hgc
  let s : SchwartzMap ℝ ℂ :=
    (hgc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hgd)
  have heq := congrArg (fun T : TemperedDistribution ℝ ℂ => T s)
    (Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at heq
  calc
    (∫ x, g x • (𝓕 (hf₂.toLp f) : ComplexL2) x) =
        ∫ x, (𝓕 s) x * (hf₂.toLp f) x := by
      change (∫ x, s x • (𝓕 (hf₂.toLp f) : ComplexL2) x) = _
      simpa only [smul_eq_mul] using heq.symm
    _ = ∫ x, (𝓕 s) x * f x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx using by rw [hx]
    _ = ∫ x, s x * 𝓕 f x := integral_fourier_mul_eq s.integrable hf
    _ = ∫ x, g x • 𝓕 f x := by rfl

theorem fourierInv_toLp_ae {f : ℝ → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2) :
    (𝓕⁻ (hf₂.toLp f) : ComplexL2) =ᵐ[volume] 𝓕⁻ f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num))
    ((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2)) hf).locallyIntegrable)
  intro g hgd hgc
  let s : SchwartzMap ℝ ℂ :=
    (hgc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hgd)
  have heq := congrArg (fun T : TemperedDistribution ℝ ℂ => T s)
    (Lp.fourierInv_toTemperedDistribution_eq (hf₂.toLp f))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at heq
  calc
    (∫ x, g x • (𝓕⁻ (hf₂.toLp f) : ComplexL2) x) =
        ∫ x, (𝓕⁻ s) x * (hf₂.toLp f) x := by
      change (∫ x, s x • (𝓕⁻ (hf₂.toLp f) : ComplexL2) x) = _
      simpa only [smul_eq_mul] using heq.symm
    _ = ∫ x, (𝓕⁻ s) x * f x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx using by rw [hx]
    _ = ∫ x, s x * 𝓕⁻ f x := by
      simpa only [SchwartzMap.fourierInv_coe] using integral_fourierInv_mul_eq s.integrable hf
    _ = ∫ x, g x • 𝓕⁻ f x := by rfl

section Difference

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cancellation in a symmetrically truncated Hilbert integral. -/
def hilbertDifference (f : ℝ → E) (x y : ℝ) : E :=
  y⁻¹ • (f (x - y) - f (x + y))

theorem integrable_hilbertDifference {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (x : ℝ) : Integrable (hilbertDifference f x) := by
  let r : ℝ → E := fun y => f (x - y) - f (x + y)
  have hr : Integrable r := (hi.comp_sub_left x).sub (hi.comp_add_left x)
  have hrd : ContDiff ℝ 1 r := by dsimp [r]; fun_prop
  have hds : Continuous (dslope r 0) := by
    rw [← continuousOn_univ, continuousOn_dslope (univ_mem : univ ∈ 𝓝 (0 : ℝ))]
    exact ⟨hrd.continuous.continuousOn, (hrd.differentiable (by norm_num)).differentiableAt⟩
  have hnear : IntegrableOn (hilbertDifference f x) (Icc (-1) 1) := by
    apply hds.integrableOn_Icc.congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with y hy
    simp [hilbertDifference, dslope_of_ne r hy, slope_def_module, r]
  have hfar : IntegrableOn (hilbertDifference f x) {y : ℝ | 1 / 2 < |y|} := by
    change IntegrableOn (fun y => y⁻¹ • (f (x - y) - f (x + y))) _
    have h := (hilbertTrunc_integrable hr (show (0 : ℝ) < 1 / 2 by norm_num) 0).neg
    simpa [IntegrableOn, hilbertDifference, r, neg_smul] using h
  have hu : Icc (-1 : ℝ) 1 ∪ {y : ℝ | 1 / 2 < |y|} = univ := by
    ext y
    simp only [mem_union, mem_Icc, mem_ofPred_eq, mem_univ, iff_true]
    by_cases h : -1 ≤ y ∧ y ≤ 1
    · exact Or.inl h
    · right
      rcases not_and_or.mp h with h | h <;> simp only [not_le] at h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  have h := hnear.union hfar
  rwa [hu, integrableOn_univ] at h

theorem hilbertTrunc_eq_difference {f : ℝ → E} (hi : Integrable f)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    hilbertTrunc ε f x = (2 * Real.pi)⁻¹ •
      ∫ y in {y : ℝ | ε < |y|}, hilbertDifference f x y := by
  let a : ℝ → E := fun y => if ε < |y| then y⁻¹ • f (x - y) else 0
  have hs : MeasurableSet {y : ℝ | ε < |x - y|} := by
    exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have ha : Integrable a := by
    have h := ((integrable_indicator_iff hs).2 (hilbertTrunc_integrable hi hε x)).comp_sub_left x
    simpa [a, Set.indicator, sub_sub_cancel] using h
  have hchange : hilbertTrunc ε f x = Real.pi⁻¹ • ∫ y, a y := by
    rw [hilbertTrunc, ← integral_indicator hs]
    congr 1
    rw [← integral_sub_left_eq_self _ volume x]
    simp [a, Set.indicator, sub_sub_cancel]
  have hsym : (∫ y in {y : ℝ | ε < |y|}, hilbertDifference f x y) =
      (2 : ℝ) • ∫ y, a y := by
    rw [← integral_indicator (isOpen_lt continuous_const continuous_abs).measurableSet]
    have heq : ({y : ℝ | ε < |y|}.indicator (hilbertDifference f x)) =
        fun y => a y + a (-y) := by
      funext y
      by_cases hy : ε < |y|
      · simp [a, hilbertDifference, hy, sub_eq_add_neg]
      · simp [a, hy]
    rw [heq, integral_add ha ha.comp_neg, integral_neg_eq_self, two_smul]
  rw [hchange, hsym, smul_smul]
  congr 1
  field_simp

theorem isHilbertPV_difference [CompleteSpace E] {f : ℝ → E} (hf : ContDiff ℝ 1 f) (hi : Integrable f) :
    IsHilbertPV f (fun x => (2 * Real.pi)⁻¹ • ∫ y, hilbertDifference f x y) := by
  intro x
  have h := (tendsto_integral_hilbert_cutoff (integrable_hilbertDifference hf hi x) 0).const_smul
    (2 * Real.pi)⁻¹
  simp only [zero_sub, abs_neg] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hilbertTrunc_eq_difference hi hε x).symm

end Difference

def hilbertSpectralCutoff (R : ℝ) : ℝ → ℂ :=
  (Ioc (-R) 0).indicator (fun _ => Complex.I) +
    (Ioc 0 R).indicator (fun _ => -Complex.I)

theorem integrable_hilbertSpectralCutoff (R : ℝ) : Integrable (hilbertSpectralCutoff R) := by
  apply Integrable.add <;> apply (integrable_indicator_iff measurableSet_Ioc).2 <;>
    exact integrableOn_const (measure_Ioc_lt_top.ne)

theorem fourierInv_interval {a b : ℝ} (hab : a ≤ b) (c : ℂ) (x : ℝ) :
    𝓕⁻ ((Ioc a b).indicator (fun _ : ℝ => c)) x =
      (∫ ξ in a..b, Complex.exp ((2 * Real.pi * x * Complex.I) * ξ)) * c := by
  rw [Real.fourierInv_eq']
  simp only [smul_eq_mul]
  have heq : (fun v : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) *
      (Ioc a b).indicator (fun _ => c) v) =
      (Ioc a b).indicator (fun v => Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) * c) := by
    ext v; by_cases hv : v ∈ Ioc a b <;> simp [hv]
  rw [heq]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro ξ _
  simp only [RCLike.inner_apply, conj_trivial, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring_nf

theorem fourierInv_hilbertSpectralCutoff {R : ℝ} (hR : 0 ≤ R) {x : ℝ} (hx : x ≠ 0) :
    𝓕⁻ (hilbertSpectralCutoff R) x =
      ((1 - Real.cos (2 * Real.pi * R * x)) / (Real.pi * x) : ℝ) := by
  have hi (a b : ℝ) (c : ℂ) : Integrable ((Ioc a b).indicator (fun _ : ℝ => c)) :=
    (integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const measure_Ioc_lt_top.ne)
  have hadd : 𝓕⁻ (hilbertSpectralCutoff R) =
      fun x => 𝓕⁻ ((Ioc (-R) 0).indicator (fun _ : ℝ => Complex.I)) x +
        𝓕⁻ ((Ioc 0 R).indicator (fun _ : ℝ => -Complex.I)) x := by
    exact VectorFourier.fourierIntegral_add Real.continuous_fourierChar
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2))
      (hi _ _ _) (hi _ _ _)
  rw [hadd]
  dsimp only
  rw [fourierInv_interval (neg_nonpos.mpr hR), fourierInv_interval hR]
  have hc : (2 * Real.pi * x * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Complex.ofReal_ne_zero.mpr hx)) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc, integral_exp_mul_complex hc]
  have hp : (2 * Real.pi * x * Complex.I : ℂ) * R =
      (2 * Real.pi * R * x : ℝ) * Complex.I := by push_cast; ring
  have hn : (2 * Real.pi * x * Complex.I : ℂ) * (-R : ℝ) =
      (-(2 * Real.pi * R * x : ℝ)) * Complex.I := by push_cast; ring
  rw [hp, hn]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  field_simp
  ring_nf

theorem fourierInv_mul_fourier {m f : ℝ → ℂ} (hm : Integrable m) (hf : Integrable f) (x : ℝ) :
    𝓕⁻ (fun ξ => m ξ * 𝓕 f ξ) x = ∫ y, f y * 𝓕⁻ m (x - y) := by
  let b : ℝ → ℂ := fun ξ => 𝐞 (ξ * x) • m ξ
  have hb : Integrable b := by
    simpa [b, mul_comm] using (Real.fourierIntegral_convergent_iff (-x)).2 hm
  have hbF (y : ℝ) : 𝓕 b y = 𝓕⁻ m (x - y) := by
    rw [Real.fourier_eq, Real.fourierInv_eq]
    apply integral_congr_ae
    exact .of_forall fun ξ => by
      dsimp [b]
      rw [← mul_smul, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [conj_trivial]
      ring
  calc
    _ = ∫ ξ, 𝓕 f ξ * b ξ := by
      rw [Real.fourierInv_eq]
      apply integral_congr_ae
      exact .of_forall fun ξ => by
        simp only [b, RCLike.inner_apply, conj_trivial, Circle.smul_def, smul_eq_mul]
        ring_nf
    _ = ∫ y, f y * 𝓕 b y := integral_fourier_mul_eq hf hb
    _ = _ := by simp_rw [hbF]

def hilbertSpectralKernel (R y : ℝ) : ℝ :=
  (1 - Real.cos (2 * Real.pi * R * y)) / (Real.pi * y)

theorem hilbertSpectralKernel_neg (R y : ℝ) :
    hilbertSpectralKernel R (-y) = -hilbertSpectralKernel R y := by
  simp [hilbertSpectralKernel, div_neg]

theorem fourierInv_hilbertSpectralCutoff_mul {f : ℝ → ℂ} (hf : Integrable f)
    {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    𝓕⁻ (fun ξ => hilbertSpectralCutoff R ξ * 𝓕 f ξ) x =
      (2 * Real.pi)⁻¹ • ∫ y, (1 - Real.cos (2 * Real.pi * R * y)) •
        hilbertDifference f x y := by
  let m := hilbertSpectralCutoff R
  let K := hilbertSpectralKernel R
  have hm : Integrable m := integrable_hilbertSpectralCutoff R
  have hK : (fun y => 𝓕⁻ m y) =ᵐ[volume] (fun y => (K y : ℂ)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
    exact fourierInv_hilbertSpectralCutoff hR hy
  have hKmeas : AEStronglyMeasurable (fun y => 𝓕⁻ m y) volume :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2)) hm).aestronglyMeasurable
  have hq : Integrable (fun y => (K y : ℂ) * f (x - y)) := by
    have h := (hf.comp_sub_left x).bdd_mul hKmeas
      (.of_forall fun y => VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (-innerₗ ℝ) m y)
    exact h.congr (hK.mul (.refl _ _))
  rw [fourierInv_mul_fourier hm hf]
  have hchange : (∫ y, f y * 𝓕⁻ m (x - y)) =
      ∫ y, (K y : ℂ) * f (x - y) := by
    rw [← integral_sub_left_eq_self _ volume x]
    apply integral_congr_ae
    filter_upwards [hK] with y hy
    simp [sub_sub_cancel, hy, mul_comm]
  rw [hchange]
  have heq : (fun y => (K y : ℂ) * (f (x - y) - f (x + y))) =
      fun y => (K y : ℂ) * f (x - y) + (K (-y) : ℂ) * f (x - (-y)) := by
    funext y
    simp [K, hilbertSpectralKernel_neg, sub_eq_add_neg]
    ring
  have hs : (∫ y, (K y : ℂ) * (f (x - y) - f (x + y))) =
      (2 : ℝ) • ∫ y, (K y : ℂ) * f (x - y) := by
    rw [heq, integral_add hq hq.comp_neg,
      integral_neg_eq_self (fun y : ℝ => (K y : ℂ) * f (x - y)), two_smul]
  have hi : (∫ y, (K y : ℂ) * (f (x - y) - f (x + y))) =
      Real.pi⁻¹ • ∫ y, (1 - Real.cos (2 * Real.pi * R * y)) • hilbertDifference f x y := by
    rw [← integral_smul]
    apply integral_congr_ae
    exact .of_forall fun y => by
      simp [K, hilbertSpectralKernel, hilbertDifference, Complex.real_smul, div_eq_mul_inv]
      ring
  rw [hs] at hi
  have h := congrArg (fun z : ℂ => (2 : ℝ)⁻¹ • z) hi
  simpa only [smul_smul, inv_mul_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num),
    one_smul, mul_inv] using h

theorem integral_cos_smul {d : ℝ → ℂ} (hd : Integrable d) (R : ℝ) :
    (∫ y, Real.cos (2 * Real.pi * R * y) • d y) =
      (2 : ℝ)⁻¹ • (𝓕 d R + 𝓕 d (-R)) := by
  rw [Real.fourier_eq, Real.fourier_eq,
    ← integral_add ((Real.fourierIntegral_convergent_iff R).2 hd)
      ((Real.fourierIntegral_convergent_iff (-R)).2 hd), ← integral_smul]
  apply integral_congr_ae
  exact .of_forall fun y => by
    simp only [RCLike.inner_apply, conj_trivial, Circle.smul_def, Real.fourierChar_apply,
      Complex.real_smul, smul_eq_mul]
    simp only [mul_neg, neg_mul, neg_neg]
    simp only [Complex.ofReal_neg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring_nf

theorem tendsto_integral_cos_smul {d : ℝ → ℂ} (hd : Integrable d) :
    Tendsto (fun R : ℝ => ∫ y, Real.cos (2 * Real.pi * R * y) • d y) atTop (𝓝 0) := by
  have hp := (Real.zero_at_infty_fourier d).mono_left atTop_le_cocompact
  have hn := ((Real.zero_at_infty_fourier d).mono_left atBot_le_cocompact).comp
    tendsto_neg_atTop_atBot
  simpa only [Function.comp_def, add_zero, smul_zero, ← integral_cos_smul hd] using
    (hp.add hn).const_smul (2 : ℝ)⁻¹

theorem tendsto_fourierInv_hilbertSpectralCutoff {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hi : Integrable f) (x : ℝ) :
    Tendsto (fun R : ℝ => 𝓕⁻ (fun ξ => hilbertSpectralCutoff R ξ * 𝓕 f ξ) x)
      atTop (𝓝 ((2 * Real.pi)⁻¹ • ∫ y, hilbertDifference f x y)) := by
  have hd := integrable_hilbertDifference hf hi x
  have h := ((tendsto_const_nhds (x := ∫ y, hilbertDifference f x y)).sub
    (tendsto_integral_cos_smul hd)).const_smul
    (2 * Real.pi)⁻¹
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [fourierInv_hilbertSpectralCutoff_mul hi hR]
  congr 1
  simp only [sub_smul, one_smul]
  rw [integral_sub hd]
  apply hd.bdd_smul (𝕜 := ℝ) 1
  · exact (by fun_prop : Continuous (fun y : ℝ => Real.cos (2 * Real.pi * R * y))).aestronglyMeasurable
  · exact .of_forall fun y => by simpa using Real.abs_cos_le_one (2 * Real.pi * R * y)

def l2FrequencyCutoff (u : ComplexL2) (R : ℝ) : ComplexL2 :=
  ((Lp.memLp u).indicator measurableSet_Ioc).toLp ((Ioc (-R) R).indicator u)

theorem l2FrequencyCutoff_coeFn (u : ComplexL2) (R : ℝ) :
    l2FrequencyCutoff u R =ᵐ[volume] (Ioc (-R) R).indicator u :=
  MemLp.coeFn_toLp _

theorem tendsto_l2FrequencyCutoff (u : ComplexL2) :
    Tendsto (fun n : ℕ => l2FrequencyCutoff u n) atTop (𝓝 u) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have heq (n : ℕ) : eLpNorm (⇑(l2FrequencyCutoff u n) - ⇑u) 2 volume =
      eLpNorm ((Ioc (-(n : ℝ)) n).indicator u - ⇑u) 2 volume :=
    eLpNorm_congr_ae ((l2FrequencyCutoff_coeFn u n).sub .rfl)
  simp_rw [heq, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have hd : Tendsto (fun n : ℕ => ∫⁻ y,
      ‖(Ioc (-(n : ℝ)) n).indicator u y - u y‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    have hfin : (∫⁻ y, ‖u y‖ₑ ^ (2 : ℝ)) ≠ ⊤ := by
      simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (Lp.memLp u).2).ne
    convert tendsto_lintegral_of_dominated_convergence'
      (f := fun _ : ℝ => (0 : ℝ≥0∞)) (fun y => ‖u y‖ₑ ^ (2 : ℝ)) ?_ ?_ hfin ?_ using 1
    · simp only [lintegral_zero]
    · intro n
      exact (((Lp.aestronglyMeasurable u).indicator measurableSet_Ioc).sub
        (Lp.aestronglyMeasurable u)).enorm.pow_const _
    · intro n
      exact .of_forall fun y => by
        by_cases hy : y ∈ Ioc (-(n : ℝ)) n <;> simp [hy]
    · exact .of_forall fun y => by
        apply tendsto_const_nhds.congr'
        filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
          (eventually_gt_atTop |y|)] with n hn
        have hy : y ∈ Ioc (-(n : ℝ)) n := by
          constructor <;> linarith [le_abs_self y, neg_abs_le y]
        simp [hy]
  have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hd
  simpa [Function.comp_def] using h

theorem hilbertSpectralCutoff_eq_indicator {R ξ : ℝ} (hR : 0 ≤ R) (hξ : ξ ≠ 0) :
    hilbertSpectralCutoff R ξ = (Ioc (-R) R).indicator hilbertSymbol ξ := by
  rcases hξ.lt_or_gt with h | h
  · have hle : ξ ≤ R := le_trans h.le hR
    simp [hilbertSpectralCutoff, hilbertSymbol, Set.indicator, h, hle, h.le, h.not_gt]
  · have hleft : -R < ξ := lt_of_le_of_lt (neg_nonpos.mpr hR) h
    simp [hilbertSpectralCutoff, hilbertSymbol, Set.indicator, h, hleft, h.not_gt, h.not_ge]

theorem fourierInv_l2FrequencyCutoff_ae {f : ℝ → ℂ} (hi : Integrable f) (h₂ : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) :
    (𝓕⁻ (l2FrequencyCutoff (hilbertMultiplier (𝓕 (h₂.toLp f))) R) : ComplexL2) =ᵐ[volume]
      𝓕⁻ (fun ξ => hilbertSpectralCutoff R ξ * 𝓕 f ξ) := by
  let u : ComplexL2 := hilbertMultiplier (𝓕 (h₂.toLp f))
  have hq : Integrable ((Ioc (-R) R).indicator u) := by
    apply (integrable_indicator_iff measurableSet_Ioc).2
    exact integrableOn_Lp_of_measure_ne_top u (by norm_num) measure_Ioc_lt_top.ne
  have heq : (Ioc (-R) R).indicator u =ᵐ[volume]
      (fun ξ => hilbertSpectralCutoff R ξ * 𝓕 f ξ) := by
    filter_upwards [hilbertMultiplier_coeFn (𝓕 (h₂.toLp f)), fourier_toLp_ae hi h₂,
      volume.ae_ne (0 : ℝ)] with ξ hu hf hξ
    rw [hilbertSpectralCutoff_eq_indicator hR hξ]
    by_cases hmem : ξ ∈ Ioc (-R) R
    · simp [hmem, u, hu, hf]
    · simp [hmem]
  exact (fourierInv_toLp_ae hq ((Lp.memLp u).indicator measurableSet_Ioc)).trans
    (.of_forall (Real.fourierInv_congr_ae heq))

/-- Scalar principal values coincide almost everywhere with the Plancherel multiplier. -/
theorem scalar_pv_fourier_ae {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hi : Integrable f)
    (h₂ : MemLp f 2) : IsHilbertPVAe f (hilbertL2 (h₂.toLp f)) := by
  let u : ComplexL2 := hilbertMultiplier (𝓕 (h₂.toLp f))
  let v : ℕ → ComplexL2 := fun n => 𝓕⁻ (l2FrequencyCutoff u n)
  have hv : Tendsto v atTop (𝓝 (hilbertL2 (h₂.toLp f))) := by
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous.continuousAt.tendsto.comp
      (tendsto_l2FrequencyCutoff u)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have heq : ∀ n : ℕ, v n =ᵐ[volume]
      𝓕⁻ (fun ξ => hilbertSpectralCutoff n ξ * 𝓕 f ξ) := fun n =>
    fourierInv_l2FrequencyCutoff_ae hi h₂ (Nat.cast_nonneg n)
  have hPV := isHilbertPV_difference hf hi
  filter_upwards [hae, ae_all_iff.mpr heq] with x hx hxeq
  have ht := (tendsto_fourierInv_hilbertSpectralCutoff hf hi x).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hns.tendsto_atTop)
  have hvx : Tendsto (fun n => v (ns n) x) atTop
      (𝓝 ((2 * Real.pi)⁻¹ • ∫ y, hilbertDifference f x y)) := by
    apply ht.congr
    intro n
    exact (hxeq (ns n)).symm
  have hvalue := tendsto_nhds_unique hvx hx
  rw [← hvalue]
  exact hPV x

end HilbertUMD
