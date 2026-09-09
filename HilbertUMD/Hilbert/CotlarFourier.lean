import HilbertUMD.Hilbert.HilbertPVFourier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Function.Holder

/-! The polarized Cotlar identity for the Fourier Hilbert transform. -/

noncomputable section
open MeasureTheory Filter FourierTransform Convolution
open scoped ENNReal NNReal Topology SchwartzMap

namespace HilbertUMD.CotlarFourier

/-- The algebraic cancellation behind the polarized product identity. -/
theorem symbol_identity (a b : ℝ) :
    hilbertSymbol (a + b) * (hilbertSymbol a + hilbertSymbol b) =
      hilbertSymbol a * hilbertSymbol b - 1 := by
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · simp [hilbertSymbol, ha, hb, add_neg ha hb, mul_add, Complex.I_mul_I, sub_eq_add_neg]
  · simp [hilbertSymbol, ha, hb]
  · simp [hilbertSymbol, ha, hb]
  · simp [hilbertSymbol, ha, hb, not_lt.mpr (add_nonneg (not_lt.mp ha) (not_lt.mp hb)),
      mul_add, Complex.I_mul_I, sub_eq_add_neg]

def symbolMul (f : ℝ → ℂ) : ℝ → ℂ := fun x => hilbertSymbol x * f x

theorem symbolMul_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (symbolMul f) := by
  apply hf.congr' (measurable_hilbertSymbol.aestronglyMeasurable.mul hf.1)
  exact .of_forall fun x => by simp

theorem symbolMul_memLp {f : ℝ → ℂ} {p : ℝ≥0∞} (hf : MemLp f p) :
    MemLp (symbolMul f) p := by
  apply hf.congr_norm (measurable_hilbertSymbol.aestronglyMeasurable.mul hf.1)
  exact .of_forall fun x => by simp

def conv (f g : ℝ → ℂ) : ℝ → ℂ := f ⋆[ContinuousLinearMap.mul ℂ ℂ] g

theorem conv_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (conv f g) := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg

theorem conv_integrand {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) (x : ℝ) :
    Integrable (fun y => f y * g (x-y)) :=
  hf.integrable_mul (hg.comp_measurePreserving (volume.measurePreserving_sub_left x))

theorem symbolMul_conv {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    symbolMul (conv f (symbolMul g) + conv (symbolMul f) g) =
      conv (symbolMul f) (symbolMul g) - conv f g := by
  funext x
  have hfg := conv_integrand hf (symbolMul_memLp hg) x
  have hgf := conv_integrand (symbolMul_memLp hf) hg x
  have hHH := conv_integrand (symbolMul_memLp hf) (symbolMul_memLp hg) x
  have huv := conv_integrand hf hg x
  simp only [symbolMul, conv, convolution_def, ContinuousLinearMap.mul_apply',
    Pi.add_apply, Pi.sub_apply] at *
  rw [← integral_add hfg hgf, ← integral_sub hHH huv, ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun y => by
    have h := symbol_identity y (x-y)
    rw [add_sub_cancel] at h
    calc
      _ = (hilbertSymbol x * (hilbertSymbol y + hilbertSymbol (x-y))) *
          (f y * g (x-y)) := by ring
      _ = _ := by rw [h]; ring

theorem inverse_conv {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕⁻ (conv f g) x = 𝓕⁻ f x * 𝓕⁻ g x := by
  simpa only [conv, Real.fourierInv_eq_fourier_neg] using
    Real.fourier_mul_convolution_eq hf hg (-x)

/-- Integrable, bounded frequency data. This class is closed under all
operations used in the identity and contains every Schwartz function. -/
structure Data (f : ℝ → ℂ) : Prop where
  integrable : Integrable f
  bound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

theorem Data.memLp {f : ℝ → ℂ} (hf : Data f) : MemLp f 2 := by
  obtain ⟨C, hC⟩ := hf.bound
  apply (memLp_two_iff_integrable_sq_norm hf.integrable.1).mpr
  apply (hf.integrable.norm.const_mul C).mono (hf.integrable.1.norm.pow 2)
  exact .of_forall fun x => by
    change ‖‖f x‖ ^ 2‖ ≤ ‖C * ‖f x‖‖
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      ‖f x‖ ^ 2 ≤ C * ‖f x‖ := by nlinarith [hC x, norm_nonneg (f x)]
      _ ≤ ‖C * ‖f x‖‖ := le_abs_self _

theorem Data.schwartz (f : SchwartzMap ℝ ℂ) : Data f :=
  ⟨f.integrable, ⟨SchwartzMap.seminorm ℝ 0 0 f, SchwartzMap.norm_le_seminorm ℝ f⟩⟩

theorem Data.symbolMul {f : ℝ → ℂ} (hf : Data f) : Data (symbolMul f) := by
  obtain ⟨C, hC⟩ := hf.bound
  exact ⟨symbolMul_integrable hf.integrable,
    ⟨C, fun x => by simpa [CotlarFourier.symbolMul] using hC x⟩⟩

theorem Data.add {f g : ℝ → ℂ} (hf : Data f) (hg : Data g) : Data (f + g) := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨D, hD⟩ := hg.bound
  exact ⟨hf.integrable.add hg.integrable,
    ⟨C+D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩⟩

theorem Data.sub {f g : ℝ → ℂ} (hf : Data f) (hg : Data g) : Data (f - g) := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨D, hD⟩ := hg.bound
  exact ⟨hf.integrable.sub hg.integrable,
    ⟨C+D, fun x => (norm_sub_le _ _).trans (add_le_add (hC x) (hD x))⟩⟩

theorem Data.conv {f g : ℝ → ℂ} (hf : Data f) (hg : Data g) : Data (conv f g) := by
  obtain ⟨C, hC⟩ := hg.bound
  refine ⟨conv_integrable hf.integrable hg.integrable, ⟨(∫ y, ‖f y‖) * C, ?_⟩⟩
  intro x
  change ‖∫ y, f y * g (x-y)‖ ≤ _
  calc
    _ ≤ ∫ y, ‖f y * g (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖f y‖ * C := integral_mono
      (conv_integrand hf.memLp hg.memLp x).norm (hf.integrable.norm.mul_const C)
      (fun y => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
    _ = _ := integral_mul_const C _

def inverse (f : ℝ → ℂ) (hf : Data f) : ComplexL2 := 𝓕⁻ (hf.memLp.toLp f)

theorem inverse_ae {f : ℝ → ℂ} (hf : Data f) :
    inverse f hf =ᵐ[volume] 𝓕⁻ f := fourierInv_toLp_ae hf.integrable hf.memLp

theorem inverse_add {f g : ℝ → ℂ} (hf : Data f) (hg : Data g) :
    inverse (f+g) (hf.add hg) = inverse f hf + inverse g hg := by
  simp only [inverse, ← fourierInv_add]
  congr 1

theorem inverse_sub {f g : ℝ → ℂ} (hf : Data f) (hg : Data g) :
    inverse (f-g) (hf.sub hg) = inverse f hf - inverse g hg := by
  change 𝓕⁻ ((hf.sub hg).memLp.toLp (f-g)) = _
  rw [show (hf.sub hg).memLp.toLp (f-g) = hf.memLp.toLp f - hg.memLp.toLp g from
    MemLp.toLp_sub hf.memLp hg.memLp]
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.map_sub _ _

theorem inverse_symbolMul {f : ℝ → ℂ} (hf : Data f) :
    inverse (symbolMul f) hf.symbolMul = hilbertL2 (inverse f hf) := by
  have hm : hf.symbolMul.memLp.toLp (symbolMul f) = hilbertMultiplier (hf.memLp.toLp f) := by
    apply Lp.ext
    filter_upwards [hf.symbolMul.memLp.coeFn_toLp,
      hilbertMultiplier_coeFn (hf.memLp.toLp f), hf.memLp.coeFn_toLp] with x h1 h2 h3
    simp only [symbolMul] at h1
    rw [h1, h2, h3]
  simp only [inverse, hm]
  change _ = (Lp.fourierTransformₗᵢ ℝ ℂ).symm
    (hilbertMultiplier ((Lp.fourierTransformₗᵢ ℝ ℂ) ((Lp.fourierTransformₗᵢ ℝ ℂ).symm _)))
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem inverse_conv_ae {f g : ℝ → ℂ} (hf : Data f) (hg : Data g) :
    inverse (conv f g) (hf.conv hg) =ᵐ[volume]
      fun x => inverse f hf x * inverse g hg x := by
  filter_upwards [inverse_ae (hf.conv hg), inverse_ae hf, inverse_ae hg] with x h1 h2 h3
  rw [h1, h2, h3, inverse_conv hf.integrable hg.integrable]

/-- Cotlar's identity in L2 for inverse transforms of bounded integrable data.
The two product expressions belong to L2, as witnessed by the construction. -/
theorem cotlar_inverse {f g : ℝ → ℂ} (hf : Data f) (hg : Data g) :
    ∃ W : ComplexL2,
      W =ᵐ[volume] (fun x => inverse f hf x * hilbertL2 (inverse g hg) x +
        inverse g hg x * hilbertL2 (inverse f hf) x) ∧
      hilbertL2 W =ᵐ[volume] (fun x => hilbertL2 (inverse f hf) x *
        hilbertL2 (inverse g hg) x - inverse f hf x * inverse g hg x) := by
  let a := conv f (symbolMul g) + conv (symbolMul f) g
  have ha : Data a := (hf.conv hg.symbolMul).add (hf.symbolMul.conv hg)
  refine ⟨inverse a ha, ?_, ?_⟩
  · rw [inverse_add (hf.conv hg.symbolMul) (hf.symbolMul.conv hg)]
    filter_upwards [Lp.coeFn_add (inverse (conv f (symbolMul g)) (hf.conv hg.symbolMul))
      (inverse (conv (symbolMul f) g) (hf.symbolMul.conv hg)),
      inverse_conv_ae hf hg.symbolMul, inverse_conv_ae hf.symbolMul hg] with x hx h1 h2
    simp only [Pi.add_apply] at hx
    rw [hx, h1, h2, inverse_symbolMul hg, inverse_symbolMul hf]
    ring
  · rw [← inverse_symbolMul ha]
    have he : symbolMul a = conv (symbolMul f) (symbolMul g) - conv f g :=
      symbolMul_conv hf.memLp hg.memLp
    have hb := (hf.symbolMul.conv hg.symbolMul).sub (hf.conv hg)
    have hi : inverse (symbolMul a) ha.symbolMul =
        inverse (conv (symbolMul f) (symbolMul g) - conv f g) hb := by
      congr 1
    rw [hi, inverse_sub (hf.symbolMul.conv hg.symbolMul) (hf.conv hg)]
    filter_upwards [Lp.coeFn_sub (inverse (conv (symbolMul f) (symbolMul g)) (hf.symbolMul.conv hg.symbolMul))
      (inverse (conv f g) (hf.conv hg)), inverse_conv_ae hf.symbolMul hg.symbolMul,
      inverse_conv_ae hf hg] with x hx h1 h2
    simp only [Pi.sub_apply] at hx
    rw [hx, h1, h2, inverse_symbolMul hf, inverse_symbolMul hg]

theorem inverse_fourier_schwartz (u : SchwartzMap ℝ ℂ) :
    inverse (⇑(𝓕 u : SchwartzMap ℝ ℂ)) (Data.schwartz (𝓕 u)) = u.toLp 2 := by
  change 𝓕⁻ ((𝓕 u).toLp 2) = u.toLp 2
  rw [← SchwartzMap.toLp_fourier_eq, fourierInv_fourier_eq]

theorem complex_schwartz (u v : SchwartzMap ℝ ℂ) :
    ∃ W : ComplexL2,
      W =ᵐ[volume] (fun x => u x * hilbertL2 (v.toLp 2) x +
        v x * hilbertL2 (u.toLp 2) x) ∧
      hilbertL2 W =ᵐ[volume] (fun x => hilbertL2 (u.toLp 2) x *
        hilbertL2 (v.toLp 2) x - u x * v x) := by
  obtain ⟨W, hW, hHW⟩ := cotlar_inverse (Data.schwartz (𝓕 u)) (Data.schwartz (𝓕 v))
  rw [inverse_fourier_schwartz, inverse_fourier_schwartz] at hW hHW
  refine ⟨W, ?_, ?_⟩
  · filter_upwards [hW, u.coeFn_toLp 2, v.coeFn_toLp 2] with x hx hu hv
    simpa only [hu, hv] using hx
  · filter_upwards [hHW, u.coeFn_toLp 2, v.coeFn_toLp 2] with x hx hu hv
    simpa only [hu, hv] using hx

theorem ofReal_schwartz_toLp (u : SchwartzMap ℝ ℝ) :
    (u.postcompCLM Complex.ofRealCLM).toLp 2 = l2OfReal (u.toLp 2) := by
  apply Lp.ext
  filter_upwards [(u.postcompCLM Complex.ofRealCLM).coeFn_toLp 2,
    l2OfReal_coeFn (u.toLp 2), u.coeFn_toLp 2] with x hc hr hu
  simp [hc, hr, hu, SchwartzMap.postcompCLM_apply]

/-- The real Schwartz version, with products and their Hilbert transforms
represented in L2. No principal-value existence theorem is used here. -/
theorem real_schwartz (u v : SchwartzMap ℝ ℝ) :
    ∃ W : RealL2,
      W =ᵐ[volume] (fun x => u x * realHilbertL2 (v.toLp 2) x +
        v x * realHilbertL2 (u.toLp 2) x) ∧
      realHilbertL2 W =ᵐ[volume] (fun x => realHilbertL2 (u.toLp 2) x *
        realHilbertL2 (v.toLp 2) x - u x * v x) := by
  obtain ⟨W, hW, hHW⟩ := complex_schwartz
    (u.postcompCLM Complex.ofRealCLM) (v.postcompCLM Complex.ofRealCLM)
  have hc (s : SchwartzMap ℝ ℝ) :
      hilbertL2 ((s.postcompCLM Complex.ofRealCLM).toLp 2) =ᵐ[volume]
        fun x => (realHilbertL2 (s.toLp 2) x : ℂ) := by
    rw [ofReal_schwartz_toLp, ← ofReal_realHilbertL2]
    exact l2OfReal_coeFn _
  have hW' : W =ᵐ[volume] fun x =>
      ((u x * realHilbertL2 (v.toLp 2) x + v x * realHilbertL2 (u.toLp 2) x : ℝ) : ℂ) := by
    filter_upwards [hW, hc u, hc v] with x hw hu hv
    rw [hu, hv] at hw
    simpa only [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
      Complex.ofReal_add, Complex.ofReal_mul] using hw
  have hHW' : hilbertL2 W =ᵐ[volume] fun x =>
      ((realHilbertL2 (u.toLp 2) x * realHilbertL2 (v.toLp 2) x - u x * v x : ℝ) : ℂ) := by
    filter_upwards [hHW, hc u, hc v] with x hw hu hv
    rw [hu, hv] at hw
    simpa only [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
      Complex.ofReal_sub, Complex.ofReal_mul] using hw
  have hwreal : l2OfReal (l2Re W) = W := by
    apply Lp.ext
    filter_upwards [l2OfReal_coeFn (l2Re W), l2Re_coeFn W, hW'] with x ho hr hw
    rw [ho, hr, hw, Complex.ofReal_re]
  have hreal : realHilbertL2 (l2Re W) = l2Re (hilbertL2 W) := by
    change l2Re (hilbertL2 (l2OfReal (l2Re W))) = _
    rw [hwreal]
  refine ⟨l2Re W, ?_, ?_⟩
  · filter_upwards [l2Re_coeFn W, hW'] with x hr hw
    rw [hr, hw, Complex.ofReal_re]
  · rw [hreal]
    filter_upwards [l2Re_coeFn (hilbertL2 W), hHW'] with x hr hw
    rw [hr, hw, Complex.ofReal_re]

end HilbertUMD.CotlarFourier
