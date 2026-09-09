import HilbertUMD.Analysis.CubicLp
import Mathlib.Analysis.Complex.Basic

/-! Actual complexification on finite-coordinate Lp spaces. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD.CubicLp

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S)

abbrev ComplexSpace (p : ℝ≥0∞) := Lp (ι → ℂ) p μ

def reVec : (ι → ℂ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => Complex.reCLM.comp
    ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).restrictScalars ℝ))

def imVec : (ι → ℂ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => Complex.imCLM.comp
    ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).restrictScalars ℝ))

def ofRealVec : (ι → ℝ) →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

omit [Fintype ι] in
@[simp] theorem reVec_apply (x : ι → ℂ) (i : ι) : reVec x i = (x i).re := rfl
omit [Fintype ι] in
@[simp] theorem imVec_apply (x : ι → ℂ) (i : ι) : imVec x i = (x i).im := rfl
omit [Fintype ι] in
@[simp] theorem ofRealVec_apply (x : ι → ℝ) (i : ι) : ofRealVec x i = (x i : ℂ) := rfl

def reLp (p : ℝ≥0∞) [Fact (1 ≤ p)] : ComplexSpace (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p :=
  (reVec (ι := ι)).compLpL p μ

def imLp (p : ℝ≥0∞) [Fact (1 ≤ p)] : ComplexSpace (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p :=
  (imVec (ι := ι)).compLpL p μ

def ofRealLp (p : ℝ≥0∞) [Fact (1 ≤ p)] : Space (ι := ι) μ p →L[ℝ] ComplexSpace (ι := ι) μ p :=
  (ofRealVec (ι := ι)).compLpL p μ

def complexToL1 : (ι → ℂ) →L[ℂ] PiLp 1 (fun _ : ι => ℂ) :=
  (WithLp.linearEquiv 1 ℂ (ι → ℂ)).symm.toLinearMap.toContinuousLinearMap

def complexFromL1 : PiLp 1 (fun _ : ι => ℂ) →L[ℂ] (ι → ℂ) :=
  (WithLp.linearEquiv 1 ℂ (ι → ℂ)).toLinearMap.toContinuousLinearMap

def complexL1Norm (p : ℝ≥0∞) [Fact (1 ≤ p)] : Seminorm ℂ (ComplexSpace (ι := ι) μ p) :=
  (normSeminorm ℂ (Lp (PiLp 1 (fun _ : ι => ℂ)) p μ)).comp
    ((complexToL1 (ι := ι)).compLpL p μ).toLinearMap

theorem norm_complexToL1 (x : ι → ℂ) : ‖complexToL1 x‖ = ∑ i, ‖x i‖ :=
  PiLp.norm_eq_of_L1 _

theorem complexL1Norm_fromL1 {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp (PiLp 1 (fun _ : ι => ℂ)) p μ) :
    complexL1Norm μ p ((complexFromL1 (ι := ι)).compLpL p μ f) = ‖f‖ := by
  change ‖(complexToL1 (ι := ι)).compLpL p μ
    ((complexFromL1 (ι := ι)).compLpL p μ f)‖ = ‖f‖
  congr 1
  apply Lp.ext
  filter_upwards [(complexToL1 (ι := ι)).coeFn_compLpL ((complexFromL1 (ι := ι)).compLpL p μ f),
    (complexFromL1 (ι := ι)).coeFn_compLpL f] with x ht hf
  rw [ht, hf]
  rfl

def mixedComplexRealization {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (V : ComplexSpace (ι := ι) μ p →L[ℂ] ComplexSpace (ι := ι) μ p) :
    Lp (PiLp 1 (fun _ : ι => ℂ)) p μ →L[ℂ] ComplexSpace (ι := ι) μ p :=
  V.comp ((complexFromL1 (ι := ι)).compLpL p μ)

theorem norm_ofRealVec (x : ι → ℝ) : ‖ofRealVec x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    simpa only [ofRealVec_apply, Complex.norm_real] using norm_le_pi_norm x i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (ofRealVec x))).mpr
    intro i
    simpa only [ofRealVec_apply, Complex.norm_real] using norm_le_pi_norm (ofRealVec x) i

theorem norm_ofRealLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    ‖ofRealLp μ p f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [(ofRealVec (ι := ι)).coeFn_compLpL f] with x hx
  change (ofRealLp μ p f) x = ofRealVec (f x) at hx
  rw [hx, norm_ofRealVec]

theorem l1Norm_reLp_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : ComplexSpace (ι := ι) μ p) :
    l1Norm μ p (reLp μ p f) ≤ complexL1Norm μ p f := by
  change ‖(toL1 (ι := ι)).compLpL p μ (reLp μ p f)‖ ≤
    ‖(complexToL1 (ι := ι)).compLpL p μ f‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(toL1 (ι := ι)).coeFn_compLpL (reLp μ p f),
    (reVec (ι := ι)).coeFn_compLpL f, (complexToL1 (ι := ι)).coeFn_compLpL f] with x hL hr hR
  change (reLp μ p f) x = reVec (f x) at hr
  rw [hL, hr, hR, norm_toL1, norm_complexToL1]
  change (∑ i, |(f x i).re|) ≤ ∑ i, ‖f x i‖
  exact Finset.sum_le_sum (fun i _ => Complex.abs_re_le_norm (f x i))

theorem l1Norm_imLp_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : ComplexSpace (ι := ι) μ p) :
    l1Norm μ p (imLp μ p f) ≤ complexL1Norm μ p f := by
  change ‖(toL1 (ι := ι)).compLpL p μ (imLp μ p f)‖ ≤
    ‖(complexToL1 (ι := ι)).compLpL p μ f‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(toL1 (ι := ι)).coeFn_compLpL (imLp μ p f),
    (imVec (ι := ι)).coeFn_compLpL f, (complexToL1 (ι := ι)).coeFn_compLpL f] with x hL hi hR
  change (imLp μ p f) x = imVec (f x) at hi
  rw [hL, hi, hR, norm_toL1, norm_complexToL1]
  change (∑ i, |(f x i).im|) ≤ ∑ i, ‖f x i‖
  exact Finset.sum_le_sum (fun i _ => Complex.abs_im_le_norm (f x i))

/-- Real-linear construction; complex linearity is proved below. -/
def complexifyReal {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (V : Space (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p) :
    ComplexSpace (ι := ι) μ p →L[ℝ] ComplexSpace (ι := ι) μ p :=
  (ofRealLp μ p).comp (V.comp (reLp μ p)) +
    Complex.I • (ofRealLp μ p).comp (V.comp (imLp μ p))

theorem complexifyReal_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (V : Space (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p) (f : ComplexSpace (ι := ι) μ p) :
    complexifyReal μ V f = ofRealLp μ p (V (reLp μ p f)) +
      Complex.I • ofRealLp μ p (V (imLp μ p f)) := rfl

theorem reLp_I {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ComplexSpace (ι := ι) μ p) :
    reLp μ p (Complex.I • f) = -imLp μ p f := by
  apply Lp.ext
  filter_upwards [(reVec (ι := ι)).coeFn_compLpL (Complex.I • f), Lp.coeFn_smul Complex.I f,
    (imVec (ι := ι)).coeFn_compLpL f, Lp.coeFn_neg (imLp μ p f)] with x hr hs hi hn
  change (reLp μ p (Complex.I • f)) x = reVec ((Complex.I • f) x) at hr
  change (imLp μ p f) x = imVec (f x) at hi
  rw [hr, hn]
  simp only [Pi.neg_apply]
  rw [hi, hs]
  ext i
  simp [reVec_apply, imVec_apply, Pi.smul_apply, smul_eq_mul]

theorem imLp_I {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ComplexSpace (ι := ι) μ p) :
    imLp μ p (Complex.I • f) = reLp μ p f := by
  apply Lp.ext
  filter_upwards [(imVec (ι := ι)).coeFn_compLpL (Complex.I • f), Lp.coeFn_smul Complex.I f,
    (reVec (ι := ι)).coeFn_compLpL f] with x hi hs hr
  change (imLp μ p (Complex.I • f)) x = imVec ((Complex.I • f) x) at hi
  change (reLp μ p f) x = reVec (f x) at hr
  rw [hi, hr, hs]
  ext i
  simp [reVec_apply, imVec_apply, Pi.smul_apply, smul_eq_mul]

theorem complexifyReal_I {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (V : Space (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p) (f : ComplexSpace (ι := ι) μ p) :
    complexifyReal μ V (Complex.I • f) = Complex.I • complexifyReal μ V f := by
  simp only [complexifyReal_apply, reLp_I, imLp_I, map_neg, smul_add, smul_smul,
    Complex.I_mul_I, neg_one_smul]
  abel

theorem complex_smul_decompose {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (z : ℂ) (f : ComplexSpace (ι := ι) μ p) :
    z • f = z.re • f + z.im • (Complex.I • f) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
    smul_smul, ← add_smul]
  exact congrArg (fun z : ℂ => z • f) (Complex.re_add_im z).symm

/-- The complex-linear operator extending V by V(Re f)+i V(Im f). -/
def complexify {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (V : Space (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p) :
    ComplexSpace (ι := ι) μ p →L[ℂ] ComplexSpace (ι := ι) μ p where
  toFun := complexifyReal μ V
  map_add' := (complexifyReal μ V).map_add
  map_smul' z f := by
    rw [complex_smul_decompose μ z f, map_add, map_smul, map_smul,
      complexifyReal_I, ← complex_smul_decompose]
    rfl
  cont := (complexifyReal μ V).continuous

@[simp] theorem complexify_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (V : Space (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p) (f : ComplexSpace (ι := ι) μ p) :
    complexify μ V f = complexifyReal μ V f := rfl

/-- Real/imaginary splitting gives the exact dimension-independent factor two
for complexifying any real mixed Lp bound. -/
theorem complexifyReal_bound {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (V : Space (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p) (M : ℝ) (hM : 0 ≤ M)
    (hV : ∀ f, ‖V f‖ ≤ M * l1Norm μ p f) (f : ComplexSpace (ι := ι) μ p) :
    ‖complexifyReal μ V f‖ ≤ (2 * M) * complexL1Norm μ p f := by
  rw [complexifyReal_apply]
  have hn := norm_add_le (ofRealLp μ p (V (reLp μ p f)))
    (Complex.I • ofRealLp μ p (V (imLp μ p f)))
  rw [norm_smul, Complex.norm_I, one_mul, norm_ofRealLp, norm_ofRealLp] at hn
  have hr := (hV (reLp μ p f)).trans (mul_le_mul_of_nonneg_left (l1Norm_reLp_le μ p f) hM)
  have hi := (hV (imLp μ p f)).trans (mul_le_mul_of_nonneg_left (l1Norm_imLp_le μ p f) hM)
  linarith

theorem complexify_bound {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (V : Space (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p) (M : ℝ) (hM : 0 ≤ M)
    (hV : ∀ f, ‖V f‖ ≤ M * l1Norm μ p f) (f : ComplexSpace (ι := ι) μ p) :
    ‖complexify μ V f‖ ≤ (2 * M) * complexL1Norm μ p f :=
  complexifyReal_bound μ V M hM hV f

theorem reLp_ae_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {f : ComplexSpace (ι := ι) μ p} {g : ComplexSpace (ι := ι) μ q} (h : f =ᵐ[μ] g) :
    reLp μ p f =ᵐ[μ] reLp μ q g := by
  filter_upwards [(reVec (ι := ι)).coeFn_compLpL f,
    (reVec (ι := ι)).coeFn_compLpL g, h] with x hf hg hx
  exact hf.trans ((congrArg reVec hx).trans hg.symm)

theorem imLp_ae_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {f : ComplexSpace (ι := ι) μ p} {g : ComplexSpace (ι := ι) μ q} (h : f =ᵐ[μ] g) :
    imLp μ p f =ᵐ[μ] imLp μ q g := by
  filter_upwards [(imVec (ι := ι)).coeFn_compLpL f,
    (imVec (ι := ι)).coeFn_compLpL g, h] with x hf hg hx
  exact hf.trans ((congrArg imVec hx).trans hg.symm)

theorem coeFn_complexify {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (V : Space (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p) (f : ComplexSpace (ι := ι) μ p) :
    complexify μ V f =ᵐ[μ] (fun x => ofRealVec (V (reLp μ p f) x) +
      Complex.I • ofRealVec (V (imLp μ p f) x)) := by
  filter_upwards [Lp.coeFn_add (ofRealLp μ p (V (reLp μ p f)))
      (Complex.I • ofRealLp μ p (V (imLp μ p f))),
    Lp.coeFn_smul Complex.I (ofRealLp μ p (V (imLp μ p f))),
    (ofRealVec (ι := ι)).coeFn_compLpL (V (reLp μ p f)),
    (ofRealVec (ι := ι)).coeFn_compLpL (V (imLp μ p f))] with x ha hs hr hi
  change (complexify μ V f) x = _ at ha
  change (ofRealLp μ p (V (reLp μ p f))) x = _ at hr
  change (ofRealLp μ p (V (imLp μ p f))) x = _ at hi
  rw [ha]
  simp only [Pi.add_apply]
  rw [hr, hs]
  simp only [Pi.smul_apply]
  rw [hi]

/-- Complexification preserves the precise common-representative agreement
needed for the interpolation of different Lp realizations. -/
theorem complexify_ae_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (V : Space (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p)
    (W : Space (ι := ι) μ q →L[ℝ] Space (ι := ι) μ q)
    (hVW : ∀ (f : Space (ι := ι) μ p) (g : Space (ι := ι) μ q),
      f =ᵐ[μ] g → V f =ᵐ[μ] W g)
    (f : ComplexSpace (ι := ι) μ p) (g : ComplexSpace (ι := ι) μ q) (hfg : f =ᵐ[μ] g) :
    complexify μ V f =ᵐ[μ] complexify μ W g := by
  have hr := hVW _ _ (reLp_ae_eq (ι := ι) μ hfg)
  have hi := hVW _ _ (imLp_ae_eq (ι := ι) μ hfg)
  filter_upwards [coeFn_complexify μ V f, coeFn_complexify μ W g, hr, hi] with x hf hg hr hi
  rw [hf, hg, hr, hi]

theorem reLp_ofRealLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    reLp μ p (ofRealLp μ p f) = f := by
  apply Lp.ext
  filter_upwards [(reVec (ι := ι)).coeFn_compLpL (ofRealLp μ p f),
    (ofRealVec (ι := ι)).coeFn_compLpL f] with x hr ho
  change (reLp μ p (ofRealLp μ p f)) x = _ at hr
  change (ofRealLp μ p f) x = _ at ho
  rw [hr, ho]
  rfl

theorem imLp_ofRealLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    imLp μ p (ofRealLp μ p f) = 0 := by
  apply Lp.ext
  filter_upwards [(imVec (ι := ι)).coeFn_compLpL (ofRealLp μ p f),
    (ofRealVec (ι := ι)).coeFn_compLpL f, Lp.coeFn_zero (ι → ℝ) p μ] with x hi ho hz
  change (imLp μ p (ofRealLp μ p f)) x = _ at hi
  change (ofRealLp μ p f) x = _ at ho
  rw [hi, ho, hz]
  rfl

theorem complexify_ofRealLp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (V : Space (ι := ι) μ p →L[ℝ] Space (ι := ι) μ p) (f : Space (ι := ι) μ p) :
    complexify μ V (ofRealLp μ p f) = ofRealLp μ p (V f) := by
  simp only [complexify_apply, complexifyReal_apply, reLp_ofRealLp, imLp_ofRealLp,
    map_zero, smul_zero, add_zero]

theorem complexL1Norm_ofRealLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    complexL1Norm μ p (ofRealLp μ p f) = l1Norm μ p f := by
  change ‖(complexToL1 (ι := ι)).compLpL p μ (ofRealLp μ p f)‖ =
    ‖(toL1 (ι := ι)).compLpL p μ f‖
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [(complexToL1 (ι := ι)).coeFn_compLpL (ofRealLp μ p f),
    (ofRealVec (ι := ι)).coeFn_compLpL f, (toL1 (ι := ι)).coeFn_compLpL f] with x hc ho hr
  change (ofRealLp μ p f) x = _ at ho
  rw [hc, ho, hr, norm_complexToL1, norm_toL1]
  simp only [ofRealVec_apply, Complex.norm_real, Real.norm_eq_abs]

end HilbertUMD.CubicLp
