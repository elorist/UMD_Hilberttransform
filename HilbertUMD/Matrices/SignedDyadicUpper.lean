import HilbertUMD.Hilbert.SharpHilbertTransfer
import HilbertUMD.Hilbert.HilbertMatrixData
import HilbertUMD.Matrices.MatrixCompatible
import HilbertUMD.Analysis.CubicComplex
import HilbertUMD.Matrices.MatrixBound

/-! Principal-value upper bounds for the manuscript's signed dyadic matrices.
The mixed operator estimates are converted to the original test-function
definition by the proved scalar PV reconstruction. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD
namespace L2Transfer

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

def rawFromL1 : L1Vec 𝕜 n →L[𝕜] Vec 𝕜 n :=
  (WithLp.linearEquiv 1 𝕜 (Vec 𝕜 n)).toLinearMap.toContinuousLinearMap

@[simp] theorem toL1_rawFromL1 (x : L1Vec 𝕜 n) : toL1 (rawFromL1 x) = x := rfl

/-- Converse of `ScalarPV.mixed`: a bound for the genuine amplified L²
operator implies the manuscript's principal-value test-function bound. -/
theorem ScalarPV.hilbertBound_of_mixed
    {U : Lp 𝕜 2 (volume : Measure ℝ) →L[𝕜] Lp 𝕜 2 (volume : Measure ℝ)}
    (hU : ScalarPV U) {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) (C : ℝ≥0)
    (hC : ∀ f : Lp (Vec 𝕜 n) 2 (volume : Measure ℝ),
      fibreNorm volume (toImage T) (amplification volume U f) ≤
        (C : ℝ) * fibreNorm volume (toL1 (𝕜 := 𝕜) (n := n)) f) :
    HilbertBound 2 (asL1Operator n T h) C := by
  intro f hf hc
  have hfR : ContDiff ℝ 1 (fun t => rawFromL1 (f t)) :=
    ((rawFromL1 (𝕜 := 𝕜) (n := n)).restrictScalars ℝ).contDiff.comp hf
  have hcR : HasCompactSupport (fun t => rawFromL1 (f t)) :=
    hc.comp_left (rawFromL1 (𝕜 := 𝕜) (n := n)).map_zero
  obtain ⟨g, hg, hpv, heq⟩ := hU.vector (fun t => rawFromL1 (f t)) hfR hcR
  refine ⟨fun t => T (g t), ?_, (toImage T).comp_memLp' hg, ?_⟩
  · exact hpv.map (hfR.continuous.integrable_of_hasCompactSupport hcR)
      ((toImage T).restrictScalars ℝ)
  · have hn := hC ((hilbertTest_memLp hfR hcR 2).toLp (fun t => rawFromL1 (f t)))
    rw [← heq, fibreNorm_apply, fibreNorm_apply, compLpL_toLp, compLpL_toLp] at hn
    have hen := ENNReal.ofReal_le_ofReal hn
    simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
      ofReal_norm, Lp.enorm_toLp, toImage_apply, toL1_rawFromL1] using hen

set_option maxHeartbeats 400000 in
/-- The harmless diagonal term has the same square-root growth required by
the final theorem, directly from the previously checked dyadic Hilbert norm. -/
theorem amplification_norm_le_sqrt
    (U : Lp 𝕜 2 (volume : Measure ℝ) →L[𝕜] Lp 𝕜 2 (volume : Measure ℝ))
    (hU : ∀ z, ‖U z‖ ≤ ‖z‖) (f : Lp (Vec 𝕜 n) 2 (volume : Measure ℝ)) :
    ‖amplification (n := n) volume U f‖ ≤ Real.sqrt ((n : ℝ) + 1) *
      fibreNorm volume (toL1 (𝕜 := 𝕜) (n := n)) f := by
  have hraw (z : Lp (Vec 𝕜 n) 2 (volume : Measure ℝ)) :
      ‖z‖ ≤ fibreNorm volume (toH (𝕜 := 𝕜) (n := n)) z := by
    change ‖z‖ ≤ ‖(toH (𝕜 := 𝕜) (n := n)).compLpL 2 volume z‖
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(toH (𝕜 := 𝕜) (n := n)).coeFn_compLpL z] with t ht
    rw [ht, norm_toH]
    exact (pi_norm_le_iff_of_nonneg (apply_nonneg (hilbertNorm n) (z t))).mpr
      (norm_coordinate_le_hilbert n (z t))
  have hin : fibreNorm volume (toH (𝕜 := 𝕜) (n := n)) f ≤
      Real.sqrt ((n : ℝ) + 1) * fibreNorm volume (toL1 (𝕜 := 𝕜) (n := n)) f := by
    change ‖(toH (𝕜 := 𝕜) (n := n)).compLpL 2 volume f‖ ≤
      Real.sqrt ((n : ℝ) + 1) * ‖(toL1 (𝕜 := 𝕜) (n := n)).compLpL 2 volume f‖
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(toH (𝕜 := 𝕜) (n := n)).coeFn_compLpL f,
      (toL1 (𝕜 := 𝕜) (n := n)).coeFn_compLpL f] with t hh hl
    rw [hh, hl, norm_toH, norm_toL1]
    exact hilbertNorm_le_l1 n (f t)
  exact (hraw _).trans ((amplification_hilbert_contraction (n := n) volume U hU f).trans hin)

end L2Transfer

theorem signedDyadic_ofReal (n : ℕ) (x : Vec ℝ n) :
    signedDyadic n (fun i => (x i : ℂ)) = fun i => ((signedDyadic (𝕜 := ℝ) n x i : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    rcases i with i | i
    · change signedDyadic n (fun i => ((left x) i : ℂ)) i +
        (-1 : ℂ) ^ (n + 1) * total (fun i => ((right x) i : ℂ)) = _
      rw [ih]
      simp [signedDyadic, total, left, right]
    · change (-1 : ℂ) ^ (n + 1) * total (fun i => ((left x) i : ℂ)) +
        signedDyadic n (fun i => ((right x) i : ℂ)) i = _
      rw [ih]
      simp [signedDyadic, total, left, right]

namespace SignedHilbert

def action {𝕜 : Type*} [RCLike 𝕜] (n : ℕ)
    (U : Lp 𝕜 2 (volume : Measure ℝ) →L[𝕜] Lp 𝕜 2 (volume : Measure ℝ)) :
    Lp (Vec 𝕜 n) 2 (volume : Measure ℝ) →L[𝕜] Lp (Vec 𝕜 n) 2 (volume : Measure ℝ) :=
  ((L2Transfer.toImage (signedDyadicLinear n)).compLpL 2 volume).comp
    (L2Transfer.amplification volume U)

theorem coordinate_ofRealLp {n : ℕ} (f : CubicLp.Space (ι := Leaf n) volume 2) (j : Leaf n) :
    (L2Transfer.coordinate (𝕜 := ℂ) j).compLpL 2 volume (CubicLp.ofRealLp volume 2 f) =
      l2OfReal ((L2Transfer.coordinate (𝕜 := ℝ) j).compLpL 2 volume f) := by
  apply Lp.ext
  filter_upwards [(L2Transfer.coordinate (𝕜 := ℂ) j).coeFn_compLpL (CubicLp.ofRealLp volume 2 f),
    (CubicLp.ofRealVec (ι := Leaf n)).coeFn_compLpL f,
    l2OfReal_coeFn ((L2Transfer.coordinate (𝕜 := ℝ) j).compLpL 2 volume f),
    (L2Transfer.coordinate (𝕜 := ℝ) j).coeFn_compLpL f] with t hc hf ho hr
  change (CubicLp.ofRealLp volume 2 f) t = _ at hf
  rw [hc, hf, ho, hr]
  rfl

theorem amplification_ofRealLp {n : ℕ} (f : CubicLp.Space (ι := Leaf n) volume 2) :
    L2Transfer.amplification volume hilbertL2.toContinuousLinearMap (CubicLp.ofRealLp volume 2 f) =
      CubicLp.ofRealLp volume 2 (L2Transfer.amplification volume realHilbertL2CLM f) := by
  apply L2Transfer.lp_eq_of_coordinates
  intro j
  rw [L2Transfer.coordinate_amplification, coordinate_ofRealLp,
    coordinate_ofRealLp, L2Transfer.coordinate_amplification]
  exact (ofReal_realHilbertL2 _).symm

theorem action_ofRealLp {n : ℕ} (f : CubicLp.Space (ι := Leaf n) volume 2) :
    action n hilbertL2.toContinuousLinearMap (CubicLp.ofRealLp volume 2 f) =
      CubicLp.ofRealLp volume 2 (action n realHilbertL2CLM f) := by
  change (L2Transfer.toImage (signedDyadicLinear (𝕜 := ℂ) n)).compLpL 2 volume
    (L2Transfer.amplification volume hilbertL2.toContinuousLinearMap (CubicLp.ofRealLp volume 2 f)) = _
  rw [amplification_ofRealLp]
  apply Lp.ext
  filter_upwards [(L2Transfer.toImage (signedDyadicLinear (𝕜 := ℂ) n)).coeFn_compLpL
      (CubicLp.ofRealLp volume 2 (L2Transfer.amplification volume realHilbertL2CLM f)),
    (CubicLp.ofRealVec (ι := Leaf n)).coeFn_compLpL (L2Transfer.amplification volume realHilbertL2CLM f),
    (CubicLp.ofRealVec (ι := Leaf n)).coeFn_compLpL (action n realHilbertL2CLM f),
    (L2Transfer.toImage (signedDyadicLinear (𝕜 := ℝ) n)).coeFn_compLpL
      (L2Transfer.amplification volume realHilbertL2CLM f)] with t hc hf ho hr
  change (CubicLp.ofRealLp volume 2 (L2Transfer.amplification volume realHilbertL2CLM f)) t = _ at hf
  change (CubicLp.ofRealLp volume 2 (action n realHilbertL2CLM f)) t = _ at ho
  change (action n realHilbertL2CLM f) t = _ at hr
  rw [hc, hf, ho, hr]
  exact signedDyadic_ofReal n _

theorem complex_reconstruction {n : ℕ} (f : CubicLp.ComplexSpace (ι := Leaf n) (volume : Measure ℝ) 2) :
    CubicLp.ofRealLp volume 2 (CubicLp.reLp volume 2 f) +
      Complex.I • CubicLp.ofRealLp volume 2 (CubicLp.imLp volume 2 f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (CubicLp.ofRealLp volume 2 (CubicLp.reLp volume 2 f))
      (Complex.I • CubicLp.ofRealLp volume 2 (CubicLp.imLp volume 2 f)),
    Lp.coeFn_smul Complex.I (CubicLp.ofRealLp volume 2 (CubicLp.imLp volume 2 f)),
    (CubicLp.ofRealVec (ι := Leaf n)).coeFn_compLpL (CubicLp.reLp volume 2 f),
    (CubicLp.ofRealVec (ι := Leaf n)).coeFn_compLpL (CubicLp.imLp volume 2 f),
    (CubicLp.reVec (ι := Leaf n)).coeFn_compLpL f,
    (CubicLp.imVec (ι := Leaf n)).coeFn_compLpL f] with t ha hs hor hoi hr hi
  change (CubicLp.ofRealLp volume 2 (CubicLp.reLp volume 2 f)) t = _ at hor
  change (CubicLp.ofRealLp volume 2 (CubicLp.imLp volume 2 f)) t = _ at hoi
  change (CubicLp.reLp volume 2 f) t = _ at hr
  change (CubicLp.imLp volume 2 f) t = _ at hi
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply]
  rw [hor, hoi, hr, hi]
  funext j
  simpa only [Pi.add_apply, Pi.smul_apply, CubicLp.ofRealVec_apply, CubicLp.reVec_apply,
    CubicLp.imVec_apply, smul_eq_mul, mul_comm] using Complex.re_add_im (f t j)

theorem action_complexify {n : ℕ} (f : CubicLp.ComplexSpace (ι := Leaf n) volume 2) :
    action n hilbertL2.toContinuousLinearMap f =
      CubicLp.complexify volume (action n realHilbertL2CLM) f := by
  conv_lhs => rw [← complex_reconstruction f]
  rw [map_add, map_smul, action_ofRealLp, action_ofRealLp]
  rfl

theorem action_eq_tree_add (n : ℕ) (f : CubicLp.Space (ι := Leaf n) volume 2) :
    action n realHilbertL2CLM f =
      MatrixCompatible.action volume 1 (fun k => (-1 : ℝ)^k) n 2 realHilbertL2CLM f +
        L2Transfer.amplification volume realHilbertL2CLM f := by
  have hamp : ScalarLp.amplification (ι := Leaf n) volume 2 realHilbertL2CLM =
      L2Transfer.amplification volume realHilbertL2CLM := by
    apply ContinuousLinearMap.ext
    intro z
    apply L2Transfer.lp_eq_of_coordinates
    intro j
    change (ScalarLp.coordinate j).compLpL 2 volume
      (ScalarLp.amplification volume 2 realHilbertL2CLM z) = _
    rw [ScalarLp.coordinate_amplification, L2Transfer.coordinate_amplification]
    rfl
  apply Lp.ext
  filter_upwards [(L2Transfer.toImage (signedDyadicLinear (𝕜 := ℝ) n)).coeFn_compLpL
      (L2Transfer.amplification volume realHilbertL2CLM f),
    (MatrixCompatible.treeCLM 1 (fun k => (-1 : ℝ)^k) n).coeFn_compLpL
      (L2Transfer.amplification volume realHilbertL2CLM f),
    Lp.coeFn_add (MatrixCompatible.action volume 1 (fun k => (-1 : ℝ)^k) n 2 realHilbertL2CLM f)
      (L2Transfer.amplification volume realHilbertL2CLM f)] with t hd ht ha
  change (action n realHilbertL2CLM f) t = _ at hd
  change (MatrixCompatible.treeCLM 1 (fun k => (-1 : ℝ)^k) n).compLpL 2 volume
    (L2Transfer.amplification volume realHilbertL2CLM f) t = _ at ht
  have ht' : MatrixCompatible.action volume 1 (fun k => (-1 : ℝ)^k) n 2 realHilbertL2CLM f t =
      treeMatrix 1 (fun k => (-1 : ℝ)^k) n (L2Transfer.amplification volume realHilbertL2CLM f t) := by
    simpa only [MatrixCompatible.action, ContinuousLinearMap.comp_apply, hamp,
      MatrixCompatible.treeCLM_apply] using ht
  rw [hd, ha]
  simp only [Pi.add_apply]
  rw [ht', treeMatrix_signedDyadic]
  exact (sub_add_cancel _ _).symm

def realBound (n : ℕ) : ℝ := matrixUpperConstant n 6 37 + Real.sqrt ((n : ℝ) + 1)

theorem realBound_nonneg (n : ℕ) : 0 ≤ realBound n :=
  add_nonneg (matrixUpperConstant_nonneg n 6 37) (Real.sqrt_nonneg _)

theorem action_real_bound (n : ℕ) (f : CubicLp.Space (ι := Leaf n) volume 2) :
    ‖action n realHilbertL2CLM f‖ ≤ realBound n * CubicLp.l1Norm volume 2 f := by
  have htree := ScalarMatrixData.matrix_bound_real volume hilbertMatrixData
    (by norm_num) (by norm_num) (by norm_num) (fun k => (-1 : ℝ)^k)
    (fun k => by rw [← pow_mul, Nat.mul_comm k 2, pow_mul]; norm_num) n realHilbertL2CLM
    (fun f h2 h3 => (realHilbertThree_agrees_two f h2 h3).symm)
    (fun f g => by simpa [realHilbertL2] using realHilbertL2_integral_skew f g) f
  have hdiag := L2Transfer.amplification_norm_le_sqrt realHilbertL2CLM
    (fun z => (norm_realHilbertL2 z).le) f
  have heq : L2Transfer.fibreNorm volume (L2Transfer.toL1 (𝕜 := ℝ) (n := n)) f =
      CubicLp.l1Norm volume 2 f := rfl
  rw [heq] at hdiag
  rw [action_eq_tree_add]
  exact (norm_add_le _ _).trans (by dsimp [realBound]; nlinarith)

theorem action_complex_bound (n : ℕ) (f : CubicLp.ComplexSpace (ι := Leaf n) volume 2) :
    ‖action n hilbertL2.toContinuousLinearMap f‖ ≤
      (2 * realBound n) * CubicLp.complexL1Norm volume 2 f := by
  rw [action_complexify]
  exact CubicLp.complexify_bound volume _ _ (realBound_nonneg n) (action_real_bound n) f

theorem realBound_le_sqrt (n : ℕ) :
    realBound n ≤ ((127 / 40) * Real.sqrt (9 * 146) + 1) * Real.sqrt ((n : ℝ) + 1) := by
  have hs := Real.sqrt_le_sqrt (show
      9 * ((n : ℝ) * (2 * (6 : ℝ)^2 + 2 * 37)) ≤ (9 * 146) * ((n : ℝ) + 1) by
    nlinarith)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9 * 146)] at hs
  unfold realBound matrixUpperConstant
  calc
    _ ≤ (127 / 40 : ℝ) * (Real.sqrt (9 * 146) * Real.sqrt ((n : ℝ) + 1)) +
        Real.sqrt ((n : ℝ) + 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 127 / 40)) le_rfl
    _ = _ := by ring

end SignedHilbert

/-- One explicit universal constant, shared by the real and complex bounds. -/
def signedDyadicUpperConstant : ℝ≥0 :=
  ⟨2 * ((127 / 40) * Real.sqrt (9 * 146) + 1), by positivity⟩

theorem SignedHilbert.two_realBound_le (n : ℕ) :
    2 * realBound n ≤ (signedDyadicUpperConstant * NNReal.sqrt (n + 1) : ℝ≥0) := by
  have h := mul_le_mul_of_nonneg_left (realBound_le_sqrt n) (by norm_num : (0 : ℝ) ≤ 2)
  change 2 * realBound n ≤ 2 * ((127 / 40) * Real.sqrt (9 * 146) + 1) *
    (NNReal.sqrt (n + 1) : ℝ)
  rw [Real.coe_sqrt]
  simpa only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, mul_assoc] using h

/-- Principal-value signed-dyadic upper bound over the real field. All
original matrix and transfer arguments in this implication are checked. -/
theorem signedDyadic_hilbertBound_real (n : ℕ) :
    HilbertBound 2 (signedDyadicOperator (𝕜 := ℝ) n)
      (signedDyadicUpperConstant * NNReal.sqrt (n + 1)) := by
  have hpv : L2Transfer.ScalarPV realHilbertL2CLM := Interfaces.real_scalar_pv_fourier
  apply hpv.hilbertBound_of_mixed (signedDyadic_le_l1 n)
  intro f
  have h := SignedHilbert.action_real_bound n f
  have hC : SignedHilbert.realBound n ≤ (signedDyadicUpperConstant * NNReal.sqrt (n + 1) : ℝ≥0) :=
    (by linarith [SignedHilbert.realBound_nonneg n] :
      SignedHilbert.realBound n ≤ 2 * SignedHilbert.realBound n).trans (SignedHilbert.two_realBound_le n)
  exact h.trans (mul_le_mul_of_nonneg_right hC (apply_nonneg _ _))

/-- The same principal-value bound over the complex field. The realization
is identified locally with the actual Fourier Hilbert transform. -/
theorem signedDyadic_hilbertBound_complex (n : ℕ) :
    HilbertBound 2 (signedDyadicOperator (𝕜 := ℂ) n)
      (signedDyadicUpperConstant * NNReal.sqrt (n + 1)) := by
  have hpv : L2Transfer.ScalarPV hilbertL2.toContinuousLinearMap := Interfaces.complex_scalar_pv_fourier
  apply hpv.hilbertBound_of_mixed (signedDyadic_le_l1 n)
  intro f
  exact (SignedHilbert.action_complex_bound n f).trans
    (mul_le_mul_of_nonneg_right (SignedHilbert.two_realBound_le n) (apply_nonneg _ _))

theorem signedDyadic_hilbertConstant_upper_real (n : ℕ) :
    hilbertConstant 2 (signedDyadicOperator (𝕜 := ℝ) n) ≤
      (signedDyadicUpperConstant * NNReal.sqrt (n + 1) : ℝ≥0) :=
  hilbertConstant_le (signedDyadic_hilbertBound_real n)

theorem signedDyadic_hilbertConstant_upper_complex (n : ℕ) :
    hilbertConstant 2 (signedDyadicOperator (𝕜 := ℂ) n) ≤
      (signedDyadicUpperConstant * NNReal.sqrt (n + 1) : ℝ≥0) :=
  hilbertConstant_le (signedDyadic_hilbertBound_complex n)

end HilbertUMD
