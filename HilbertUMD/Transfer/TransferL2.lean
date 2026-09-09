import HilbertUMD.Transfer.Transfer
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Transfer on genuine Bochner L2 spaces

The common domain below is mathlib's `Lp (Vec K n) 2 μ`; each norm is
the norm of its image in the corresponding genuine Bochner L2 space.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace HilbertUMD.L2Transfer

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

def toH : Vec 𝕜 n →L[𝕜] HSpace 𝕜 n :=
  LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := Vec 𝕜 n) (F' := HSpace 𝕜 n) LinearMap.id

def toE : Vec 𝕜 n →L[𝕜] ESpace 𝕜 n :=
  LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := Vec 𝕜 n) (F' := ESpace 𝕜 n) LinearMap.id

def toGraph (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : Vec 𝕜 n →L[𝕜] GraphSpace T :=
  LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := Vec 𝕜 n) (F' := GraphSpace T) LinearMap.id

def toL1 : Vec 𝕜 n →L[𝕜] L1Vec 𝕜 n :=
  (WithLp.linearEquiv 1 𝕜 (Vec 𝕜 n)).symm.toLinearMap.toContinuousLinearMap

def toImage (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : Vec 𝕜 n →L[𝕜] Vec 𝕜 n :=
  T.toContinuousLinearMap

@[simp] theorem norm_toH (x : Vec 𝕜 n) : ‖toH x‖ = hilbertNorm n x := rfl
@[simp] theorem norm_toE (x : Vec 𝕜 n) : ‖toE x‖ = sumNorm n x := rfl
@[simp] theorem norm_toGraph (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) (x : Vec 𝕜 n) :
    ‖toGraph T x‖ = graphNorm T x := rfl
@[simp] theorem norm_toL1 (x : Vec 𝕜 n) : ‖toL1 x‖ = l1Norm n x :=
  PiLp.norm_eq_of_L1 _
@[simp] theorem toImage_apply (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) (x : Vec 𝕜 n) :
    toImage T x = T x := rfl

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pull back the Bochner L2 norm through a continuous linear fibre map. -/
def fibreNorm (J : Vec 𝕜 n →L[𝕜] F) : Seminorm 𝕜 (Lp (Vec 𝕜 n) 2 μ) :=
  (normSeminorm 𝕜 (Lp F 2 μ)).comp (J.compLpL 2 μ).toLinearMap

theorem fibreNorm_apply (J : Vec 𝕜 n →L[𝕜] F) (f : Lp (Vec 𝕜 n) 2 μ) :
    fibreNorm μ J f = ‖J.compLpL 2 μ f‖ := rfl

theorem continuous_fibreNorm (J : Vec 𝕜 n →L[𝕜] F) : Continuous (fibreNorm μ J) :=
  continuous_norm.comp (J.compLpL 2 μ).continuous

theorem fibreNorm_bound (J : Vec 𝕜 n →L[𝕜] F) (K : Vec 𝕜 n →L[𝕜] G)
    (c : ℝ) (h : ∀ x, ‖J x‖ ≤ c * ‖K x‖) (f : Lp (Vec 𝕜 n) 2 μ) :
    fibreNorm μ J f ≤ c * fibreNorm μ K f := by
  change ‖J.compLpL 2 μ f‖ ≤ c * ‖K.compLpL 2 μ f‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [J.coeFn_compLpL f, K.coeFn_compLpL f] with t hJ hK
  rw [hJ, hK]
  exact h (f t)

theorem lp_norm_sq_integral {B : Type*} [NormedAddCommGroup B] (f : Lp B 2 μ) :
    ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable f),
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable f)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg (fun t => sq_nonneg _))]

theorem fibreNorm_sq (J : Vec 𝕜 n →L[𝕜] F) (f : Lp (Vec 𝕜 n) 2 μ) :
    fibreNorm μ J f ^ 2 = ∫ t, ‖J (f t)‖ ^ 2 ∂μ := by
  rw [fibreNorm_apply, lp_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [J.coeFn_compLpL f] with t ht
  rw [ht]

theorem fibreNorm_integrable_sq (J : Vec 𝕜 n →L[𝕜] F) (f : Lp (Vec 𝕜 n) 2 μ) :
    Integrable (fun t => ‖J (f t)‖ ^ 2) μ := by
  have h : Integrable (fun t => ‖(J.compLpL 2 μ f) t‖ ^ 2) μ :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  apply h.congr
  filter_upwards [J.coeFn_compLpL f] with t ht
  rw [ht]

theorem fibreNorm_sq_toLp (J : Vec 𝕜 n →L[𝕜] F) (f : S → Vec 𝕜 n)
    (hf : MemLp f 2 μ) : fibreNorm μ J (hf.toLp f) ^ 2 = ∫ t, ‖J (f t)‖ ^ 2 ∂μ := by
  rw [fibreNorm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]

/-- A genuine L2 decomposition for each simple-function equivalence class. -/
theorem simple_decomposition (f : SimpleFunc S (Vec 𝕜 n)) (hf : MemLp f 2 μ) :
    ∃ u v : Lp (Vec 𝕜 n) 2 μ, hf.toLp f = u + v ∧
      fibreNorm μ toL1 u ^ 2 + fibreNorm μ toH v ^ 2 ≤ fibreNorm μ toE (hf.toLp f) ^ 2 := by
  have hfs : f.FinMeasSupp μ :=
    (SimpleFunc.memLp_iff_finMeasSupp (by norm_num) (by norm_num)).mp hf
  obtain ⟨u, v, huv, hu, hv, hdec⟩ :=
    simpleFunc_integral_sumNorm_decomposition (𝕜 := 𝕜) (n := n) μ f hfs
  have huLp : MemLp u 2 μ :=
    (SimpleFunc.memLp_iff_finMeasSupp (by norm_num) (by norm_num)).mpr hu
  have hvLp : MemLp v 2 μ :=
    (SimpleFunc.memLp_iff_finMeasSupp (by norm_num) (by norm_num)).mpr hv
  refine ⟨huLp.toLp u, hvLp.toLp v, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [hf.coeFn_toLp, huLp.coeFn_toLp, hvLp.coeFn_toLp,
      Lp.coeFn_add (huLp.toLp u) (hvLp.toLp v)] with t hf' hu' hv' ha
    rw [hf', ha]
    change f t = (huLp.toLp u) t + (hvLp.toLp v) t
    rw [hu', hv']
    exact congrArg (fun z : SimpleFunc S (Vec 𝕜 n) => z t) huv
  · rw [fibreNorm_sq_toLp, fibreNorm_sq_toLp, fibreNorm_sq_toLp]
    simpa only [norm_toL1, norm_toH, norm_toE] using hdec

theorem lp_simple_decomposition (f : Lp.simpleFunc (Vec 𝕜 n) 2 μ) :
    ∃ u v : Lp (Vec 𝕜 n) 2 μ, (f : Lp (Vec 𝕜 n) 2 μ) = u + v ∧
      fibreNorm μ toL1 u ^ 2 + fibreNorm μ toH v ^ 2 ≤
        fibreNorm μ toE (f : Lp (Vec 𝕜 n) 2 μ) ^ 2 := by
  have heq : (Lp.simpleFunc.memLp f).toLp (Lp.simpleFunc.toSimpleFunc f) =
      (f : Lp (Vec 𝕜 n) 2 μ) :=
    congrArg Subtype.val (Lp.simpleFunc.toLp_toSimpleFunc f)
  simpa only [heq] using
    simple_decomposition μ (Lp.simpleFunc.toSimpleFunc f) (Lp.simpleFunc.memLp f)

theorem fibreNorm_graph_sq_le (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n)
    (f : Lp (Vec 𝕜 n) 2 μ) :
    fibreNorm μ (toGraph T) f ^ 2 ≤
      fibreNorm μ (toImage T) f ^ 2 + fibreNorm μ toE f ^ 2 := by
  rw [fibreNorm_sq, fibreNorm_sq, fibreNorm_sq, ← integral_add
    (fibreNorm_integrable_sq μ (toImage T) f) (fibreNorm_integrable_sq μ toE f)]
  apply integral_mono (fibreNorm_integrable_sq μ (toGraph T) f)
    ((fibreNorm_integrable_sq μ (toImage T) f).add (fibreNorm_integrable_sq μ toE f))
  intro t
  change (max ‖T (f t)‖ (sumNorm n (f t))) ^ 2 ≤ ‖T (f t)‖ ^ 2 + sumNorm n (f t) ^ 2
  rcases le_total ‖T (f t)‖ (sumNorm n (f t)) with h | h
  · rw [max_eq_right h]
    nlinarith only [sq_nonneg ‖T (f t)‖]
  · rw [max_eq_left h]
    nlinarith only [sq_nonneg (sumNorm n (f t))]

/-- The core transfer estimate when an L2 minimizing decomposition is supplied.
The operator assumptions are contraction for the dyadic Hilbert norm and
the mixed l1-to-linfinity bound for TA. -/
theorem transfer_of_decomposition {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    (hT : TransferAssumptions T)
    (A : Lp (Vec 𝕜 n) 2 μ →L[𝕜] Lp (Vec 𝕜 n) 2 μ)
    (hH : ∀ f, fibreNorm μ toH (A f) ≤ fibreNorm μ toH f)
    (M : ℝ)
    (hM : ∀ f, fibreNorm μ (toImage T) (A f) ≤ M * fibreNorm μ toL1 f)
    (f u v : Lp (Vec 𝕜 n) 2 μ) (huv : f = u + v)
    (hdec : fibreNorm μ toL1 u ^ 2 + fibreNorm μ toH v ^ 2 ≤ fibreNorm μ toE f ^ 2) :
    fibreNorm μ (toGraph T) (A f) ^ 2 ≤
      (M ^ 2 + 2 * ((n : ℝ) + 1)) * fibreNorm μ (toGraph T) f ^ 2 := by
  let s := Real.sqrt ((n : ℝ) + 1)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hEH (g : Lp (Vec 𝕜 n) 2 μ) : fibreNorm μ toE g ≤ fibreNorm μ toH g := by
    simpa only [one_mul] using fibreNorm_bound μ toE toH 1
      (fun x => by simpa only [norm_toE, norm_toH, one_mul] using sumNorm_le_hilbert n x) g
  have hEF : fibreNorm μ toE f ≤ fibreNorm μ (toGraph T) f := by
    simpa only [one_mul] using fibreNorm_bound μ toE (toGraph T) 1
      (fun x => by rw [one_mul, norm_toE, norm_toGraph]; exact le_max_right _ _) f
  have hHF : fibreNorm μ toH f ≤ s * fibreNorm μ (toGraph T) f := by
    apply fibreNorm_bound μ toH (toGraph T) s _ f
    intro x
    rw [norm_toH, norm_toGraph]
    exact hilbertNorm_le_graphNorm (𝕜 := 𝕜) (n := n) T x
  have hE : fibreNorm μ toE (A f) ≤ s * fibreNorm μ (toGraph T) f :=
    (hEH _).trans ((hH f).trans hHF)
  have hE2 : fibreNorm μ toE (A f) ^ 2 ≤ (s * fibreNorm μ (toGraph T) f) ^ 2 := by
    apply pow_le_pow_left₀ _ hE 2
    exact apply_nonneg _ _
  rw [mul_pow, hs2] at hE2
  have hEF2 : fibreNorm μ toE f ^ 2 ≤ fibreNorm μ (toGraph T) f ^ 2 := by
    apply pow_le_pow_left₀ _ hEF 2
    exact apply_nonneg _ _
  have hdecF : fibreNorm μ toL1 u ^ 2 + fibreNorm μ toH v ^ 2 ≤
      fibreNorm μ (toGraph T) f ^ 2 := hdec.trans hEF2
  have hTv : fibreNorm μ (toImage T) (A v) ≤ s * fibreNorm μ toH v := by
    apply le_trans (fibreNorm_bound μ (toImage T) toH s _ (A v))
      (mul_le_mul_of_nonneg_left (hH v) hs)
    intro x
    rw [toImage_apply, norm_toH]
    exact hT.hilbert_bound x
  have hTf : fibreNorm μ (toImage T) (A f) ≤
      M * fibreNorm μ toL1 u + s * fibreNorm μ toH v := by
    rw [huv, map_add]
    exact (map_add_le_add (fibreNorm μ (toImage T)) _ _).trans (add_le_add (hM u) hTv)
  have hTf2 : fibreNorm μ (toImage T) (A f) ^ 2 ≤
      (M * fibreNorm μ toL1 u + s * fibreNorm μ toH v) ^ 2 := by
    apply pow_le_pow_left₀ _ hTf 2
    exact apply_nonneg _ _
  have hCS : (M * fibreNorm μ toL1 u + s * fibreNorm μ toH v) ^ 2 ≤
      (M ^ 2 + s ^ 2) * (fibreNorm μ toL1 u ^ 2 + fibreNorm μ toH v ^ 2) := by
    nlinarith only [sq_nonneg (M * fibreNorm μ toH v - s * fibreNorm μ toL1 u)]
  have hTfFinal : fibreNorm μ (toImage T) (A f) ^ 2 ≤
      (M ^ 2 + s ^ 2) * fibreNorm μ (toGraph T) f ^ 2 :=
    hTf2.trans (hCS.trans (mul_le_mul_of_nonneg_left hdecF (by positivity)))
  rw [hs2] at hTfFinal
  calc
    fibreNorm μ (toGraph T) (A f) ^ 2 ≤
        fibreNorm μ (toImage T) (A f) ^ 2 + fibreNorm μ toE (A f) ^ 2 :=
      fibreNorm_graph_sq_le μ T _
    _ ≤ (M ^ 2 + ((n : ℝ) + 1)) * fibreNorm μ (toGraph T) f ^ 2 +
        ((n : ℝ) + 1) * fibreNorm μ (toGraph T) f ^ 2 := add_le_add hTfFinal hE2
    _ = _ := by ring

/-- Full transfer on a genuine Bochner L2 space over an arbitrary measure.
Density removes the simple-function restriction. This theorem assumes exactly
the operator's H-L2 contraction and TA mixed-norm bound; deriving H-L2
contraction from a given scalar operator is a separate amplification step. -/
theorem transfer {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} (hT : TransferAssumptions T)
    (A : Lp (Vec 𝕜 n) 2 μ →L[𝕜] Lp (Vec 𝕜 n) 2 μ)
    (hH : ∀ f, fibreNorm μ toH (A f) ≤ fibreNorm μ toH f)
    (M : ℝ)
    (hM : ∀ f, fibreNorm μ (toImage T) (A f) ≤ M * fibreNorm μ toL1 f)
    (f : Lp (Vec 𝕜 n) 2 μ) :
    fibreNorm μ (toGraph T) (A f) ^ 2 ≤
      (M ^ 2 + 2 * ((n : ℝ) + 1)) * fibreNorm μ (toGraph T) f ^ 2 := by
  refine (Lp.simpleFunc.denseRange (E := Vec 𝕜 n) (p := 2) (μ := μ) (by norm_num)).induction_on
    (p := fun g => fibreNorm μ (toGraph T) (A g) ^ 2 ≤
      (M ^ 2 + 2 * ((n : ℝ) + 1)) * fibreNorm μ (toGraph T) g ^ 2) f ?_ ?_
  · exact isClosed_le (((continuous_fibreNorm μ (toGraph T)).comp A.continuous).pow 2)
      (continuous_const.mul ((continuous_fibreNorm μ (toGraph T)).pow 2))
  · intro g
    obtain ⟨u, v, huv, hdec⟩ := lp_simple_decomposition (𝕜 := 𝕜) (n := n) μ g
    exact transfer_of_decomposition μ hT A hH M hM g u v huv hdec

end HilbertUMD.L2Transfer
