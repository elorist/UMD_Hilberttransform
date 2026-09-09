import HilbertUMD.Analysis.LpDualRepresentation
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
The dual endpoint in the original cubic argument. The required Bochner dual
representation, operator construction, endpoint estimate, skew pairing and
compatibility are proved locally.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace HilbertUMD.CubicLp

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S)

local instance : DecidableEq ι := Classical.decEq ι

local instance : ENNReal.HolderConjugate (3 : ℝ≥0∞) (3 / 2) := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]⟩

def ofL1 : PiLp 1 (fun _ : ι => ℝ) →L[ℝ] (ι → ℝ) :=
  (WithLp.linearEquiv 1 ℝ (ι → ℝ)).toLinearMap.toContinuousLinearMap

@[simp] theorem toL1_ofL1 (x : PiLp 1 (fun _ : ι => ℝ)) : toL1 (ofL1 x) = x := rfl
@[simp] theorem ofL1_toL1 (x : ι → ℝ) : ofL1 (toL1 x) = x := rfl

def pairingRight : Space (ι := ι) μ (3 / 2) →L[ℝ] StrongDual ℝ (Space (ι := ι) μ 3) :=
  ((dotL1 (ι := ι)).lpPairing μ 3 (3 / 2)).flip.comp ((toL1 (ι := ι)).compLpL (3 / 2) μ)

theorem pairingRight_apply (g : Space (ι := ι) μ (3 / 2)) (f : Space (ι := ι) μ 3) :
    pairingRight μ g f = ∫ x, ∑ i, f x i * g x i ∂μ := by
  rw [pairingRight, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(toL1 (ι := ι)).coeFn_compLpL g] with x hx
  rw [hx]
  rfl

theorem pairingRight_bound (g : Space (ι := ι) μ (3 / 2)) (f : Space (ι := ι) μ 3) :
    ‖pairingRight μ g f‖ ≤ ‖f‖ * l1Norm μ (3 / 2) g := by
  let G := (toL1 (ι := ι)).compLpL (3 / 2) μ g
  change ‖(dotL1 (ι := ι)).lpPairing μ 3 (3 / 2) f G‖ ≤ _
  calc
    _ ≤ ‖(dotL1 (ι := ι)).holder 1 f G‖ := by
      change ‖L1.integralCLM' ℝ ((dotL1 (ι := ι)).holder 1 f G)‖ ≤ _
      rw [← L1.integral_eq']
      exact L1.norm_integral_le ((dotL1 (ι := ι)).holder 1 f G)
    _ ≤ ‖dotL1 (ι := ι)‖ * ‖f‖ * ‖G‖ := ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ 1 * ‖f‖ * ‖G‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right dotL1_norm_le (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by rw [one_mul]; rfl

theorem pairingRight_norm_le (g : Space (ι := ι) μ (3 / 2)) :
    ‖pairingRight μ g‖ ≤ l1Norm μ (3 / 2) g := by
  apply ContinuousLinearMap.opNorm_le_bound _ (apply_nonneg _ _)
  intro f
  simpa only [mul_comm] using pairingRight_bound μ g f

theorem toL1_ofL1_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp (PiLp 1 (fun _ : ι => ℝ)) p μ) :
    (toL1 (ι := ι)).compLpL p μ ((ofL1 (ι := ι)).compLpL p μ f) = f := by
  apply Lp.ext
  filter_upwards [(toL1 (ι := ι)).coeFn_compLpL ((ofL1 (ι := ι)).compLpL p μ f),
    (ofL1 (ι := ι)).coeFn_compLpL f] with x ht ho
  rw [ht, ho, toL1_ofL1]

theorem ofL1_toL1_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    (ofL1 (ι := ι)).compLpL p μ ((toL1 (ι := ι)).compLpL p μ f) = f := by
  apply Lp.ext
  filter_upwards [(ofL1 (ι := ι)).coeFn_compLpL ((toL1 (ι := ι)).compLpL p μ f),
    (toL1 (ι := ι)).coeFn_compLpL f] with x ho ht
  rw [ho, ht, ofL1_toL1]

def mixedAtThree (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3) :
    Lp (PiLp 1 (fun _ : ι => ℝ)) 3 μ →L[ℝ] Space (ι := ι) μ 3 :=
  V.comp ((ofL1 (ι := ι)).compLpL 3 μ)

theorem mixedAtThree_norm_le (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    {K : ℝ} (hK : 0 ≤ K) (hV : ∀ f, ‖V f‖ ≤ K * l1Norm μ 3 f) :
    ‖mixedAtThree μ V‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro f
  have h := hV ((ofL1 (ι := ι)).compLpL 3 μ f)
  rw [l1Norm_apply, toL1_ofL1_Lp] at h
  exact h

def dualRepresentation : StrongDual ℝ (Lp (PiLp 1 (fun _ : ι => ℝ)) 3 μ) ≃ₗᵢ[ℝ]
    Space (ι := ι) μ (3 / 2) := (CubicLp.exists_l1_three_dual_representation μ).choose

theorem dualRepresentation_pairing
    (ℓ : StrongDual ℝ (Lp (PiLp 1 (fun _ : ι => ℝ)) 3 μ))
    (f : Lp (PiLp 1 (fun _ : ι => ℝ)) 3 μ) :
    ℓ f = ∫ x, ∑ i, f x i * dualRepresentation μ ℓ x i ∂μ :=
  (CubicLp.exists_l1_three_dual_representation μ).choose_spec ℓ f

def dualAtThreeLinear (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3) :
    Space (ι := ι) μ (3 / 2) →ₗ[ℝ] Space (ι := ι) μ (3 / 2) where
  toFun g := -(dualRepresentation μ ((pairingRight μ g).comp (mixedAtThree μ V)))
  map_add' g h := by simp [map_add, ContinuousLinearMap.add_comp, add_comm]
  map_smul' c g := by simp [map_smul, ContinuousLinearMap.smul_comp]

theorem dualAtThreeLinear_bound (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    (g : Space (ι := ι) μ (3 / 2)) :
    ‖dualAtThreeLinear μ V g‖ ≤ ‖mixedAtThree μ V‖ * l1Norm μ (3 / 2) g := by
  change ‖-(dualRepresentation μ ((pairingRight μ g).comp (mixedAtThree μ V)))‖ ≤ _
  rw [norm_neg, LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖pairingRight μ g‖ * ‖mixedAtThree μ V‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ l1Norm μ (3 / 2) g * ‖mixedAtThree μ V‖ :=
      mul_le_mul_of_nonneg_right (pairingRight_norm_le μ g) (norm_nonneg _)
    _ = _ := mul_comm _ _

def dualAtThree (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3) :
    Space (ι := ι) μ (3 / 2) →L[ℝ] Space (ι := ι) μ (3 / 2) :=
  (dualAtThreeLinear μ V).mkContinuous
    (‖mixedAtThree μ V‖ * ‖(toL1 (ι := ι)).compLpL (3 / 2) μ‖) (fun g => by
      refine (dualAtThreeLinear_bound μ V g).trans ?_
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((toL1 (ι := ι)).compLpL (3 / 2) μ).le_opNorm g)

theorem dualAtThree_apply (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    (g : Space (ι := ι) μ (3 / 2)) :
    dualAtThree μ V g = -(dualRepresentation μ ((pairingRight μ g).comp (mixedAtThree μ V))) := rfl

/-- The dual endpoint preserves the same mixed operator constant. -/
theorem dualAtThree_bound (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    {K : ℝ} (hK : 0 ≤ K) (hV : ∀ f, ‖V f‖ ≤ K * l1Norm μ 3 f)
    (g : Space (ι := ι) μ (3 / 2)) :
    ‖dualAtThree μ V g‖ ≤ K * l1Norm μ (3 / 2) g :=
  (dualAtThreeLinear_bound μ V g).trans
    (mul_le_mul_of_nonneg_right (mixedAtThree_norm_le μ V hK hV) (apply_nonneg _ _))

theorem dualAtThree_pairing (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    (f : Space (ι := ι) μ 3) (g : Space (ι := ι) μ (3 / 2)) :
    (∫ x, ∑ i, V f x i * g x i ∂μ) =
      -(∫ x, ∑ i, f x i * dualAtThree μ V g x i ∂μ) := by
  have h := dualRepresentation_pairing μ ((pairingRight μ g).comp (mixedAtThree μ V))
    ((toL1 (ι := ι)).compLpL 3 μ f)
  have hleft : ((pairingRight μ g).comp (mixedAtThree μ V))
      ((toL1 (ι := ι)).compLpL 3 μ f) = ∫ x, ∑ i, V f x i * g x i ∂μ := by
    simp only [ContinuousLinearMap.comp_apply, mixedAtThree, ofL1_toL1_Lp]
    exact pairingRight_apply μ g (V f)
  rw [hleft] at h
  refine h.trans ?_
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [(toL1 (ι := ι)).coeFn_compLpL f,
    Lp.coeFn_neg (dualRepresentation μ ((pairingRight μ g).comp (mixedAtThree μ V)))] with x ht hn
  rw [dualAtThree_apply, hn, ht]
  simp [toL1]

theorem pairing_coordinateIndicator (p : ℝ≥0∞) {s : Set S} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (i : ι) (g : S → ι → ℝ) :
    (∫ x, ∑ j, indicatorConstLp p hs hμs (Pi.single i (1 : ℝ) : ι → ℝ) x j * g x j ∂μ) =
      ∫ x in s, g x i ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs)
    (c := (Pi.single i (1 : ℝ) : ι → ℝ))] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · simp [Set.indicator_of_mem hxs, Pi.single_apply]
  · simp [Set.indicator_of_notMem hxs]

variable [SigmaFinite μ]

/-- The dual realization agrees with the original L2 operator on their full
intersection. Finite-measure coordinate indicators are the separating tests;
their L2/L3 agreement and the original L2 skew hypothesis are used explicitly. -/
theorem dualAtThree_agree (V : CompatibleRealOperator (ι := ι) μ)
    (f : Space (ι := ι) μ 2) (g : Space (ι := ι) μ (3 / 2)) (hfg : f =ᵐ[μ] g) :
    V.atTwo f =ᵐ[μ] dualAtThree μ V.atThree g := by
  have hi : ∀ i, (fun x => dualAtThree μ V.atThree g x i) =ᵐ[μ]
      (fun x => V.atTwo f x i) := by
    intro i
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    · intro s hs hμs
      have : Fact (μ s < ∞) := ⟨hμs⟩
      exact memLp_one_iff_integrable.mp
        (((memLp_pi_iff.mp (Lp.memLp (dualAtThree μ V.atThree g)) i).restrict s).mono_exponent
          (Fact.out : (1 : ℝ≥0∞) ≤ 3 / 2))
    · intro s hs hμs
      have : Fact (μ s < ∞) := ⟨hμs⟩
      exact memLp_one_iff_integrable.mp
        (((memLp_pi_iff.mp (Lp.memLp (V.atTwo f)) i).restrict s).mono_exponent (by norm_num))
    · intro s hs hμs
      let φ2 : Space (ι := ι) μ 2 := indicatorConstLp 2 hs hμs.ne (Pi.single i (1 : ℝ))
      let φ3 : Space (ι := ι) μ 3 := indicatorConstLp 3 hs hμs.ne (Pi.single i (1 : ℝ))
      have hφ : φ2 =ᵐ[μ] φ3 :=
        (indicatorConstLp_coeFn (p := 2)).trans (indicatorConstLp_coeFn (p := 3)).symm
      have hagree := V.agree φ2 φ3 hφ
      have hleft : (∫ x, ∑ j, V.atThree φ3 x j * g x j ∂μ) =
          ∫ x, ∑ j, V.atTwo φ2 x j * f x j ∂μ := by
        apply integral_congr_ae
        filter_upwards [hagree, hfg] with x hv hf
        rw [hv, hf]
      have hdual := dualAtThree_pairing μ V.atThree φ3 g
      rw [hleft] at hdual
      have hskew := V.skew φ2 f
      have heq := neg_injective (hdual.symm.trans hskew)
      change (∫ x, ∑ j, indicatorConstLp 3 hs hμs.ne (Pi.single i (1 : ℝ) : ι → ℝ) x j *
          dualAtThree μ V.atThree g x j ∂μ) =
        (∫ x, ∑ j, indicatorConstLp 2 hs hμs.ne (Pi.single i (1 : ℝ) : ι → ℝ) x j *
          V.atTwo f x j ∂μ) at heq
      simpa only [pairing_coordinateIndicator] using heq
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact (funext hx).symm

/-- Actual conjugate-exponent operator, with the same endpoint constant and
the agreement needed to interpolate the original L2 realization. -/
theorem exists_dual_endpoint (V : CompatibleRealOperator (ι := ι) μ)
    {K : ℝ} (hK : 0 ≤ K) (hV : ∀ f, ‖V.atThree f‖ ≤ K * l1Norm μ 3 f) :
    ∃ W : Space (ι := ι) μ (3 / 2) →L[ℝ] Space (ι := ι) μ (3 / 2),
      (∀ g, ‖W g‖ ≤ K * l1Norm μ (3 / 2) g) ∧
      (∀ (f : Space (ι := ι) μ 2) (g : Space (ι := ι) μ (3 / 2)),
        f =ᵐ[μ] g → V.atTwo f =ᵐ[μ] W g) :=
  ⟨dualAtThree μ V.atThree, dualAtThree_bound μ V.atThree hK hV, dualAtThree_agree μ V⟩

end HilbertUMD.CubicLp
