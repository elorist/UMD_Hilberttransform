import HilbertUMD.Analysis.ScalarLpDualRepresentation
import HilbertUMD.Analysis.MixedLpNorming
import Mathlib.MeasureTheory.Function.Holder

/-! Isometric L³(l¹) dual representation for finite real coordinate spaces.
Scalar existence comes from cubic-energy minimization; the exact norm comes
from the explicit measurable maximizing-coordinate tests. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace HilbertUMD.CubicLp

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S)
local instance : DecidableEq ι := Classical.decEq ι

def dotL1Linear : (ι → ℝ) →ₗ[ℝ] PiLp 1 (fun _ : ι => ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, x i * y i)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [mul_assoc, Finset.mul_sum])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp [mul_left_comm, Finset.mul_sum])

theorem dotL1_bound (x : ι → ℝ) (y : PiLp 1 (fun _ : ι => ℝ)) :
    ‖dotL1Linear x y‖ ≤ 1 * ‖x‖ * ‖y‖ := by
  change |∑ i, x i * y i| ≤ _
  rw [one_mul, PiLp.norm_eq_of_L1, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (abs_nonneg _)

def dotL1 : (ι → ℝ) →L[ℝ] PiLp 1 (fun _ : ι => ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ dotL1Linear 1 dotL1_bound

@[simp] theorem dotL1_apply (x : ι → ℝ) (y : PiLp 1 (fun _ : ι => ℝ)) :
    dotL1 x y = ∑ i, x i * y i := rfl

theorem dotL1_norm_le : ‖dotL1 (ι := ι)‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ (by norm_num) _

/-- The canonical integral map into the dual of L³(l¹). -/
def l1DualPairing : Space (ι := ι) μ (3 / 2) →L[ℝ]
    StrongDual ℝ (Lp (PiLp 1 (fun _ : ι => ℝ)) 3 μ) :=
  (dotL1 (ι := ι)).lpPairing μ (3 / 2) 3

theorem l1DualPairing_apply (w : Space (ι := ι) μ (3 / 2))
    (f : Lp (PiLp 1 (fun _ : ι => ℝ)) 3 μ) :
    l1DualPairing μ w f = ∫ x, ∑ i, f x i * w x i ∂μ := by
  rw [l1DualPairing, ContinuousLinearMap.lpPairing_eq_integral]
  simp only [dotL1_apply, mul_comm]

theorem l1DualPairing_norm_le (w : Space (ι := ι) μ (3 / 2)) :
    ‖l1DualPairing μ w‖ ≤ ‖w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  calc
    _ ≤ ‖(dotL1 (ι := ι)).holder 1 w f‖ := by
      change ‖L1.integralCLM' ℝ ((dotL1 (ι := ι)).holder 1 w f)‖ ≤ _
      rw [← L1.integral_eq']
      exact L1.norm_integral_le _
    _ ≤ ‖dotL1 (ι := ι)‖ * ‖w‖ * ‖f‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ 1 * ‖w‖ * ‖f‖ := by gcongr; exact dotL1_norm_le
    _ = _ := by rw [one_mul]

theorem l1DualPairing_norm (w : Space (ι := ι) μ (3 / 2)) :
    ‖l1DualPairing μ w‖ = ‖w‖ := by
  apply le_antisymm (l1DualPairing_norm_le μ w)
  apply norm_le_of_l1_unit_tests μ (q := 3)
    (by apply (ENNReal.toReal_lt_toReal (by simp) (by finiteness)).mp; norm_num) (by finiteness)
    (by norm_num) (by simp) w _ (norm_nonneg _)
  intro g hg
  have he : (∫ x, ∑ i, w x i * g x i ∂μ) =
      l1DualPairing μ w ((toL1 (ι := ι)).compLpL 3 μ g) := by
    rw [l1DualPairing_apply]
    apply integral_congr_ae
    filter_upwards [(toL1 (ι := ι)).coeFn_compLpL g] with x hx
    rw [hx]
    change (∑ i, w x i * g x i) = ∑ i, g x i * w x i
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he]
  exact ((l1DualPairing μ w).le_opNorm _).trans
    (by simpa only [l1Norm_apply, mul_one] using
      mul_le_mul_of_nonneg_left hg (norm_nonneg (l1DualPairing μ w)))

private def coordinateIn (i : ι) : ℝ →L[ℝ] PiLp 1 (fun _ : ι => ℝ) :=
  (toL1 (ι := ι)).comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)

private def coordinateOut (i : ι) : PiLp 1 (fun _ : ι => ℝ) →L[ℝ] ℝ :=
  PiLp.proj 1 (fun _ : ι => ℝ) i

private theorem sum_coordinate_Lp (f : Lp (PiLp 1 (fun _ : ι => ℝ)) 3 μ) :
    (∑ i, (coordinateIn i).compLpL 3 μ ((coordinateOut i).compLpL 3 μ f)) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => (coordinateIn i).compLpL 3 μ ((coordinateOut i).compLpL 3 μ f)),
    ae_all_iff.mpr (fun i : ι => (coordinateIn (ι := ι) i).coeFn_compLpL ((coordinateOut i).compLpL 3 μ f)),
    ae_all_iff.mpr (fun i : ι => (coordinateOut i).coeFn_compLpL f)] with x hs hi ho
  rw [hs]
  simp only [hi, ho]
  apply (WithLp.linearEquiv 1 ℝ (ι → ℝ)).injective
  simp only [map_sum]
  change (∑ i, Pi.single i (f x i)) = _
  ext i
  simp

theorem l1DualPairing_surjective : Function.Surjective (l1DualPairing (ι := ι) μ) := by
  intro ℓ
  have hc (i : ι) := ScalarLpDualRepresentation.exists_representation μ
    (ℓ.comp ((coordinateIn i).compLpL 3 μ))
  choose w hw using hc
  have hW : MemLp (fun x i => w i x) (3 / 2) μ :=
    memLp_pi_iff.mpr (fun i => Lp.memLp (w i))
  refine ⟨hW.toLp _, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  have hfi (i : ι) : MemLp (fun x => f x i) 3 μ :=
    (coordinateOut i).comp_memLp f
  have hw' (i : ι) := hw i ((coordinateOut i).compLpL 3 μ f)
  have hi (i : ι) : ℓ ((coordinateIn i).compLpL 3 μ ((coordinateOut i).compLpL 3 μ f)) =
      ∫ x, f x i * w i x ∂μ := by
    refine (hw' i).trans ?_
    apply integral_congr_ae
    filter_upwards [(coordinateOut i).coeFn_compLpL f] with x hx
    rw [hx]
    rfl
  rw [l1DualPairing_apply]
  calc
    _ = ∫ x, ∑ i, f x i * w i x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hW.coeFn_toLp] with x hx
      rw [hx]
    _ = ∑ i, ∫ x, f x i * w i x ∂μ :=
      integral_finsetSum _ (fun i _ => (hfi i).integrable_mul (Lp.memLp (w i)))
    _ = ℓ (∑ i, (coordinateIn i).compLpL 3 μ ((coordinateOut i).compLpL 3 μ f)) := by
      simp only [map_sum, hi]
    _ = ℓ f := by rw [sum_coordinate_Lp]

/-- Finite real l¹/l∞ duality at the conjugate exponents 3 and 3/2.
The proof works for every measure, including empty coordinate types. -/
theorem exists_l1_three_dual_representation :
    ∃ R : StrongDual ℝ (Lp (PiLp 1 (fun _ : ι => ℝ)) 3 μ) ≃ₗᵢ[ℝ]
        Space (ι := ι) μ (3 / 2),
      ∀ ℓ f, ℓ f = ∫ x, ∑ i, f x i * R ℓ x i ∂μ := by
  let J : Space (ι := ι) μ (3 / 2) →ₗᵢ[ℝ]
      StrongDual ℝ (Lp (PiLp 1 (fun _ : ι => ℝ)) 3 μ) :=
    { (l1DualPairing μ).toLinearMap with norm_map' := l1DualPairing_norm μ }
  let e := LinearIsometryEquiv.ofSurjective J (l1DualPairing_surjective μ)
  refine ⟨e.symm, fun ℓ f => ?_⟩
  have h := congrArg (fun L => L f) (e.apply_symm_apply ℓ)
  exact h.symm.trans (l1DualPairing_apply μ (e.symm ℓ) f)

end HilbertUMD.CubicLp
