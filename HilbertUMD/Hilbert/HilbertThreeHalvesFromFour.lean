import HilbertUMD.Hilbert.HilbertThreeFromFour
import HilbertUMD.Analysis.ScalarThreeDuality
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# An independent bounded L(3/2) Hilbert operator

Dualize the independent L3 realization. Finite-measure indicator tests identify
the result with Fourier L2 on the intersection. Principal-value convergence on
arbitrary L(3/2) inputs is proved subsequently in `HilbertThreeHalvesPV`.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace HilbertUMD.HilbertThreeHalvesFromFour

open ScalarThreeDuality

def realHilbertThree : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 (volume : Measure ℝ) :=
  HilbertThreeFromFour.exists_real_hilbert_three.choose

theorem realHilbertThree_norm_le : ‖realHilbertThree‖ ≤ 6 :=
  HilbertThreeFromFour.exists_real_hilbert_three.choose_spec.1

theorem realHilbertThree_agrees_two (f : ℝ → ℝ) (h2 : MemLp f 2 volume)
    (h3 : MemLp f 3 volume) :
    realHilbertThree (h3.toLp f) =ᵐ[volume] realHilbertL2 (h2.toLp f) :=
  HilbertThreeFromFour.exists_real_hilbert_three.choose_spec.2 f h2 h3

/-- The negative transpose, transported through scalar isometric Lp duality. -/
def dual (R : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 (volume : Measure ℝ)) :
    Lp ℝ (3 / 2) (volume : Measure ℝ) →L[ℝ] Lp ℝ (3 / 2) (volume : Measure ℝ) :=
  -((representation volume).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL ℝ (Lp ℝ 3 (volume : Measure ℝ)) (Lp ℝ 3 (volume : Measure ℝ)) ℝ).flip R).comp
      (pairing volume)))

theorem dual_apply (R : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 volume)
    (g : Lp ℝ (3 / 2) (volume : Measure ℝ)) :
    dual R g = -(representation volume ((pairing volume g).comp R)) := rfl

theorem dual_norm_le (R : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 volume) :
    ‖dual R‖ ≤ ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro g
  rw [dual_apply, norm_neg, LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖pairing volume g‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by rw [norm_pairing]; ring

theorem dual_pairing (R : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 volume)
    (f : Lp ℝ 3 (volume : Measure ℝ)) (g : Lp ℝ (3 / 2) (volume : Measure ℝ)) :
    (∫ x, f x * dual R g x) = -(∫ x, R f x * g x) := by
  have he := representation_pairing volume ((pairing volume g).comp R) f
  rw [ContinuousLinearMap.comp_apply, pairing_apply] at he
  rw [he, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_neg (representation volume ((pairing volume g).comp R))] with x hx
  rw [dual_apply, hx]
  simp only [Pi.neg_apply, mul_neg]

def realHilbertThreeHalves : Lp ℝ (3 / 2) (volume : Measure ℝ) →L[ℝ]
    Lp ℝ (3 / 2) (volume : Measure ℝ) := dual realHilbertThree

theorem realHilbertThreeHalves_norm_le : ‖realHilbertThreeHalves‖ ≤ 6 :=
  (dual_norm_le realHilbertThree).trans realHilbertThree_norm_le

theorem realHilbertThreeHalves_nnnorm_le : ‖realHilbertThreeHalves‖₊ ≤ 6 := by
  exact_mod_cast realHilbertThreeHalves_norm_le

end HilbertUMD.HilbertThreeHalvesFromFour
