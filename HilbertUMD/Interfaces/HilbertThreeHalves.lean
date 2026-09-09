import HilbertUMD.Hilbert.HilbertThreeHalvesPV

/-! Scalar L(3/2) principal-value realization. The bounded operator and
its norm estimate are constructed independently by Cotlar's identity,
L2/L4 interpolation, and duality. Smooth averaging, kernel cancellation,
and Lebesgue differentiation identify the sharp principal values. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace HilbertUMD.Interfaces

local instance : Fact ((1 : ℝ≥0∞) ≤ 3 / 2) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num⟩

/-- The scalar L(3/2) realization, with PV identification and bound 6. -/
theorem exists_real_hilbert_three_halves :
    ∃ R : Lp ℝ (3 / 2) (volume : Measure ℝ) →L[ℝ]
        Lp ℝ (3 / 2) (volume : Measure ℝ),
      ‖R‖₊ ≤ 6 ∧ ∀ (f : ℝ → ℝ) (hf : MemLp f (3 / 2) volume),
        IsHilbertPVAe f (R (hf.toLp f)) := by
  refine ⟨HilbertThreeHalvesFromFour.realHilbertThreeHalves,
    HilbertThreeHalvesFromFour.realHilbertThreeHalves_nnnorm_le, ?_⟩
  intro f hf
  exact HilbertThreeHalvesPV.realHilbertThreeHalves_pv hf

end HilbertUMD.Interfaces
