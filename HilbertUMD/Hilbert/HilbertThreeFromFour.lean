import HilbertUMD.Hilbert.HilbertFourCompatibility
import HilbertUMD.Analysis.TwoFourInterpolation
import HilbertUMD.Hilbert.HilbertThreeDual

/-!
# An independent real L3 Hilbert operator

The Fourier L2 isometry, the Cotlar L4 estimate, and elementary interpolation
give an L3 operator without using the cited L(3/2) realization.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal

namespace HilbertUMD.HilbertThreeFromFour

open TwoFourInterpolation HilbertFourCompatibility

private theorem moment_two (g : Lp ℝ 2 (volume : Measure ℝ)) :
    moment (realHilbertL2 g) 2 ≤ moment g 2 := by
  have he (f : ℝ → ℝ) : eLpNorm f 2 volume ^ 2 = moment f 2 := by
    simpa only [Nat.cast_ofNat] using eLpNorm_pow_eq_moment f (by norm_num : (2 : ℕ) ≠ 0)
  rw [← he, ← he, ← Lp.enorm_def, ← Lp.enorm_def, realHilbertL2.enorm_map]

private theorem moment_four (g : ℝ → ℝ) (h2 : MemLp g 2 volume) (h4 : MemLp g 4 volume) :
    moment (realHilbertL2 (h2.toLp g)) 4 ≤ ENNReal.ofReal (625 / 16 : ℝ) * moment g 4 := by
  have he (f : ℝ → ℝ) : eLpNorm f 4 volume ^ 4 = moment f 4 := by
    simpa only [Nat.cast_ofNat] using eLpNorm_pow_eq_moment f (by norm_num : (4 : ℕ) ≠ 0)
  have h := pow_le_pow_left' (realHilbertL2_eLpNorm_four_le g h2 h4) 4
  rw [mul_pow, he, he] at h
  have hc : (5 / 2 : ℝ≥0∞) ^ 4 = ENNReal.ofReal (625 / 16 : ℝ) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) ENNReal.ofReal_ne_top).mp
    norm_num
  simpa only [hc] using h

/-- The Fourier Hilbert transform satisfies the L3 bound 6 on the L2 intersection. -/
theorem realHilbertL2_eLpNorm_three_le (f : ℝ → ℝ) (h2 : MemLp f 2 volume) :
    eLpNorm (realHilbertL2 (h2.toLp f)) 3 volume ≤ 6 * eLpNorm f 3 volume :=
  eLpNorm_three_le realHilbertL2.toContinuousLinearMap moment_two moment_four f h2

theorem realHilbertL2_memLp_three (f : ℝ → ℝ) (h2 : MemLp f 2 volume)
    (h3 : MemLp f 3 volume) : MemLp (fun x => realHilbertL2 (h2.toLp f) x) 3 volume :=
  memLp_three realHilbertL2.toContinuousLinearMap moment_two moment_four f h2 h3

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

/-- Independent L3 existence, including exact Fourier agreement on the full L2 intersection. -/
theorem exists_real_hilbert_three :
    ∃ R : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 volume,
      ‖R‖ ≤ 6 ∧ ∀ (f : ℝ → ℝ) (h2 : MemLp f 2 volume) (h3 : MemLp f 3 volume),
        R (h3.toLp f) =ᵐ[volume] realHilbertL2 (h2.toLp f) := by
  apply HilbertThreeDual.exists_extension_of_eLpNorm_bound volume
    realHilbertL2.toContinuousLinearMap (by norm_num : (0 : ℝ) ≤ 6)
  intro f
  have hf2 : MemLp (fun x : ℝ => f.val x) 2 volume := f.property
  have hf3 : MemLp (fun x : ℝ => f.val x) 3 volume := Lp.memLp _
  constructor
  · change MemLp (fun x => realHilbertL2 (hf2.toLp _) x) 3 volume
    apply realHilbertL2_memLp_three
    exact hf3
  change eLpNorm (realHilbertL2 (hf2.toLp _)) 3 volume ≤ _
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_ofNat,
    ofReal_norm, Lp.enorm_def]
  exact realHilbertL2_eLpNorm_three_le _ hf2

end HilbertUMD.HilbertThreeFromFour
