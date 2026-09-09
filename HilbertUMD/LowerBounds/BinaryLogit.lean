import HilbertUMD.LowerBounds.BinaryLogitPairing
import HilbertUMD.UMD.BinaryWalsh

/-! The direct square-root lower bound for the logarithmic signed-dyadic witness.
Every scalar integral, coefficient identity and Bessel step is proved locally. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace HilbertUMD.BinaryLogit

theorem a_eq_pair_r (j : ℕ) : a j = ∫ t, g t * r j t ∂unitMeasure :=
  a_eq_integral_g_sign_iterate j

def G_coefficient (n j : ℕ) : ℝ := ∫ t, G n t * r j t ∂unitMeasure

theorem G_coefficient_succ (n j : ℕ) :
    G_coefficient (n + 1) j =
      (∫ t, G n (tau t) * r j t ∂unitMeasure) +
        (-1 : ℝ) ^ (n + 1) * (a j - ∫ t, g (tau t) * r j t ∂unitMeasure) := by
  have hGt := integrable_mul_r
    (tau_measurePreserving.integrable_comp_of_integrable (G_integrable n)) j
  have hgr := integrable_mul_r integrable_g j
  have hgtr := integrable_mul_r
    (tau_measurePreserving.integrable_comp_of_integrable integrable_g) j
  change Integrable (fun t => G n (tau t) * r j t) unitMeasure at hGt
  change Integrable (fun t => g (tau t) * r j t) unitMeasure at hgtr
  have hrest : Integrable (fun t => (-1 : ℝ) ^ (n + 1) *
      (g t * r j t - g (tau t) * r j t)) unitMeasure :=
    (hgr.sub hgtr).const_mul _
  unfold G_coefficient
  simp_rw [G_succ, add_mul, mul_assoc, sub_mul]
  rw [MeasureTheory.integral_add hGt hrest,
    integral_const_mul, MeasureTheory.integral_sub hgr hgtr, ← a_eq_pair_r]

theorem G_coefficient_first (n : ℕ) :
    G_coefficient (n + 1) 0 = (-1 : ℝ) ^ (n + 1) * a 0 := by
  rw [G_coefficient_succ, pair_r_zero (G_integrable n), pair_r_zero integrable_g]
  ring

theorem G_coefficient_shift (n j : ℕ) :
    G_coefficient (n + 1) (j + 1) = G_coefficient n j +
      (-1 : ℝ) ^ (n + 1) * (a (j + 1) - a j) := by
  rw [G_coefficient_succ, pair_r_shift (G_integrable n), pair_r_shift integrable_g,
    ← a_eq_pair_r]
  rfl

theorem G_coefficient_eq (n j : ℕ) (hj : j < n) :
    G_coefficient n j = (-1 : ℝ) ^ (n - j) * alternatingCoefficient a j :=
  binary_coefficient_recursion a G_coefficient G_coefficient_first G_coefficient_shift n j hj

theorem G_coefficient_abs_lower (n j : ℕ) (hj : j < n) :
    delta ≤ |G_coefficient n j| := by
  rw [G_coefficient_eq n j hj, abs_mul, abs_pow]
  norm_num only [abs_neg, abs_one, one_pow, one_mul]
  exact (a_alternating_lower j).trans (le_abs_self _)

/-- The original scalar diagonal estimate, with the exact positive constant
`delta = (2/π) log(27/16)`, for restricted Lebesgue measure on (0,1). -/
theorem G_lower (n : ℕ) :
    ENNReal.ofReal (delta * Real.sqrt (n : ℝ)) ≤ eLpNorm (G n) 2 unitMeasure := by
  classical
  by_cases hG : MemLp (G n) 2 unitMeasure
  · have hb := bessel n hG
    have hc : (n : ℝ) * delta ^ 2 ≤ ∑ j : Fin n, (G_coefficient n j.val) ^ 2 := by
      calc
        _ = ∑ _j : Fin n, delta ^ 2 := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          have h := G_coefficient_abs_lower n j.val j.isLt
          have hδ := delta_pos
          nlinarith [sq_abs (G_coefficient n j.val)]
    have he : (delta * Real.sqrt (n : ℝ)) ^ 2 ≤
        (eLpNorm (G n) 2 unitMeasure).toReal ^ 2 := by
      calc
        _ = (n : ℝ) * delta ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
          ring
        _ ≤ _ := hc.trans hb
    have hle : delta * Real.sqrt (n : ℝ) ≤ (eLpNorm (G n) 2 unitMeasure).toReal :=
      (sq_le_sq₀ (mul_nonneg delta_pos.le (Real.sqrt_nonneg _)) ENNReal.toReal_nonneg).mp he
    exact (ENNReal.ofReal_le_ofReal hle).trans_eq (ENNReal.ofReal_toReal hG.eLpNorm_ne_top)
  · have ht : eLpNorm (G n) 2 unitMeasure = ⊤ := by
      by_contra ht
      exact hG ⟨(measurable_G n).aestronglyMeasurable, lt_top_iff_ne_top.mpr ht⟩
    rw [ht]
    exact le_top

end HilbertUMD.BinaryLogit
