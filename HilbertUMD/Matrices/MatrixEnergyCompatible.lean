import HilbertUMD.Matrices.MatrixCompatible
import HilbertUMD.Matrices.MatrixEnergy

/-! Connecting the checked scalar-family matrix energy to genuine vector L³. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

theorem CubicLp.ofReal_l1Norm_eq {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : CubicLp.Space (ι := ι) μ p) :
    ENNReal.ofReal (CubicLp.l1Norm μ p f) = eLpNorm (fun x => ∑ i, |f x i|) p μ := by
  rw [CubicLp.l1Norm_apply, ofReal_norm, Lp.enorm_def]
  apply eLpNorm_congr_norm_ae
  filter_upwards [(CubicLp.toL1 (ι := ι)).coeFn_compLpL f] with x hx
  rw [hx, CubicLp.norm_toL1]
  exact (abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (f x i)))).symm

/-- The original matrix cubic-energy bound on the genuine L³(l¹) domain.
Coordinate representatives and the nonnegative mass norm are identified here;
no pointwise linear action on arbitrary representatives is assumed. -/
theorem ScalarMatrixData.action_energy_bound {η M P : ℝ}
    (R : ScalarMatrixData μ η M P) (hη : η ^ 2 = 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (c : ℕ → ℝ) (hc : ∀ k, c k ^ 2 = 1) (n : ℕ)
    (f : CubicLp.Space (ι := Leaf n) μ 3) (hf : CubicLp.Nonnegative μ f) :
    CubicLp.energy μ (MatrixCompatible.action μ η c n 3 R.atThree) f ≤
      ((n : ℝ) * (2 * M ^ 2 + 2 * P)) * CubicLp.l1Norm μ 3 f ^ 3 := by
  let F : Leaf n → Lp ℝ 3 μ := fun j => (ScalarLp.coordinate j).compLpL 3 μ f
  have hF : ∀ᵐ x ∂μ, ∀ j, F j x = f x j :=
    ae_all_iff.mpr (fun j => (ScalarLp.coordinate j).coeFn_compLpL f)
  have hFpos : ∀ᵐ x ∂μ, ∀ j, 0 ≤ F j x := by
    filter_upwards [hF, hf] with x hx hf
    intro j
    rw [hx j]
    exact hf j
  have hG : eLpNorm (fun x => ∑ j, F j x) 3 μ ≤ ENNReal.ofReal (CubicLp.l1Norm μ 3 f) := by
    rw [CubicLp.ofReal_l1Norm_eq]
    apply le_of_eq
    apply eLpNorm_congr_ae
    filter_upwards [hF, hf] with x hx hf
    apply Finset.sum_congr rfl
    intro j _
    rw [hx j, abs_of_nonneg (hf j)]
  have he := R.cubic_energy_bound hη hM hP c hc n F hFpos
    (CubicLp.l1Norm μ 3 f) (apply_nonneg _ _) hG
  rw [MatrixCompatible.energy_action_eq]
  calc
    _ = ∫ x, ∑ i, F i x * (treeMatrix η c n (fun j => R.atThree (F j) x) i) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hF] with x hx
      simp only [treeEnergy, zero_add]
      apply Finset.sum_congr rfl
      intro i _
      rw [hx i]
    _ ≤ _ := he

end HilbertUMD
