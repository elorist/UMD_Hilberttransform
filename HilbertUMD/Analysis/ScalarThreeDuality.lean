import HilbertUMD.Analysis.ScalarLpDualRepresentation
import HilbertUMD.Analysis.MixedLpNorming
import HilbertUMD.Hilbert.HilbertThreeDual

/-! Isometric scalar duality between real L3 and L(3/2). -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal

namespace HilbertUMD.ScalarThreeDuality

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

private def embed : ℝ →L[ℝ] (Unit → ℝ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ

private def project : (Unit → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj ()

private theorem norm_embedLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : Lp ℝ p μ) :
    ‖embed.compLpL p μ w‖ = ‖w‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [embed.coeFn_compLpL w] with x hx
  rw [hx]
  exact pi_norm_const _

private theorem norm_projectLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : Lp (Unit → ℝ) p μ) :
    ‖project.compLpL p μ g‖ = CubicLp.l1Norm μ p g := by
  rw [CubicLp.l1Norm_apply, Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [project.coeFn_compLpL g, (CubicLp.toL1 (ι := Unit)).coeFn_compLpL g] with x hp ht
  rw [hp, ht, CubicLp.norm_toL1]
  simp [project, Real.norm_eq_abs]

/-- Scalar L(3/2) is normed by the L3 unit ball. -/
theorem norm_le_of_unit_tests (w : Lp ℝ (3 / 2) μ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ g : Lp ℝ 3 μ, ‖g‖ ≤ 1 → |∫ x, g x * w x ∂μ| ≤ M) : ‖w‖ ≤ M := by
  rw [← norm_embedLp μ w]
  apply CubicLp.norm_le_of_l1_unit_tests μ (q := 3)
    (by apply (ENNReal.toReal_lt_toReal (by simp) (by finiteness)).mp; norm_num)
    (by finiteness) (by norm_num) (by simp) _ M hM
  intro g hg
  have hb := h (project.compLpL 3 μ g) ((norm_projectLp μ g).trans_le hg)
  have he : (∫ x, ∑ i, embed.compLpL (3 / 2) μ w x i * g x i ∂μ) =
      ∫ x, project.compLpL 3 μ g x * w x ∂μ := by
    apply integral_congr_ae
    filter_upwards [embed.coeFn_compLpL w, project.coeFn_compLpL g] with x hw hgp
    rw [hw, hgp]
    simp [embed, project, mul_comm]
  rw [he]
  exact hb

/-- The canonical integral pairing with L3. -/
def pairing : Lp ℝ (3 / 2) μ →L[ℝ] StrongDual ℝ (Lp ℝ 3 μ) :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ (3 / 2) 3

theorem pairing_apply (w : Lp ℝ (3 / 2) μ) (f : Lp ℝ 3 μ) :
    pairing μ w f = ∫ x, f x * w x ∂μ := by
  rw [pairing, ContinuousLinearMap.lpPairing_eq_integral]
  simp only [ContinuousLinearMap.mul_apply', mul_comm]

theorem norm_pairing (w : Lp ℝ (3 / 2) μ) : ‖pairing μ w‖ = ‖w‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    rw [pairing_apply, Real.norm_eq_abs]
    simpa only [mul_comm] using HilbertThreeDual.abs_pairing_le μ f w
  · apply norm_le_of_unit_tests μ w _ (norm_nonneg _)
    intro f hf
    rw [← pairing_apply]
    exact ((pairing μ w).le_opNorm f).trans (mul_le_of_le_one_right (norm_nonneg _) hf)

theorem pairing_surjective : Function.Surjective (pairing μ) := by
  intro ℓ
  obtain ⟨w, hw⟩ := ScalarLpDualRepresentation.exists_representation μ ℓ
  refine ⟨w, ?_⟩
  ext f
  rw [pairing_apply, hw]

/-- The scalar representation theorem with the exact operator norm. -/
def representation : StrongDual ℝ (Lp ℝ 3 μ) ≃ₗᵢ[ℝ] Lp ℝ (3 / 2) μ :=
  (LinearIsometryEquiv.ofSurjective
    ({ (pairing μ).toLinearMap with norm_map' := norm_pairing μ } :
      Lp ℝ (3 / 2) μ →ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ 3 μ)) (pairing_surjective μ)).symm

theorem representation_pairing (ℓ : StrongDual ℝ (Lp ℝ 3 μ)) (f : Lp ℝ 3 μ) :
    ℓ f = ∫ x, f x * representation μ ℓ x ∂μ := by
  have he : pairing μ (representation μ ℓ) = ℓ :=
    (representation μ).symm_apply_apply ℓ
  exact (congrArg (fun L => L f) he).symm.trans (pairing_apply μ _ f)

end HilbertUMD.ScalarThreeDuality
