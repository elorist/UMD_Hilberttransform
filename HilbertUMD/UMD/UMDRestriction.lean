import HilbertUMD.UMD.UMD

/-!
# Restricting UMD bounds to real subspaces

These results use the full sigma-finite martingale definition. Restricting
complex coefficients to real signs, and restricting the input and output
to isometric real subspaces, do not change the bound.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD

universe uΩ

/-- A complex UMD bound controls the same operator with real coefficients. -/
theorem UMDBound.restrictScalars_real
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F]
    {p : ℝ≥0∞} {T : E →L[ℂ] F} {C : ℝ≥0} (hC : UMDBound.{uΩ} p T C) :
    UMDBound.{uΩ} p (T.restrictScalars ℝ) C := by
  intro Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε
  have h := hC Ω mΩ μ hμ m hm ℱ hℱ f hf (fun k => (ε k : ℂ))
    (fun k => by simpa using hε k)
  have ht : martingaleTransform T (fun k => (ε k : ℂ)) f =
      martingaleTransform (T.restrictScalars ℝ) ε f := by
    funext x
    apply Finset.sum_congr rfl
    intro k _
    exact algebraMap_smul ℂ (ε k) (T (f k.succ x - f k.castSucc x))
  rwa [ht] at h

/-- Pull back a UMD bound through an isometric intertwining of operators. -/
theorem UMDBound.of_isometric_intertwining
    {𝕜 E F E' F' : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (J : E →ₗᵢ[𝕜] E') (K : F →ₗᵢ[𝕜] F')
    {T : E →L[𝕜] F} {S : E' →L[𝕜] F'}
    (hST : ∀ x, S (J x) = K (T x))
    {p : ℝ≥0∞} (hp : 1 ≤ p) {C : ℝ≥0} (hC : UMDBound.{uΩ} p S C) :
    UMDBound.{uΩ} p T C := by
  intro Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε
  have h := hC Ω mΩ μ hμ m hm ℱ hℱ (fun k x => J (f k x))
    (hf.map hp J.toContinuousLinearMap) ε hε
  have ht : martingaleTransform S ε (fun k x => J (f k x)) =
      fun x => K (martingaleTransform T ε f x) := by
    funext x
    simp only [martingaleTransform, ← map_sub J, hST, map_sum, map_smul]
  have hd : differenceSum (fun k x => J (f k x)) = fun x => J (differenceSum f x) :=
    funext (differenceSum_map J.toContinuousLinearMap f)
  rw [ht, hd] at h
  have hnK : eLpNorm (fun x => K (martingaleTransform T ε f x)) p μ =
      eLpNorm (martingaleTransform T ε f) p μ :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun x => K.norm_map _)
  have hnJ : eLpNorm (fun x => J (differenceSum f x)) p μ =
      eLpNorm (differenceSum f) p μ :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun x => J.norm_map _)
  rwa [hnK, hnJ] at h

end HilbertUMD
