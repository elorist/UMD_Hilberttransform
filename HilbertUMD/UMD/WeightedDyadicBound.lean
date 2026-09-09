import HilbertUMD.UMD.DyadicProbabilityApproximation

/-! The uniform dyadic bound extends to every finite weighted binary tree. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace HilbertUMD

theorem leafL2Norm_sq_mean {G : Type*} [Norm G] (n : ℕ) (f : Leaf n → G) :
    leafL2Norm n f ^ 2 = leafMean (𝕜 := ℝ) n (fun i => ‖f i‖ ^ 2) := by
  rw [leafL2Norm, Real.sq_sqrt (by positivity)]
  simp only [leafMean, smul_eq_mul, inv_pow]

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def FiniteWeightedTerminalBound (T : E →L[𝕜] F) (C : ℝ≥0) : Prop :=
  ∀ (n m : ℕ) (b : WeightedTree.Bias n), WeightedTree.Valid b →
  ∀ (r : Fin (m + 1) → ℕ), Monotone r → (∀ k, r k ≤ n) →
  ∀ (f : Leaf n → E) (ε : Fin m → 𝕜), (∀ k, ‖ε k‖ = 1) →
    WeightedTree.mean n b (fun i =>
      ‖martingaleTransform T ε (fun k => WeightedTree.average n b (r k) f) i‖ ^ 2) ≤
        (C : ℝ) ^ 2 * WeightedTree.mean n b (fun i => ‖f i‖ ^ 2)

namespace WeightedTree

theorem bound_code {T : E →L[𝕜] F} {C : ℝ≥0}
    (h : FiniteDyadicSampledTerminalBound T C)
    (L n m : ℕ) (s : Code L n) (r : Fin (m + 1) → ℕ)
    (hr : Monotone r) (hn : ∀ k, r k ≤ n)
    (f : Leaf n → E) (ε : Fin m → 𝕜) (hε : ∀ k, ‖ε k‖ = 1) :
    mean n (bias s) (fun i =>
      ‖martingaleTransform T ε (fun k => average n (bias s) (r k) f) i‖ ^ 2) ≤
        (C : ℝ) ^ 2 * mean n (bias s) (fun i => ‖f i‖ ^ 2) := by
  let g : Leaf (depth L n) → E := fun i => f (decode L n s i)
  let q : Leaf n → F := martingaleTransform T ε (fun k => average n (bias s) (r k) f)
  have hp : martingaleTransform T ε
      (fun k => leafAverage (𝕜 := 𝕜) (depth L n) (depth L (r k)) g) =
      fun i => q (decode L n s i) := by
    funext i
    apply Finset.sum_congr rfl
    intro k _
    simp only [g, leafAverage_real (𝕜 := 𝕜),
      leafAverage_decode L n (r k.succ) (hn k.succ),
      leafAverage_decode L n (r k.castSucc) (hn k.castSucc)]
  have hb := h (depth L n) m (fun k => depth L (r k))
    ((depth_mono L).comp hr) (fun k => depth_mono L (hn k)) g ε hε
  rw [hp, eLpNorm_leafUniform_two, eLpNorm_leafUniform_two,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg] at hb
  have hnorm : leafL2Norm (depth L n) (fun i => q (decode L n s i)) ≤
      (C : ℝ) * leafL2Norm (depth L n) g := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg C.coe_nonneg (Real.sqrt_nonneg _))).mp hb
  have hsq : leafL2Norm (depth L n) (fun i => q (decode L n s i)) ^ 2 ≤
      ((C : ℝ) * leafL2Norm (depth L n) g) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
  rw [mul_pow, leafL2Norm_sq_mean, leafL2Norm_sq_mean] at hsq
  change leafMean (𝕜 := ℝ) (depth L n) (fun i => ‖q (decode L n s i)‖ ^ 2) ≤
    (C : ℝ) ^ 2 * leafMean (𝕜 := ℝ) (depth L n) (fun i => ‖f (decode L n s i)‖ ^ 2) at hsq
  rw [leafMean_decode L n s (fun i => ‖q i‖ ^ 2),
    leafMean_decode L n s (fun i => ‖f i‖ ^ 2)] at hsq
  exact hsq

omit [IsScalarTower ℝ 𝕜 E] in
theorem continuous_transform_energy (n m : ℕ) (r : Fin (m + 1) → ℕ)
    (T : E →L[𝕜] F) (f : Leaf n → E) (ε : Fin m → 𝕜) :
    Continuous (fun b : Bias n => mean n b (fun i =>
      ‖martingaleTransform T ε (fun k => average n b (r k) f) i‖ ^ 2)) := by
  have hq (i : Leaf n) : Continuous (fun b : Bias n =>
      martingaleTransform T ε (fun k => average n b (r k) f) i) := by
    apply continuous_finsetSum
    intro k _
    exact (T.continuous.comp ((continuous_average n (r k.succ) f i).sub
      (continuous_average n (r k.castSucc) f i))).const_smul (ε k)
  simp only [mean_eq_sum, smul_eq_mul]
  exact continuous_finsetSum _ (fun i _ => (continuous_mass n i).mul ((hq i).norm.pow 2))

end WeightedTree

theorem FiniteDyadicSampledTerminalBound.weighted {T : E →L[𝕜] F} {C : ℝ≥0}
    (h : FiniteDyadicSampledTerminalBound T C) : FiniteWeightedTerminalBound T C := by
  intro n m b hb r hr hn f ε hε
  have hlim := WeightedTree.tendsto_bias_approximatingCode b hb
  apply le_of_tendsto_of_tendsto
    ((WeightedTree.continuous_transform_energy n m r T f ε).tendsto b |>.comp hlim)
    ((continuous_const.mul (WeightedTree.continuous_mean n (fun i => ‖f i‖ ^ 2))).tendsto b |>.comp hlim)
  exact Eventually.of_forall (fun L => WeightedTree.bound_code h L n m
    (WeightedTree.approximatingCode L b) r hr hn f ε hε)

end HilbertUMD
