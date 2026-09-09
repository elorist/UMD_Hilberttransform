import HilbertUMD.UMD.FiniteFiltrationModel
import HilbertUMD.UMD.WeightedTreeMeasure
import HilbertUMD.UMD.WeightedDyadicBound

/-! Transfer the weighted binary-tree bound to finite probability filtrations. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal

namespace HilbertUMD

theorem WeightedTree.lpNorm_comp_eq_sqrt_mean {Ω G : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup G] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (φ : Ω → Leaf n) (hφ : Measurable φ)
    (b : WeightedTree.Bias n) (hb : ∀ i, WeightedTree.mass n b i = (μ.map φ).real {i})
    (f : Leaf n → G) :
    lpNorm (fun x => f (φ x)) 2 μ = Real.sqrt (WeightedTree.mean n b (fun i => ‖f i‖ ^ 2)) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (WeightedTree.comp_memLp μ φ hφ f).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [WeightedTree.integral_comp_eq_mean μ φ hφ b hb (fun i => ‖f i‖ ^ 2)]
  simp only [Real.sqrt_eq_rpow, one_div]

universe uΩ

theorem FiniteWeightedTerminalBound.probabilityFinite
    {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {T : E →L[𝕜] F} {C : ℝ≥0} (h : FiniteWeightedTerminalBound T C) :
    ProbabilityFiniteTerminalBound.{uΩ} T C := by
  intro Ω mΩ μ hμ m _ ℱ hfinite g ε hε
  obtain ⟨n, r, φ, f, hr, hn, hφ, hσ, hg⟩ := exists_leaf_filtration_model ℱ hfinite g
  obtain ⟨b, hb, hmass⟩ := WeightedTree.exists_bias_map μ φ hφ
  let q : Leaf n → F := martingaleTransform T ε (fun k => WeightedTree.average n b (r k) f)
  have hnorm := Real.sqrt_le_sqrt (h n m b hb r hr hn f ε hε)
  rw [Real.sqrt_mul (sq_nonneg (C : ℝ)), Real.sqrt_sq C.coe_nonneg] at hnorm
  have hbound : eLpNorm (fun x => q (φ x)) 2 μ ≤
      (C : ℝ≥0∞) * eLpNorm (fun x => f (φ x)) 2 μ := by
    rw [← ofReal_lpNorm (WeightedTree.comp_memLp μ φ hφ q),
      ← ofReal_lpNorm (WeightedTree.comp_memLp μ φ hφ f),
      WeightedTree.lpNorm_comp_eq_sqrt_mean μ φ hφ b hmass q,
      WeightedTree.lpNorm_comp_eq_sqrt_mean μ φ hφ b hmass f,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal hnorm
  have hfg : (fun x => f (φ x)) = g := funext (fun x => (hg x).symm)
  have hce (k : Fin (m + 1)) : (fun x => WeightedTree.average n b (r k) f (φ x)) =ᵐ[μ]
      μ[g | ℱ k] := by
    have hk := WeightedTree.average_comp_ae_condExp μ φ hφ b hmass (r k) f
    rwa [← hσ k, hfg] at hk
  have hqa : (fun x => q (φ x)) =ᵐ[μ] martingaleTransform T ε (fun k => μ[g | ℱ k]) := by
    filter_upwards [ae_all_iff.mpr hce] with x hx
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun v : E => ε k • T v) (congrArg₂ (· - ·) (hx k.succ) (hx k.castSucc))
  rwa [eLpNorm_congr_ae hqa, hfg] at hbound

end HilbertUMD
