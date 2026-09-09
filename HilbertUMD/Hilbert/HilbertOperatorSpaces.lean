import HilbertUMD.Hilbert.HilbertConstant
import HilbertUMD.Foundations.OperatorSpaces

/-! Proved graph-space factorizations for the principal-value Hilbert bounds. -/

noncomputable section
open scoped ENNReal NNReal

namespace HilbertUMD

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem HilbertBound.of_graphSpace {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ 𝕜 (GraphSpace T)]
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    {p : ℝ≥0∞} {C : ℝ≥0}
    (hC : HilbertBound p (ContinuousLinearMap.id 𝕜 (GraphSpace T)) C) :
    HilbertBound p (asL1Operator n T h) C := by
  have hA : ‖l1ToGraph hT‖₊ ≤ 1 := by exact_mod_cast l1ToGraph_norm_le hT
  have hB : ‖graphToRange T‖₊ ≤ 1 := by exact_mod_cast graphToRange_norm_le T
  have hh := (hC.precomp (l1ToGraph hT)).postcomp (graphToRange T)
  have hb : ‖graphToRange T‖₊ * (C * ‖l1ToGraph hT‖₊) ≤ C := by
    calc
      _ ≤ 1 * (C * 1) := mul_le_mul' hB (mul_le_mul' le_rfl hA)
      _ = C := by simp
  have hh' := hh.mono hb
  simpa only [ContinuousLinearMap.id_comp, graph_factorization hT h] using hh'

theorem hilbertConstant_matrix_le_graphSpace {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ 𝕜 (GraphSpace T)]
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) (p : ℝ≥0∞) :
    hilbertConstant p (asL1Operator n T h) ≤
      hilbertConstant p (ContinuousLinearMap.id 𝕜 (GraphSpace T)) :=
  le_hilbertConstant fun _ hC => hilbertConstant_le (hC.of_graphSpace hT h)

/-- The n+1 upper bound follows from the displayed Hilbert-target bound one.
The factorization itself uses no admitted analytic results. -/
theorem hilbertBound_two_graph_of_hilbert {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (HSpace 𝕜 n)] [IsScalarTower ℝ 𝕜 (HSpace 𝕜 n)]
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ 𝕜 (GraphSpace T)]
    (hT : TransferAssumptions T)
    (hH : HilbertBound 2 (ContinuousLinearMap.id 𝕜 (HSpace 𝕜 n)) 1) :
    HilbertBound 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) ((n : ℝ≥0) + 1) := by
  have hh := (hH.precomp (graphToHilbert T)).postcomp (hilbertToGraph hT)
  have hb : ‖hilbertToGraph hT‖₊ * (1 * ‖graphToHilbert T‖₊) ≤ (n : ℝ≥0) + 1 := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_mul, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast,
      coe_nnnorm, one_mul]
    calc
      ‖hilbertToGraph hT‖ * ‖graphToHilbert T‖
          ≤ Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) :=
        mul_le_mul (hilbertToGraph_norm_le hT) (graphToHilbert_norm_le T)
          (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = (n : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  have hh' := hh.mono hb
  simpa only [ContinuousLinearMap.id_comp, hilbert_graph_factorization hT] using hh'

theorem hilbertConstant_two_graph_le_of_hilbert {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (HSpace 𝕜 n)] [IsScalarTower ℝ 𝕜 (HSpace 𝕜 n)]
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ 𝕜 (GraphSpace T)]
    (hT : TransferAssumptions T)
    (hH : HilbertBound 2 (ContinuousLinearMap.id 𝕜 (HSpace 𝕜 n)) 1) :
    hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) ≤ (n : ℝ≥0∞) + 1 := by
  simpa using hilbertConstant_le (hilbertBound_two_graph_of_hilbert hT hH)

end HilbertUMD
