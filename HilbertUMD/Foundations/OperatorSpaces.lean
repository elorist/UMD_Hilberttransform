import HilbertUMD.Transfer.Transfer
import HilbertUMD.UMD.UMD
import HilbertUMD.UMD.MartingaleL2

/-!
# Operator factorization through the graph spaces

The lower half of the UMD transfer proposition is proved for the full
sigma-finite definition, using genuine continuous linear contractions.
-/

noncomputable section
open scoped ENNReal NNReal

namespace HilbertUMD

universe uΩ

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

def l1ToGraphLinear (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) :
    L1Vec 𝕜 n →ₗ[𝕜] GraphSpace T where
  toFun := WithLp.ofLp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def l1ToGraph {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} (hT : TransferAssumptions T) :
    L1Vec 𝕜 n →L[𝕜] GraphSpace T :=
  (l1ToGraphLinear T).mkContinuous 1 (fun x => by
    change graphNorm T (WithLp.ofLp x) ≤ 1 * ‖x‖
    simpa [PiLp.norm_eq_of_L1, l1Norm_eq] using graphNorm_le_l1 hT (WithLp.ofLp x))

theorem l1ToGraph_norm_le {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} (hT : TransferAssumptions T) :
    ‖l1ToGraph hT‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ (by norm_num) _

def graphToRangeLinear (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) :
    GraphSpace T →ₗ[𝕜] Vec 𝕜 n where
  toFun := T
  map_add' := T.map_add
  map_smul' := T.map_smul

def graphToRange (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : GraphSpace T →L[𝕜] Vec 𝕜 n :=
  (graphToRangeLinear T).mkContinuous 1 (fun x => by
    change ‖T x‖ ≤ 1 * max ‖T x‖ (sumNorm n x)
    rw [one_mul]
    exact le_max_left _ _)

theorem graphToRange_norm_le (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : ‖graphToRange T‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem graph_factorization {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} (hT : TransferAssumptions T)
    (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) :
    (graphToRange T).comp (l1ToGraph hT) = asL1Operator n T h := by
  ext x i
  rfl

/-- Every full UMD bound for the graph space is also a bound for its matrix. -/
theorem UMDBound.of_graphSpace {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (GraphSpace T)] (hT : TransferAssumptions T)
    (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) {p : ℝ≥0∞} {C : ℝ≥0}
    (hC : UMDBound.{uΩ} p (ContinuousLinearMap.id 𝕜 (GraphSpace T)) C) (hp : 1 ≤ p) :
    UMDBound.{uΩ} p (asL1Operator n T h) C := by
  have hA : ‖l1ToGraph hT‖₊ ≤ 1 := by exact_mod_cast l1ToGraph_norm_le hT
  have hB : ‖graphToRange T‖₊ ≤ 1 := by exact_mod_cast graphToRange_norm_le T
  have hh := (hC.precomp hp (l1ToGraph hT)).postcomp (graphToRange T)
  have hb : ‖graphToRange T‖₊ * (C * ‖l1ToGraph hT‖₊) ≤ C := by
    calc
      _ ≤ 1 * (C * 1) := mul_le_mul' hB (mul_le_mul' le_rfl hA)
      _ = C := by simp
  have hh' := hh.mono hb
  simpa only [ContinuousLinearMap.id_comp, graph_factorization hT h] using hh'

theorem umdConstant_matrix_le_graphSpace {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (GraphSpace T)] (hT : TransferAssumptions T)
    (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    umdConstant.{uΩ} p (asL1Operator n T h) ≤
      umdConstant.{uΩ} p (ContinuousLinearMap.id 𝕜 (GraphSpace T)) :=
  le_umdConstant fun _ hC => umdConstant_le (hC.of_graphSpace hT h hp)

theorem umdConstant_summation_le_xSpace [NormedSpace ℝ (XSpace 𝕜 n)] :
    umdConstant.{uΩ} 2 (summationOperator (𝕜 := 𝕜) n) ≤
      umdConstant.{uΩ} 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) :=
  umdConstant_matrix_le_graphSpace (summation_transferAssumptions n) (summation_le_l1 n)
    (by norm_num)

theorem umdConstant_signedDyadic_le_ySpace [NormedSpace ℝ (YSpace 𝕜 n)] :
    umdConstant.{uΩ} 2 (signedDyadicOperator (𝕜 := 𝕜) n) ≤
      umdConstant.{uΩ} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) :=
  umdConstant_matrix_le_graphSpace (signedDyadic_transferAssumptions n) (signedDyadic_le_l1 n)
    (by norm_num)

def graphToHilbertLinear (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) :
    GraphSpace T →ₗ[𝕜] HSpace 𝕜 n where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def graphToHilbert (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : GraphSpace T →L[𝕜] HSpace 𝕜 n :=
  (graphToHilbertLinear T).mkContinuous (Real.sqrt ((n : ℝ) + 1))
    (fun x => hilbertNorm_le_graphNorm T x)

theorem graphToHilbert_norm_le (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) :
    ‖graphToHilbert T‖ ≤ Real.sqrt ((n : ℝ) + 1) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

def hilbertToGraphLinear (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) :
    HSpace 𝕜 n →ₗ[𝕜] GraphSpace T where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def hilbertToGraph {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} (hT : TransferAssumptions T) :
    HSpace 𝕜 n →L[𝕜] GraphSpace T :=
  (hilbertToGraphLinear T).mkContinuous (Real.sqrt ((n : ℝ) + 1))
    (fun x => graphNorm_le_hilbert hT x)

theorem hilbertToGraph_norm_le {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} (hT : TransferAssumptions T) :
    ‖hilbertToGraph hT‖ ≤ Real.sqrt ((n : ℝ) + 1) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

theorem hilbert_graph_factorization {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    (hT : TransferAssumptions T) :
    (hilbertToGraph hT).comp (graphToHilbert T) =
      ContinuousLinearMap.id 𝕜 (GraphSpace T) := by
  ext x
  rfl

/-- The direct Hilbert-space comparison gives UMD bound n+1 for every graph
space satisfying the matrix estimates. This does not use a Hilbert/UMD comparison theorem. -/
theorem umdBound_two_graphSpace {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (HSpace 𝕜 n)] [NormedSpace ℝ (GraphSpace T)]
    (hT : TransferAssumptions T) :
    UMDBound.{uΩ} 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) ((n : ℝ≥0) + 1) := by
  have hH : UMDBound.{uΩ} 2 (ContinuousLinearMap.id 𝕜 (HSpace 𝕜 n)) 1 :=
    umdBound_two_hilbert
  have hh := (hH.precomp (by norm_num) (graphToHilbert T)).postcomp (hilbertToGraph hT)
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

theorem umdConstant_two_graphSpace_le {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (HSpace 𝕜 n)] [NormedSpace ℝ (GraphSpace T)]
    (hT : TransferAssumptions T) :
    umdConstant.{uΩ} 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) ≤ (n : ℝ≥0∞) + 1 := by
  simpa using umdConstant_le (umdBound_two_graphSpace hT)

end HilbertUMD
