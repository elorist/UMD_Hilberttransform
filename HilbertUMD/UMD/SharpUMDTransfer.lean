import HilbertUMD.UMD.DyadicTransfer
import HilbertUMD.Interfaces.MartingaleReduction

/-!
# Sharp UMD transfer for the actual operator constants

The decomposition and terminal-value argument gives a sharp transfer for
finite dyadic tests. The proved real and complex Paley-Walsh reductions extend this
to the full UMD constant.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace HilbertUMD

def sharpTransferBound (n : ℕ) (C : ℝ≥0) : ℝ≥0 :=
  ⟨Real.sqrt ((C : ℝ) ^ 2 + 2 * ((n : ℝ) + 1)), Real.sqrt_nonneg _⟩

theorem sharpTransferBound_sq (n : ℕ) (C : ℝ≥0) :
    sharpTransferBound n C ^ 2 = C ^ 2 + 2 * ((n : ℝ≥0) + 1) := by
  apply NNReal.coe_injective
  change Real.sqrt ((C : ℝ) ^ 2 + 2 * ((n : ℝ) + 1)) ^ 2 = _
  rw [Real.sq_sqrt (by positivity)]
  simp

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- Fully checked transfer conditional on an explicit, general-to-dyadic
reduction interface for the graph space. -/
theorem UMDBound.sharp_graph_of_reduction
    {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} [NormedSpace ℝ (GraphSpace T)]
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    (hReduction : ∀ C : ℝ≥0,
      FiniteDyadicTerminalBound 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) C →
        UMDBound.{0} 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) C)
    {C : ℝ≥0} (hC : UMDBound.{0} 2 (asL1Operator n T h) C) :
    UMDBound.{0} 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) (sharpTransferBound n C) :=
  hReduction _ (finiteDyadicTerminal_graph_transfer hT h C hC.finiteDyadicTerminal_two)

/-- Uses the proved Paley-Walsh reduction over either scalar field. -/
theorem UMDBound.sharp_graph {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ 𝕜 (GraphSpace T)]
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    {C : ℝ≥0} (hC : UMDBound.{0} 2 (asL1Operator n T h) C) :
    UMDBound.{0} 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) (sharpTransferBound n C) :=
  hC.sharp_graph_of_reduction hT h
    (fun C hC => Interfaces.umdBound_of_finiteDyadicTerminalBound _ C hC)

/-- Uses the proved complex Paley-Walsh reduction. -/
theorem UMDBound.sharp_graph_complex {T : Vec ℂ n →ₗ[ℂ] Vec ℂ n}
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ ℂ (GraphSpace T)]
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    {C : ℝ≥0} (hC : UMDBound.{0} 2 (asL1Operator n T h) C) :
    UMDBound.{0} 2 (ContinuousLinearMap.id ℂ (GraphSpace T)) (sharpTransferBound n C) :=
  hC.sharp_graph_of_reduction hT h
    (fun C hC => Interfaces.complex_umdBound_of_finiteDyadicTerminalBound _ C hC)

theorem ennreal_iInf_sq {ι : Sort*} (f : ι → ℝ≥0∞) :
    (⨅ i, f i) ^ 2 = ⨅ i, f i ^ 2 := by
  have hi := (ENNReal.orderIsoRpow (2 : ℝ) (by norm_num)).map_iInf f
  change (⨅ i, f i) ^ (2 : ℝ) = ⨅ i, (f i) ^ (2 : ℝ) at hi
  simpa only [ENNReal.rpow_two] using hi

/-- Passage to the infimum of all admissible bounds is checked in the
extended nonnegative reals, including the infinite-constant case. -/
theorem umdConstant_sharp_graph_of_bounds
    {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} [NormedSpace ℝ (GraphSpace T)]
    (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    (hTransfer : ∀ C : ℝ≥0, UMDBound.{0} 2 (asL1Operator n T h) C →
      UMDBound.{0} 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) (sharpTransferBound n C)) :
    umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) ^ 2 ≤
      umdConstant.{0} 2 (asL1Operator n T h) ^ 2 + 2 * ((n : ℝ≥0∞) + 1) := by
  conv_rhs => rw [umdConstant]
  simp_rw [ennreal_iInf_sq, ENNReal.iInf_add]
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  calc
    _ ≤ (sharpTransferBound n C : ℝ≥0∞) ^ 2 := by
      exact pow_le_pow_left₀ bot_le (umdConstant_le (hTransfer C hC)) 2
    _ = _ := by
      rw [← ENNReal.coe_pow, sharpTransferBound_sq]
      push_cast
      rfl

/-- Proposition 2.2, squared sharp upper inequality for the actual
UMD constants. Uses the proved Paley-Walsh reduction. -/
theorem umdConstant_sharp_graph {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ 𝕜 (GraphSpace T)]
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) :
    umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) ^ 2 ≤
      umdConstant.{0} 2 (asL1Operator n T h) ^ 2 + 2 * ((n : ℝ≥0∞) + 1) :=
  umdConstant_sharp_graph_of_bounds h (fun _ hC => hC.sharp_graph hT h)

/-- Complex specialization of the sharp transfer. -/
theorem umdConstant_sharp_graph_complex {T : Vec ℂ n →ₗ[ℂ] Vec ℂ n}
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ ℂ (GraphSpace T)]
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) :
    umdConstant.{0} 2 (ContinuousLinearMap.id ℂ (GraphSpace T)) ^ 2 ≤
      umdConstant.{0} 2 (asL1Operator n T h) ^ 2 + 2 * ((n : ℝ≥0∞) + 1) :=
  umdConstant_sharp_graph_of_bounds h (fun _ hC => hC.sharp_graph_complex hT h)

end HilbertUMD
