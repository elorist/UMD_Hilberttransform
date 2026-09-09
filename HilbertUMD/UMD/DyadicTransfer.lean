import HilbertUMD.UMD.DyadicTerminal
import HilbertUMD.Foundations.OperatorSpaces

/-! Checked finite dyadic scalar operators used to apply the sharp transfer. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace HilbertUMD

variable {𝕜 : Type*} [RCLike 𝕜]

def leafAverageLinear (d k : ℕ) : (Leaf d → 𝕜) →ₗ[𝕜] (Leaf d → 𝕜) where
  toFun := leafAverage (𝕜 := 𝕜) d k
  map_add' f g := by
    ext i
    simp [leafAverage, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext i
    simp only [leafAverage, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, RingHom.id_apply]
    ring

/-- The actual deterministic scalar dyadic transform acting on terminal values. -/
def dyadicScalar (d : ℕ) (ε : Fin d → 𝕜) : (Leaf d → 𝕜) →ₗ[𝕜] (Leaf d → 𝕜) :=
  ∑ k : Fin d, ε k • (leafAverageLinear d k.succ.val - leafAverageLinear d k.castSucc.val)

theorem dyadicScalar_apply (d : ℕ) (ε : Fin d → 𝕜) (f : Leaf d → 𝕜) :
    dyadicScalar d ε f = martingaleTransform (ContinuousLinearMap.id 𝕜 𝕜) ε
      (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val f) := by
  ext i
  simp [dyadicScalar, leafAverageLinear, martingaleTransform, Finset.sum_apply]

theorem coordinateAction_dyadicScalar {n : ℕ} (d : ℕ) (ε : Fin d → 𝕜)
    (f : Leaf d → Vec 𝕜 n) :
    coordinateAction (dyadicScalar d ε) f =
      martingaleTransform (ContinuousLinearMap.id 𝕜 (Vec 𝕜 n)) ε
        (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val f) := by
  ext i j
  simp [coordinateAction, dyadicScalar, leafAverageLinear, leafAverage, martingaleTransform,
    Finset.sum_apply]

/-- Orthogonality, followed by the checked terminal-value reduction, gives
the scalar contraction required by the transfer theorem. -/
theorem dyadicScalar_contraction (d : ℕ) (ε : Fin d → 𝕜) (hε : ∀ k, ‖ε k‖ = 1)
    (g : Leaf d → 𝕜) : (∑ i, ‖dyadicScalar d ε g i‖ ^ 2) ≤ ∑ i, ‖g i‖ ^ 2 := by
  have hbound : FiniteDyadicTerminalBound 2 (ContinuousLinearMap.id 𝕜 𝕜) 1 :=
    UMDBound.finiteDyadicTerminal_two.{0} umdBound_two_hilbert
  have h := (finiteDyadicTerminalBound_two_iff _ _).mp hbound d g ε hε
  rw [← dyadicScalar_apply] at h
  simp only [leafL2Norm_eq_finiteL2 (𝕜 := 𝕜), NNReal.coe_one, one_mul] at h
  have hs : 0 < Real.sqrt ((2 : ℝ)⁻¹ ^ d) := Real.sqrt_pos.mpr (by positivity)
  have hn : finiteL2 (normSeminorm 𝕜 𝕜) (dyadicScalar d ε g) ≤
      finiteL2 (normSeminorm 𝕜 𝕜) g := (mul_le_mul_iff_right₀ hs).mp h
  have hsq : finiteL2 (normSeminorm 𝕜 𝕜) (dyadicScalar d ε g) ^ 2 ≤
      finiteL2 (normSeminorm 𝕜 𝕜) g ^ 2 := by
    apply pow_le_pow_left₀ _ hn 2
    exact finiteL2_nonneg _ _
  simpa only [finiteL2_sq, coe_normSeminorm] using hsq

theorem ofLp_leafAverage_toLp {n : ℕ} (d k : ℕ) (f : Leaf d → Vec 𝕜 n) (i : Leaf d) :
    WithLp.ofLp (leafAverage (𝕜 := 𝕜) d k (fun j => (WithLp.toLp 1 (f j) : L1Vec 𝕜 n)) i) =
      leafAverage (𝕜 := 𝕜) d k f i := by
  simp only [leafAverage, WithLp.ofLp_smul, WithLp.ofLp_sum]

theorem asL1_dyadic_transform {n : ℕ} (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n)
    (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) (d : ℕ) (ε : Fin d → 𝕜)
    (g : Leaf d → Vec 𝕜 n) :
    martingaleTransform (asL1Operator n T h) ε
      (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val
        (fun i => (WithLp.toLp 1 (g i) : L1Vec 𝕜 n))) =
      fun i => T (coordinateAction (dyadicScalar d ε) g i) := by
  rw [coordinateAction_dyadicScalar]
  funext i
  rw [martingaleTransform_eq_map]
  change T (WithLp.ofLp (martingaleTransform (ContinuousLinearMap.id 𝕜 (L1Vec 𝕜 n)) ε
      (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val
        (fun j => (WithLp.toLp 1 (g j) : L1Vec 𝕜 n))) i)) = _
  simp only [martingaleTransform, ContinuousLinearMap.id_apply, WithLp.ofLp_sum,
    WithLp.ofLp_smul, WithLp.ofLp_sub, ofLp_leafAverage_toLp]

theorem leafL2Norm_toL1 {n : ℕ} (d : ℕ) (g : Leaf d → Vec 𝕜 n) :
    leafL2Norm d (fun i => (WithLp.toLp 1 (g i) : L1Vec 𝕜 n)) =
      Real.sqrt ((2 : ℝ)⁻¹ ^ d) * finiteL2 (l1Norm n) g := by
  rw [leafL2Norm_eq_finiteL2 (𝕜 := 𝕜)]
  congr 1
  unfold finiteL2
  congr 1
  funext i
  exact PiLp.norm_eq_of_L1 _

theorem leafL2Norm_graph {n : ℕ} (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) (d : ℕ)
    (f : Leaf d → GraphSpace T) :
    leafL2Norm d f = Real.sqrt ((2 : ℝ)⁻¹ ^ d) *
      finiteL2 (graphNorm T) (fun i => (f i : Vec 𝕜 n)) := by
  rw [leafL2Norm_eq_finiteL2 (𝕜 := 𝕜)]
  rfl

/-- Exact transfer of the finite dyadic terminal bound. The underlying
scalar dyadic operator is proved contractive above, and the graph estimate
is the checked decomposition theorem, without a reduction admission. -/
theorem finiteDyadicTerminal_graph_transfer {n : ℕ}
    {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} (hT : TransferAssumptions T)
    (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) (C : ℝ≥0)
    (hC : FiniteDyadicTerminalBound 2 (asL1Operator n T h) C) :
    FiniteDyadicTerminalBound 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T))
      ⟨Real.sqrt ((C : ℝ) ^ 2 + 2 * ((n : ℝ) + 1)), Real.sqrt_nonneg _⟩ := by
  apply (finiteDyadicTerminalBound_two_iff _ _).mpr
  intro d f ε hε
  have hs : 0 < Real.sqrt ((2 : ℝ)⁻¹ ^ d) := Real.sqrt_pos.mpr (by positivity)
  have hM (g : Leaf d → Vec 𝕜 n) :
      finiteL2 ((normSeminorm 𝕜 (Vec 𝕜 n)).comp T) (coordinateAction (dyadicScalar d ε) g) ≤
        (C : ℝ) * finiteL2 (l1Norm n) g := by
    have hc := (finiteDyadicTerminalBound_two_iff _ _).mp hC d
      (fun i => (WithLp.toLp 1 (g i) : L1Vec 𝕜 n)) ε hε
    rw [asL1_dyadic_transform, leafL2Norm_toL1, leafL2Norm_eq_finiteL2 (𝕜 := 𝕜)] at hc
    change Real.sqrt ((2 : ℝ)⁻¹ ^ d) *
      finiteL2 ((normSeminorm 𝕜 (Vec 𝕜 n)).comp T) (coordinateAction (dyadicScalar d ε) g) ≤ _ at hc
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      _ ≤ (C : ℝ) * (Real.sqrt ((2 : ℝ)⁻¹ ^ d) * finiteL2 (l1Norm n) g) := hc
      _ = _ := by ring
  let fv : Leaf d → Vec 𝕜 n := fun i => f i
  have hf := finiteL2_scalar_transfer hT (dyadicScalar d ε) (dyadicScalar_contraction d ε hε)
    (C : ℝ) C.coe_nonneg hM fv
  have hsq : 0 ≤ (C : ℝ) ^ 2 + 2 * ((n : ℝ) + 1) := by positivity
  have hfn : finiteL2 (graphNorm T) (coordinateAction (dyadicScalar d ε) fv) ≤
      Real.sqrt ((C : ℝ) ^ 2 + 2 * ((n : ℝ) + 1)) * finiteL2 (graphNorm T) fv := by
    apply (sq_le_sq₀ (finiteL2_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg _) (finiteL2_nonneg _ _))).mp
    rw [mul_pow, Real.sq_sqrt hsq]
    exact hf
  rw [leafL2Norm_graph, leafL2Norm_graph]
  change Real.sqrt ((2 : ℝ)⁻¹ ^ d) *
      finiteL2 (graphNorm T) (martingaleTransform (ContinuousLinearMap.id 𝕜 (Vec 𝕜 n)) ε
        (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val fv)) ≤ _
  rw [← coordinateAction_dyadicScalar]
  calc
    _ ≤ Real.sqrt ((2 : ℝ)⁻¹ ^ d) *
        (Real.sqrt ((C : ℝ) ^ 2 + 2 * ((n : ℝ) + 1)) * finiteL2 (graphNorm T) fv) :=
      mul_le_mul_of_nonneg_left hfn hs.le
    _ = _ := by
      change Real.sqrt ((2 : ℝ)⁻¹ ^ d) *
        (Real.sqrt ((C : ℝ) ^ 2 + 2 * ((n : ℝ) + 1)) * finiteL2 (graphNorm T) fv) =
          Real.sqrt ((C : ℝ) ^ 2 + 2 * ((n : ℝ) + 1)) *
            (Real.sqrt ((2 : ℝ)⁻¹ ^ d) * finiteL2 (graphNorm T) fv)
      ring

end HilbertUMD
