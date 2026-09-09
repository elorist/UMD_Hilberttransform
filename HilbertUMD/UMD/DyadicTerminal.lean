import HilbertUMD.UMD.DyadicMartingale
import HilbertUMD.Transfer.Transfer
import HilbertUMD.UMD.MartingaleL2
import HilbertUMD.UMD.SampleSpaceLift

/-!
# Finite dyadic terminal-value bounds

The definition below is the concrete finite-model interface needed for the
operator Paley-Walsh reduction. This file contains only checked mathematics;
the reduction from all sample spaces is not built into the definition.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal
namespace HilbertUMD

universe uΩ

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Test every terminal function on the uniform binary tree, with denominator
equal to its terminal Lp norm and all unimodular deterministic coefficients. -/
def FiniteDyadicTerminalBound (p : ℝ≥0∞) (T : E →L[𝕜] F) (C : ℝ≥0) : Prop :=
  ∀ (d : ℕ) (f : Leaf d → E) (ε : Fin d → 𝕜), (∀ k, ‖ε k‖ = 1) →
    eLpNorm (martingaleTransform T ε
      (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val f)) p (leafUniform d) ≤
        (C : ℝ≥0∞) * eLpNorm f p (leafUniform d)

theorem finiteDyadicTerminalBound_two_iff (T : E →L[𝕜] F) (C : ℝ≥0) :
    FiniteDyadicTerminalBound 2 T C ↔
      ∀ (d : ℕ) (f : Leaf d → E) (ε : Fin d → 𝕜), (∀ k, ‖ε k‖ = 1) →
        leafL2Norm d (martingaleTransform T ε
          (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val f)) ≤
            (C : ℝ) * leafL2Norm d f := by
  unfold FiniteDyadicTerminalBound
  simp only [eLpNorm_leafUniform_two, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  apply forall_congr'
  intro d
  apply forall_congr'
  intro f
  apply forall_congr'
  intro ε
  exact imp_congr_right fun _ => ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (NNReal.coe_nonneg C) (Real.sqrt_nonneg _))

theorem leafL2Norm_signedLeafLift (d : ℕ) (f : Leaf d → E) :
    leafL2Norm (d + 1) (signedLeafLift d f) = leafL2Norm d f := by
  unfold leafL2Norm
  congr 1
  rw [Fintype.sum_sum_type]
  simp only [signedLeafLift, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, norm_neg]
  rw [pow_succ]
  ring

theorem eLpNorm_signedLeafLift (d : ℕ) (f : Leaf d → E) :
    eLpNorm (signedLeafLift d f) 2 (leafUniform (d + 1)) = eLpNorm f 2 (leafUniform d) := by
  rw [eLpNorm_leafUniform_two (d + 1), eLpNorm_leafUniform_two d, leafL2Norm_signedLeafLift]

/-- Relate the normalized dyadic L2 norm to the finite counting-measure norm. -/
theorem leafL2Norm_eq_finiteL2 (d : ℕ) (f : Leaf d → E) :
    leafL2Norm d f = Real.sqrt ((2 : ℝ)⁻¹ ^ d) * finiteL2 (normSeminorm 𝕜 E) f := by
  unfold leafL2Norm
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (finiteL2_nonneg _ _))).mp
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), finiteL2_sq]
  rfl

include 𝕜 in
theorem leafL2Norm_add_le (d : ℕ) (f g : Leaf d → E) :
    leafL2Norm d (f + g) ≤ leafL2Norm d f + leafL2Norm d g := by
  simp only [leafL2Norm_eq_finiteL2 (𝕜 := 𝕜), ← mul_add]
  exact mul_le_mul_of_nonneg_left (finiteL2_add_le _ _ _) (Real.sqrt_nonneg _)

theorem leafL2Norm_smul (d : ℕ) (c : 𝕜) (f : Leaf d → E) :
    leafL2Norm d (c • f) = ‖c‖ * leafL2Norm d f := by
  unfold leafL2Norm
  simp only [Pi.smul_apply, norm_smul, mul_pow, ← Finset.mul_sum]
  rw [show (2 : ℝ)⁻¹ ^ d * (‖c‖ ^ 2 * ∑ i, ‖f i‖ ^ 2) =
    ‖c‖ ^ 2 * ((2 : ℝ)⁻¹ ^ d * ∑ i, ‖f i‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

/-- Give the additional, independent sign its initial coefficient. -/
def prependSign {d : ℕ} (a : 𝕜) (ε : Fin d → 𝕜) : Fin (d + 1) → 𝕜 := Fin.cases a ε

theorem prependSign_norm {d : ℕ} (a : 𝕜) (ha : ‖a‖ = 1) (ε : Fin d → 𝕜)
    (hε : ∀ k, ‖ε k‖ = 1) : ∀ k, ‖prependSign a ε k‖ = 1 := by
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact ha
  · exact hε j

theorem liftedTerminal_transform_inl (d : ℕ) (T : E →L[𝕜] F)
    (a : 𝕜) (ε : Fin d → 𝕜) (f : Leaf d → E) (i : Leaf d) :
    martingaleTransform T (prependSign a ε)
      (fun k : Fin (d + 2) => leafAverage (𝕜 := 𝕜) (d + 1) k.val (signedLeafLift d f))
        (Sum.inl i) =
      a • T (leafAverage (𝕜 := 𝕜) d 0 f i) +
        martingaleTransform T ε (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val f) i := by
  rw [martingaleTransform, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, leafAverage_signedLeafLift_zero,
    leafAverage_signedLeafLift_inl, sub_zero, prependSign, Fin.cases_zero, Fin.cases_succ]
  rfl

theorem liftedTerminal_transform_inr (d : ℕ) (T : E →L[𝕜] F)
    (a : 𝕜) (ε : Fin d → 𝕜) (f : Leaf d → E) (i : Leaf d) :
    martingaleTransform T (prependSign a ε)
      (fun k : Fin (d + 2) => leafAverage (𝕜 := 𝕜) (d + 1) k.val (signedLeafLift d f))
        (Sum.inr i) =
      -(a • T (leafAverage (𝕜 := 𝕜) d 0 f i) +
        martingaleTransform T ε (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val f) i) := by
  rw [martingaleTransform, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, leafAverage_signedLeafLift_zero,
    leafAverage_signedLeafLift_inr, sub_zero, prependSign, Fin.cases_zero, Fin.cases_succ]
  have hn (x y : E) : -x - -y = -(x - y) := by abel
  simp only [martingaleTransform, hn, map_neg, smul_neg, Finset.sum_neg_distrib, neg_add_rev]
  abel

/-- The terminal-value denominator follows locally from the original UMD
definition, without loss of constant. The additional initial sign is used
twice, with coefficients 1 and -1, and its contributions cancel. -/
theorem UMDBound.finiteDyadicTerminal_two [NormedSpace ℝ E] [CompleteSpace E]
    {T : E →L[𝕜] F} {C : ℝ≥0} (hC : UMDBound.{uΩ} 2 T C) :
    FiniteDyadicTerminalBound 2 T C := by
  apply (finiteDyadicTerminalBound_two_iff T C).mpr
  intro d f ε hε
  let q : Leaf d → F := martingaleTransform T ε
    (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val f)
  let b : Leaf d → F := fun i => T (leafAverage (𝕜 := 𝕜) d 0 f i)
  have hbound (a : 𝕜) (ha : ‖a‖ = 1) :
      leafL2Norm d (a • b + q) ≤ (C : ℝ) * leafL2Norm d f := by
    let : MeasurableSpace (Leaf (d + 1)) := leafMeasurableSpace (d + 1)
    let : IsProbabilityMeasure (leafUniform (d + 1)) := leafUniform_probability (d + 1)
    let P : Fin (d + 2) → Leaf (d + 1) → E :=
      fun k => leafAverage (𝕜 := 𝕜) (d + 1) k.val (signedLeafLift d f)
    have hP : IsLpMartingale P (leafFiltration (d + 1)) 2 (leafUniform (d + 1)) :=
      isLpMartingale_leafAverage (d + 1) 2 _
    have h := hC.test_finiteMeasure (leafUniform (d + 1))
      (by omega) (leafFiltration (d + 1)) P hP
      (prependSign a ε) (prependSign_norm a ha ε hε)
    have hdiff : differenceSum P = signedLeafLift d f := by
      funext i
      rw [differenceSum_eq]
      simp [P]
    have htrans : martingaleTransform T (prependSign a ε) P = signedLeafLift d (a • b + q) := by
      funext i
      cases i with
      | inl i => exact liftedTerminal_transform_inl d T a ε f i
      | inr i => exact liftedTerminal_transform_inr d T a ε f i
    rw [hdiff, htrans, eLpNorm_signedLeafLift, eLpNorm_signedLeafLift,
      eLpNorm_leafUniform_two, eLpNorm_leafUniform_two,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)] at h
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (NNReal.coe_nonneg C) (Real.sqrt_nonneg _))).mp h
  have hp : leafL2Norm d (b + q) ≤ (C : ℝ) * leafL2Norm d f := by
    simpa using hbound 1 (by simp)
  have hm : leafL2Norm d (-b + q) ≤ (C : ℝ) * leafL2Norm d f := by
    simpa using hbound (-1) (by simp)
  have hsum : (b + q) + (-b + q) = (2 : 𝕜) • q := by
    rw [two_smul]
    abel
  have htri := leafL2Norm_add_le (𝕜 := 𝕜) d (b + q) (-b + q)
  rw [hsum, leafL2Norm_smul] at htri
  norm_num at htri
  change leafL2Norm d q ≤ _
  linarith

end HilbertUMD
