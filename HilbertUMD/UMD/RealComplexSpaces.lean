import HilbertUMD.Foundations.Spaces
import HilbertUMD.UMD.UMDRestriction

/-!
# The real spaces inside their complex versions

Taking real parts is contractive for both summands of the infimum norm.
Consequently complex decompositions cannot shorten the norm of a real vector.
The coordinate inclusion is therefore an isometry for the graph spaces too.
-/

noncomputable section
open scoped ENNReal NNReal
namespace HilbertUMD

namespace RealComplex

def ofReal (n : ℕ) : Vec ℝ n →ₗ[ℝ] Vec ℂ n where
  toFun x i := (x i : ℂ)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp [Complex.real_smul]

@[simp] theorem ofReal_apply (n : ℕ) (x : Vec ℝ n) (i : Leaf n) :
    ofReal n x i = (x i : ℂ) := rfl

theorem norm_ofReal (n : ℕ) (x : Vec ℝ n) : ‖ofReal n x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa using norm_le_pi_norm x i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa using norm_le_pi_norm (ofReal n x) i

theorem blockSum_ofReal (n : ℕ) (x : Vec ℝ n) (i : Node n) :
    blockSum n (ofReal n x) i = (blockSum (𝕜 := ℝ) n x i : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with u | (i | i)
    · simp [blockSum, total, ofReal, Complex.ofReal_sum]
    · exact ih (left x) i
    · exact ih (right x) i

theorem blockSum_re (n : ℕ) (x : Vec ℂ n) (i : Node n) :
    blockSum n (fun j => (x j).re) i = (blockSum n x i).re := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with u | (i | i)
    · simp [blockSum, total]
    · exact ih (left x) i
    · exact ih (right x) i

theorem l1Norm_ofReal (n : ℕ) (x : Vec ℝ n) :
    l1Norm n (ofReal n x) = l1Norm n x := by
  simp [l1Norm_eq]

theorem l1Norm_re_le (n : ℕ) (x : Vec ℂ n) :
    l1Norm n (fun j => (x j).re) ≤ l1Norm n x := by
  exact Finset.sum_le_sum fun i _ => Complex.abs_re_le_norm (x i)

theorem hilbertNorm_ofReal (n : ℕ) (x : Vec ℝ n) :
    hilbertNorm n (ofReal n x) = hilbertNorm n x := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  simp [hilbertNorm_sq, blockSum_ofReal]

theorem hilbertNorm_re_le (n : ℕ) (x : Vec ℂ n) :
    hilbertNorm n (fun j => (x j).re) ≤ hilbertNorm n x := by
  apply (sq_le_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  simp only [hilbertNorm_sq, blockSum_re]
  exact Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (Complex.abs_re_le_norm _) 2

theorem sumNorm_le_split {𝕜 : Type*} [RCLike 𝕜] (n : ℕ) (x u : Vec 𝕜 n) :
    sumNorm n x ≤ l1Norm n u + hilbertNorm n (x - u) := by
  rw [sumNorm_eq_inf]
  exact ciInf_le ⟨0, by rintro _ ⟨v, rfl⟩; positivity⟩ u

theorem sumNorm_re_le (n : ℕ) (x : Vec ℂ n) :
    sumNorm n (fun j => (x j).re) ≤ sumNorm n x := by
  rw [sumNorm_eq_inf]
  apply le_ciInf
  intro u
  have h := sumNorm_le_split n (fun j => (x j).re) (fun j => (u j).re)
  have hh := hilbertNorm_re_le n (x - u)
  simp only [Pi.sub_apply, Complex.sub_re] at hh
  exact h.trans (add_le_add (l1Norm_re_le n u) hh)

theorem sumNorm_ofReal (n : ℕ) (x : Vec ℝ n) :
    sumNorm n (ofReal n x) = sumNorm n x := by
  apply le_antisymm
  · rw [sumNorm_eq_inf n x]
    apply le_ciInf
    intro u
    have h := sumNorm_le_split n (ofReal n x) (ofReal n u)
    rw [← map_sub, l1Norm_ofReal, hilbertNorm_ofReal] at h
    exact h
  · simpa using sumNorm_re_le n (ofReal n x)

theorem summation_ofReal (n : ℕ) (x : Vec ℝ n) :
    summation n (ofReal n x) = ofReal n (summation n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    rcases i with i | i
    · exact congrFun (ih (left x)) i
    · change total (ofReal n (left x)) + summation n (ofReal n (right x)) i =
        ((total (left x) + summation n (right x) i : ℝ) : ℂ)
      rw [ih]
      simp [ofReal, total, Complex.ofReal_sum]

/-- A real matrix and its complex extension have isometric graph inclusions. -/
def graphIsometry {n : ℕ} (T : Vec ℝ n →ₗ[ℝ] Vec ℝ n)
    (S : Vec ℂ n →ₗ[ℂ] Vec ℂ n)
    (hST : ∀ x, S (ofReal n x) = ofReal n (T x))
    [NormedSpace ℝ (GraphSpace S)] [IsScalarTower ℝ ℂ (GraphSpace S)] :
    GraphSpace T →ₗᵢ[ℝ] GraphSpace S where
  toFun := ofReal n
  map_add' x y := (ofReal n).map_add x y
  map_smul' c x := by
    change Vec ℝ n at x
    change ofReal n (c • (show Vec ℝ n from x)) =
      c • (show GraphSpace S from ofReal n x)
    rw [← IsScalarTower.algebraMap_smul ℂ c (show GraphSpace S from ofReal n x)]
    change ofReal n (c • (show Vec ℝ n from x)) =
      (c : ℂ) • ofReal n (show Vec ℝ n from x)
    ext i
    change ((c * x i : ℝ) : ℂ) = (c : ℂ) * (x i : ℂ)
    exact Complex.ofReal_mul c (x i)
  norm_map' x := by
    change Vec ℝ n at x
    change max ‖S (ofReal n x)‖ (sumNorm n (ofReal n x)) = max ‖T x‖ (sumNorm n x)
    rw [hST, norm_ofReal, sumNorm_ofReal]

end RealComplex

universe uΩ

/-- Restriction of the complex graph-space bound to its real part. -/
theorem UMDBound.graph_real_of_complex {n : ℕ}
    (T : Vec ℝ n →ₗ[ℝ] Vec ℝ n) (S : Vec ℂ n →ₗ[ℂ] Vec ℂ n)
    (hST : ∀ x, S (RealComplex.ofReal n x) = RealComplex.ofReal n (T x))
    [NormedSpace ℝ (GraphSpace S)] [IsScalarTower ℝ ℂ (GraphSpace S)]
    {C : ℝ≥0} (hC : UMDBound.{uΩ} 2 (ContinuousLinearMap.id ℂ (GraphSpace S)) C) :
    UMDBound.{uΩ} 2 (ContinuousLinearMap.id ℝ (GraphSpace T)) C := by
  exact hC.restrictScalars_real.of_isometric_intertwining
    (RealComplex.graphIsometry T S hST) (RealComplex.graphIsometry T S hST)
    (fun _ => rfl) (by norm_num)

theorem umdConstant_xSpace_real_le_complex (n : ℕ)
    [NormedSpace ℝ (XSpace ℂ n)] [IsScalarTower ℝ ℂ (XSpace ℂ n)] :
    umdConstant.{uΩ} 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) ≤
      umdConstant.{uΩ} 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) := by
  apply le_umdConstant
  intro C hC
  exact umdConstant_le (hC.graph_real_of_complex (summationLinear n) (summationLinear n)
    (RealComplex.summation_ofReal n))

end HilbertUMD
