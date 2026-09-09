import HilbertUMD.Matrices.MatrixCompatible
import HilbertUMD.Analysis.CubicComplex
import HilbertUMD.UMD.DyadicLpOperators

/-! Identifying the actual matrix complexification on finite dyadic inputs. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD

theorem treeMatrix_ofReal (η : ℝ) (c : ℕ → ℝ) (n : ℕ) (x : Vec ℝ n) :
    treeMatrix (η : ℂ) (fun k => (c k : ℂ)) n (fun j => (x j : ℂ)) =
      (fun j => (treeMatrix η c n x j : ℂ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext i
    cases i with
    | inl i =>
      simp [treeMatrix, left, right, total, Complex.ofReal_sum]
      exact congrArg (fun z : Vec ℂ n => z i) (ih (left x))
    | inr i =>
      simp [treeMatrix, left, right, total, Complex.ofReal_sum]
      exact congrArg (fun z : Vec ℂ n => z i) (ih (right x))

theorem treeMatrix_complex_input (η : ℝ) (c : ℕ → ℝ) (n : ℕ) (x : Vec ℂ n) :
    treeMatrix (η : ℂ) (fun k => (c k : ℂ)) n x =
      (fun j => (treeMatrix η c n (fun k => (x k).re) j : ℂ)) +
        Complex.I • (fun j => (treeMatrix η c n (fun k => (x k).im) j : ℂ)) := by
  have hx : x = (fun j => ((x j).re : ℂ)) + Complex.I • (fun j => ((x j).im : ℂ)) := by
    ext j
    simp [Complex.re_add_im, mul_comm Complex.I]
  calc
    _ = treeMatrix (η : ℂ) (fun k => (c k : ℂ)) n
        ((fun j => ((x j).re : ℂ)) + Complex.I • (fun j => ((x j).im : ℂ))) := congrArg _ hx
    _ = _ := by
      rw [treeMatrix_add, treeMatrix_smul, treeMatrix_ofReal, treeMatrix_ofReal]

theorem treeMatrix_re (η : ℝ) (c : ℕ → ℝ) (n : ℕ) (x : Vec ℂ n) (i : Leaf n) :
    (treeMatrix (η : ℂ) (fun k => (c k : ℂ)) n x i).re =
      treeMatrix η c n (fun j => (x j).re) i := by
  rw [treeMatrix_complex_input]
  simp

theorem treeMatrix_im (η : ℝ) (c : ℕ → ℝ) (n : ℕ) (x : Vec ℂ n) (i : Leaf n) :
    (treeMatrix (η : ℂ) (fun k => (c k : ℂ)) n x i).im =
      treeMatrix η c n (fun j => (x j).im) i := by
  rw [treeMatrix_complex_input]
  simp

theorem dyadic_matrix_action_coe (η : ℝ) (c : ℕ → ℝ) (n d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : Fin d → ℝ)
    (f : CubicLp.Space (ι := Leaf n) (leafUniform d) p) :
    (MatrixCompatible.action (leafUniform d) η c n p (dyadicLpScalar d p ε) f : Leaf d → Vec ℝ n) =
      (fun x => treeMatrix η c n (coordinateAction (dyadicScalar d ε) (f : Leaf d → Vec ℝ n) x)) := by
  have ht := eq_of_leaf_aeEq d ((MatrixCompatible.treeCLM η c n).coeFn_compLpL
    (ScalarLp.amplification (leafUniform d) p (dyadicLpScalar d p ε) f))
  change (MatrixCompatible.action (leafUniform d) η c n p (dyadicLpScalar d p ε) f : Leaf d → Vec ℝ n) =
    (fun x => MatrixCompatible.treeCLM η c n
      (ScalarLp.amplification (leafUniform d) p (dyadicLpScalar d p ε) f x)) at ht
  rw [ht, dyadicLpScalar_amplification_coe]
  rfl

/-- Pointwise identification of the actual complex-linear Lp operator with
the concrete complex dyadic transform followed by the real-coefficient matrix. -/
theorem dyadic_matrix_complexify_coe (η : ℝ) (c : ℕ → ℝ) (n d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : Fin d → ℝ)
    (f : CubicLp.ComplexSpace (ι := Leaf n) (leafUniform d) p) :
    (CubicLp.complexify (leafUniform d)
      (MatrixCompatible.action (leafUniform d) η c n p (dyadicLpScalar d p ε)) f : Leaf d → Vec ℂ n) =
      (fun x => treeMatrix (η : ℂ) (fun k => (c k : ℂ)) n
        (coordinateAction (dyadicScalar d (fun k => (ε k : ℂ))) (f : Leaf d → Vec ℂ n) x)) := by
  have hc := eq_of_leaf_aeEq d (CubicLp.coeFn_complexify (leafUniform d)
    (MatrixCompatible.action (leafUniform d) η c n p (dyadicLpScalar d p ε)) f)
  have hr := eq_of_leaf_aeEq d ((CubicLp.reVec (ι := Leaf n)).coeFn_compLpL f)
  have hi := eq_of_leaf_aeEq d ((CubicLp.imVec (ι := Leaf n)).coeFn_compLpL f)
  change (CubicLp.reLp (leafUniform d) p f : Leaf d → Vec ℝ n) =
    (fun x => CubicLp.reVec (f x)) at hr
  change (CubicLp.imLp (leafUniform d) p f : Leaf d → Vec ℝ n) =
    (fun x => CubicLp.imVec (f x)) at hi
  rw [hc, dyadic_matrix_action_coe, dyadic_matrix_action_coe, hr, hi]
  ext x i
  apply Complex.ext
  · simp only [Pi.add_apply, CubicLp.ofRealVec_apply, Pi.smul_apply, smul_eq_mul,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero,
      treeMatrix_re]
    congr 1
    ext j
    exact (dyadicScalar_re d ε (fun y => f y j) x).symm
  · simp only [Pi.add_apply, CubicLp.ofRealVec_apply, Pi.smul_apply, smul_eq_mul,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
      treeMatrix_im]
    congr 1
    ext j
    exact (dyadicScalar_im d ε (fun y => f y j) x).symm

end HilbertUMD
