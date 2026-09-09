import HilbertUMD.UMD.DyadicLpOperators
import HilbertUMD.Matrices.MatrixScalarData

/-! The actual finite dyadic operators supply the scalar analytic input for
the common matrix energy argument, using the checked martingale product
estimate and its finite dyadic operator realizations. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace HilbertUMD

theorem scalarProductLp_dyadic_coe (n : ℕ) (ε : Fin n → ℝ)
    (u v : Lp ℝ 3 (leafUniform n)) :
    (scalarProductLp (leafUniform n) (dyadicLpScalar n 3 ε) (-1) u v : Leaf n → ℝ) =
      fun x => u x * dyadicScalar n ε (v : Leaf n → ℝ) x -
        v x * dyadicScalar n ε (u : Leaf n → ℝ) x := by
  rw [eq_of_leaf_aeEq n (scalarProductLp_coeFn _ _ _ _ _)]
  simp only [dyadicLpScalar_coe, neg_one_mul, sub_eq_add_neg]

/-- Actual dyadic scalar data with the checked product constant 1097.
The negative sign selects uUv-vUu and self-adjointness. -/
theorem dyadic_scalarMatrixData (n : ℕ) (ε : Fin n → ℝ) (hε : ∀ k, |ε k| ≤ 1) :
    ∃ R : ScalarMatrixData (leafUniform n) (-1) 2 1097,
      R.atThree = dyadicLpScalar n 3 ε ∧
      R.atThreeHalves = dyadicLpScalar n (3/2) ε := by
  refine ⟨{
    atThree := dyadicLpScalar n 3 ε
    atThreeHalves := dyadicLpScalar n (3/2) ε
    dual := ?_
    hilbertBound := ?_
    productBound := ?_ }, rfl, rfl⟩
  · intro b w
    simpa using dyadicLpScalar_integral_pairing_exponents n ε 3 (3/2) b w
  · intro ι _ u
    simpa only [dyadicLpScalar_coe, ENNReal.ofReal_ofNat] using
      Interfaces.dyadic_hilbert_transform_three n ε hε (fun x i => u i x)
  · intro ι _ u v
    have h := martingale_product_bound n ε hε (fun x i => u i x) (fun x i => v i x)
    change mixedNorm (3/2) 1 (leafUniform n)
      (fun s i => dyadicScalar n ε (fun x => u i x * dyadicScalar n ε (v i) x -
        v i x * dyadicScalar n ε (u i) x) s) ≤ _ at h
    simpa only [dyadicLpScalar_coe, scalarProductLp_dyadic_coe,
      ENNReal.ofReal_ofNat] using h

/-- The same data packaged with a universal coefficient chosen before depth. -/
theorem exists_dyadic_scalarMatrixData :
    ∃ P : ℝ≥0, ∀ (n : ℕ) (ε : Fin n → ℝ), (∀ k, |ε k| ≤ 1) →
      ∃ R : ScalarMatrixData (leafUniform n) (-1) 2 P,
        R.atThree = dyadicLpScalar n 3 ε ∧
          R.atThreeHalves = dyadicLpScalar n (3/2) ε := by
  refine ⟨1097, ?_⟩
  intro n ε hε
  exact dyadic_scalarMatrixData n ε hε

end HilbertUMD
