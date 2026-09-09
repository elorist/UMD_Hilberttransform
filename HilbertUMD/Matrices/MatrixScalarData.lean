import HilbertUMD.Matrices.MatrixBlocksLp
import HilbertUMD.Matrices.MatrixEnergyAnalysis
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Scalar analytic inputs for the common matrix argument. These are explicit
operator hypotheses, not assumed matrix estimates. The applications provide
them from the separately proved scalar product lemmas. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace HilbertUMD

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

def scalarProductLp (R : Lp ℝ 3 μ →L[ℝ] Lp ℝ 3 μ) (η : ℝ)
    (u v : Lp ℝ 3 μ) : Lp ℝ (3/2) μ :=
  ((Lp.memLp (R v)).mul (Lp.memLp u) |>.add
    (((Lp.memLp (R u)).mul (Lp.memLp v)).const_mul η)).toLp
      (fun s => u s * R v s + η * (v s * R u s))

theorem scalarProductLp_coeFn (R : Lp ℝ 3 μ →L[ℝ] Lp ℝ 3 μ) (η : ℝ)
    (u v : Lp ℝ 3 μ) :
    scalarProductLp μ R η u v =ᵐ[μ] (fun s => u s * R v s + η * (v s * R u s)) :=
  MemLp.coeFn_toLp _

/-- The precise scalar product/duality assumptions needed for energy growth.
The constants M and P precede and are independent of the finite family size. -/
structure ScalarMatrixData (η M P : ℝ) where
  atThree : Lp ℝ 3 μ →L[ℝ] Lp ℝ 3 μ
  atThreeHalves : Lp ℝ (3/2) μ →L[ℝ] Lp ℝ (3/2) μ
  dual : ∀ (b : Lp ℝ 3 μ) (w : Lp ℝ (3/2) μ),
    (∫ s, atThree b s * w s ∂μ) = -η * (∫ s, b s * atThreeHalves w s ∂μ)
  hilbertBound : ∀ (ι : Type) [Fintype ι] (u : ι → Lp ℝ 3 μ),
    mixedNorm 3 2 μ (fun s i => atThree (u i) s) ≤
      ENNReal.ofReal M * mixedNorm 3 2 μ (fun s i => u i s)
  productBound : ∀ (ι : Type) [Fintype ι] (u v : ι → Lp ℝ 3 μ),
    mixedNorm (3/2) 1 μ (fun s i => atThreeHalves (scalarProductLp μ atThree η (u i) (v i)) s) ≤
      ENNReal.ofReal P * mixedNorm 3 2 μ (fun s i => u i s) * mixedNorm 3 2 μ (fun s i => v i s)

variable {μ}

theorem ScalarMatrixData.family_dual {η M P : ℝ} (R : ScalarMatrixData μ η M P)
    {ι : Type} [Fintype ι] (b : ι → Lp ℝ 3 μ) (w : ι → Lp ℝ (3/2) μ) :
    (∫ s, ∑ i, R.atThree (b i) s * w i s ∂μ) =
      -η * (∫ s, ∑ i, b i s * R.atThreeHalves (w i) s ∂μ) := by
  rw [integral_finsetSum, integral_finsetSum]
  · simp_rw [R.dual]
    exact (Finset.mul_sum _ _ _).symm
  · intro i _
    exact (Lp.memLp (b i)).integrable_mul (Lp.memLp (R.atThreeHalves (w i)))
  · intro i _
    exact (Lp.memLp (R.atThree (b i))).integrable_mul (Lp.memLp (w i))

theorem ScalarMatrixData.family_dual_abs {η M P : ℝ} (R : ScalarMatrixData μ η M P)
    (hη : η^2 = 1) {ι : Type} [Fintype ι] (b : ι → Lp ℝ 3 μ) (w : ι → Lp ℝ (3/2) μ) :
    |∫ s, ∑ i, R.atThree (b i) s * w i s ∂μ| =
      |∫ s, ∑ i, b i s * R.atThreeHalves (w i) s ∂μ| := by
  rw [R.family_dual b w, abs_mul, abs_neg]
  have he : |η| = 1 := by rcases sq_eq_one_iff.mp hη with h | h <;> rw [h] <;> norm_num
  rw [he, one_mul]

end HilbertUMD
