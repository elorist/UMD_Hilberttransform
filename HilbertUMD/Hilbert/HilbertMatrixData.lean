import HilbertUMD.Matrices.MatrixScalarData
import HilbertUMD.Hilbert.HilbertLpCompatibility

/-!
The real-line Hilbert scalar data for the manuscript's common dyadic matrix
energy argument. The selected operators are the actual compatible L3 and
L(3/2) PV realizations. Scalar duality, Hilbert amplification, and Cotlar's
identity supply the data; no matrix estimate is assumed here.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD

/-- The scalar Hilbert input to the common matrix proof, with explicit
universal constants M=6 and P=37, obtained from the scalar analytic proofs. -/
def hilbertMatrixData : ScalarMatrixData (volume : Measure ℝ) 1 6 37 where
  atThree := realHilbertThree
  atThreeHalves := realHilbertThreeHalves
  dual b w := by
    simpa using realHilbertThree_threeHalves_duality b w
  hilbertBound ι _ u := by
    have hu : ∀ i, IsHilbertPVAe (fun t => u i t) (fun t => realHilbertThree (u i) t) := by
      intro i
      have hi := realHilbertThree_pv (u i) (Lp.memLp (u i))
      simpa only [Lp.toLp_coeFn] using hi
    simpa using hilbertPVAe_mixedNorm_three_le_six (fun t i => u i t)
      (fun t i => realHilbertThree (u i) t) (fun i => Lp.memLp (u i)) hu
  productBound ι _ u v := by
    have hu : ∀ i, IsHilbertPVAe (fun t => u i t) (fun t => realHilbertThree (u i) t) := by
      intro i
      simpa only [Lp.toLp_coeFn] using realHilbertThree_pv (u i) (Lp.memLp (u i))
    have hv : ∀ i, IsHilbertPVAe (fun t => v i t) (fun t => realHilbertThree (v i) t) := by
      intro i
      simpa only [Lp.toLp_coeFn] using realHilbertThree_pv (v i) (Lp.memLp (v i))
    have hw : ∀ i, IsHilbertPVAe
        (fun t => u i t * realHilbertThree (v i) t + v i t * realHilbertThree (u i) t)
        (fun t => realHilbertThreeHalves (scalarProductLp volume realHilbertThree 1 (u i) (v i)) t) := by
      intro i
      let w := scalarProductLp volume realHilbertThree 1 (u i) (v i)
      have hpv := realHilbertThreeHalves_pv w (Lp.memLp w)
      rw [Lp.toLp_coeFn] at hpv
      apply hpv.congr_input
      simpa only [one_mul] using scalarProductLp_coeFn volume realHilbertThree 1 (u i) (v i)
    simpa using hilbert_product_mixedNorm_le
      (fun t i => u i t) (fun t i => v i t)
      (fun t i => realHilbertThree (u i) t) (fun t i => realHilbertThree (v i) t)
      (fun t i => realHilbertThreeHalves (scalarProductLp volume realHilbertThree 1 (u i) (v i)) t)
      (fun i => Lp.memLp (u i)) (fun i => Lp.memLp (v i)) hu hv hw

@[simp] theorem hilbertMatrixData_atThree : hilbertMatrixData.atThree = realHilbertThree := rfl
@[simp] theorem hilbertMatrixData_atThreeHalves :
    hilbertMatrixData.atThreeHalves = realHilbertThreeHalves := rfl

end HilbertUMD
