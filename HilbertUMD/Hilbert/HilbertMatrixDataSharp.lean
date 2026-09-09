import HilbertUMD.Matrices.MatrixScalarData
import HilbertUMD.Hilbert.HilbertThreeSharp

/-! Hilbert scalar data with M = 11/4 and P = 9, using the improved Cotlar energy estimate. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD

def hilbertMatrixDataSharp : ScalarMatrixData (volume : Measure ℝ) 1 (11 / 4) 9 where
  atThree := realHilbertThree
  atThreeHalves := realHilbertThreeHalves
  dual b w := by simpa using realHilbertThree_threeHalves_duality b w
  hilbertBound ι _ u := by
    have hu : ∀ i, IsHilbertPVAe (fun t => u i t) (fun t => realHilbertThree (u i) t) := by
      intro i
      simpa only [Lp.toLp_coeFn] using realHilbertThree_pv (u i) (Lp.memLp (u i))
    have h := hilbertPVAe_mixedNorm_three_le_eleven_quarters (fun t i => u i t)
      (fun t i => realHilbertThree (u i) t) (fun i => Lp.memLp (u i)) hu
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
      ENNReal.ofReal_ofNat] using h
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
    simpa using hilbert_product_mixedNorm_le_nine
      (fun t i => u i t) (fun t i => v i t)
      (fun t i => realHilbertThree (u i) t) (fun t i => realHilbertThree (v i) t)
      (fun t i => realHilbertThreeHalves (scalarProductLp volume realHilbertThree 1 (u i) (v i)) t)
      (fun i => Lp.memLp (u i)) (fun i => Lp.memLp (v i)) hu hv hw

@[simp] theorem hilbertMatrixDataSharp_atThree : hilbertMatrixDataSharp.atThree = realHilbertThree := rfl

end HilbertUMD
