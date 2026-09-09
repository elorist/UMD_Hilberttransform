import HilbertUMD.Interfaces.HilbertPV

/-!
# Principal-value bounds from the constructed `L²` isometries

The principal-value/Fourier identifications in `Interfaces.HilbertPV` are proved
using the symmetric frequency cutoff argument in `HilbertPVFourier`.
All bounds in this module are free of admitted dependencies.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace HilbertUMD

theorem hilbertBound_two_real_scalar :
    HilbertBound 2 (ContinuousLinearMap.id ℝ ℝ) 1 := by
  apply hilbertBound_two_of_isometry _ realHilbertL2
  intro f hf hc
  exact Interfaces.real_scalar_pv_fourier f hf hc

theorem hilbertBound_two_complex_hilbert (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F] :
    HilbertBound 2 (ContinuousLinearMap.id ℂ F) 1 := by
  apply hilbertBound_two_of_isometry _ (HilbertValued.hilbertL2 F)
  intro f hf hc
  exact Interfaces.finite_complex_hilbert_pv_fourier F f hf hc

theorem hilbertBound_two_real_hilbert_basis {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : OrthonormalBasis ι ℝ F) :
    HilbertBound 2 (ContinuousLinearMap.id ℝ F) 1 := by
  apply hilbertBound_two_of_isometry _ (FiniteRealHilbert.hilbertL2 b)
  intro f hf hc
  exact Interfaces.finite_real_hilbert_pv_fourier b f hf hc

theorem hilbertBound_two_real_hilbert (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F] :
    HilbertBound 2 (ContinuousLinearMap.id ℝ F) 1 :=
  hilbertBound_two_real_hilbert_basis (stdOrthonormalBasis ℝ F)

end HilbertUMD
