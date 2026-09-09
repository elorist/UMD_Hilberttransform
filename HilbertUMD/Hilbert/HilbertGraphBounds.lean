import HilbertUMD.Hilbert.HilbertOperatorSpaces
import HilbertUMD.Hilbert.HilbertPVBounds

/-!
# Linear Hilbert bounds for graph spaces

The principal-value/Fourier bridges give the Hilbert-space L2 bound;
the graph-space factorization then gives the linear comparison.
-/

noncomputable section
open scoped ENNReal

namespace HilbertUMD

theorem hilbertConstant_two_real_graph_le {n : ℕ} {T : Vec ℝ n →ₗ[ℝ] Vec ℝ n}
    (hT : TransferAssumptions T) :
    hilbertConstant 2 (ContinuousLinearMap.id ℝ (GraphSpace T)) ≤ (n : ℝ≥0∞) + 1 :=
  hilbertConstant_two_graph_le_of_hilbert hT (hilbertBound_two_real_hilbert (HSpace ℝ n))

theorem hilbertConstant_two_complex_graph_le {n : ℕ} {T : Vec ℂ n →ₗ[ℂ] Vec ℂ n}
    (hT : TransferAssumptions T) :
    hilbertConstant 2 (ContinuousLinearMap.id ℂ (GraphSpace T)) ≤ (n : ℝ≥0∞) + 1 :=
  hilbertConstant_two_graph_le_of_hilbert hT (hilbertBound_two_complex_hilbert (HSpace ℂ n))

/-- Uses the PV/Fourier bridge: the desired linear upper bound for X_n. -/
theorem xSpace_hilbert_linear_upper_real (n : ℕ) :
    hilbertConstant 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) ≤ (n : ℝ≥0∞) + 1 :=
  hilbertConstant_two_real_graph_le (summation_transferAssumptions n)

/-- Uses the PV/Fourier bridge: the desired linear upper bound for X_n. -/
theorem xSpace_hilbert_linear_upper_complex (n : ℕ) :
    hilbertConstant 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) ≤ (n : ℝ≥0∞) + 1 :=
  hilbertConstant_two_complex_graph_le (summation_transferAssumptions n)

end HilbertUMD
