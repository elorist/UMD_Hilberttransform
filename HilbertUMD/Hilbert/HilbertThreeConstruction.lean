import HilbertUMD.Hilbert.HilbertTwoPV
import HilbertUMD.Hilbert.HilbertThreeDual
import HilbertUMD.Hilbert.HilbertThreePV
import HilbertUMD.Interfaces.HilbertThreeHalves

/-! The scalar L3 PV realization follows from the existing L(3/2)
realization and L2 PV extension. The conjugate norm bound and the passage
from compact cutoffs to the actual PV limit are checked independently.
This module does not use the Cotlar identity or the later skew-duality wrapper. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace HilbertUMD

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

/-- Construct the L3 realization from the L(3/2) realization and L2 PV
extension, retaining the explicit bound 6. -/
theorem exists_real_hilbert_three_of_three_halves :
    ∃ R : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 (volume : Measure ℝ),
      ‖R‖₊ ≤ 6 ∧ ∀ (f : ℝ → ℝ) (hf : MemLp f 3 volume),
        IsHilbertPVAe f (R (hf.toLp f)) := by
  obtain ⟨T, hT, hTPV⟩ := Interfaces.exists_real_hilbert_three_halves
  have hTnorm : ‖T‖ ≤ (6 : ℝ) := by exact_mod_cast hT
  let U := realHilbertL2.toContinuousLinearMap
  have hskew (f g : RealL2) :
      (∫ x, U f x * g x) = -(∫ x, f x * U g x) := by
    simpa [U, L2.inner_def, RCLike.inner_apply, mul_comm] using realHilbertL2_skew f g
  have hagree (g : ℝ → ℝ) (h2 : MemLp g 2 volume) (hq : MemLp g (3/2) volume) :
      U (h2.toLp g) =ᵐ[volume] T (hq.toLp g) :=
    (realHilbertL2_pv_all g h2).unique (hTPV g hq)
  obtain ⟨R, hR, hAgree⟩ := HilbertThreeDual.exists_three_of_two_threeHalves
    volume U T hTnorm hskew hagree
  refine ⟨R, by exact_mod_cast hR, ?_⟩
  intro f hf
  exact HilbertThreePV.isHilbertPVAe_of_L2_agreement U R realHilbertL2_pv_all
    (fun g h2 h3 => (hAgree g h2 h3).symm) f hf

end HilbertUMD
