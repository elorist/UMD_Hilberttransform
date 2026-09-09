import HilbertUMD.Hilbert.HilbertInterval
import HilbertUMD.Hilbert.HilbertL2Extension

/-!
# Proved interval formula and derived finite-dimensional `L²` extension

Reference: Hytönen, van Neerven, Veraar and Weis, *Analysis in Banach Spaces,
Volume I: Martingales and Littlewood-Paley Theory*, Springer, 2016.
Example 5.1.2, p. 375 gives the interval logarithm formula (away from its
endpoints), now proved directly in `HilbertUMD.Hilbert.HilbertInterval`. The extension
below combines Lemma 1.2.31 and Proposition 1.2.32,
p. 29 (density and mollification), with scalar Theorem 5.1.1, p. 374 (`L²`
and a.e. truncation convergence). Componentwise smooth approximation in finite
dimensions preserves the same operator constant. The extension is now proved
in `HilbertL2Extension` from the existing scalar L(3/2) PV realization, using
localization, finite-coordinate reconstruction, and smooth density.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace HilbertUMD.Interfaces

/-- Compatibility name for the proved formula of HNVW I, Example 5.1.2,
p. 375, in either scalar field. Endpoints form a null set. -/
theorem interval_hilbert_pv (𝕜 : Type*) [RCLike 𝕜] (a b : ℝ) (hab : a < b) :
    IsHilbertPVAe ((Set.Ico a b).indicator (fun _ : ℝ => (1 : 𝕜)))
      (fun t => ((Real.log |(t - a) / (t - b)| / Real.pi : ℝ) : 𝕜)) := by
  exact HilbertUMD.interval_hilbert_pv 𝕜 a b hab

/-- Componentwise scalar `L²` extension, with the exact smooth-test bound.
The proof depends only on the existing scalar L(3/2) PV realization. -/
theorem HilbertBound.l2_pv_extension {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {T : E →L[𝕜] F} {C : ℝ≥0} (hC : HilbertBound 2 T C)
    (f : ℝ → E) (hf : MemLp f 2 volume) :
    ∃ g : ℝ → F, IsHilbertPVAe (fun x => T (f x)) g ∧ MemLp g 2 volume ∧
      eLpNorm g 2 volume ≤ (C : ℝ≥0∞) * eLpNorm f 2 volume := by
  let : FiniteDimensional ℝ F := FiniteDimensional.trans ℝ 𝕜 F
  exact HilbertL2Extension.extension F hC f hf

end HilbertUMD.Interfaces
