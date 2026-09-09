import HilbertUMD.UMD.FiniteTreeReduction

/-!
# Proved complex Paley-Walsh reduction at exponent two

SOURCE: Hytönen--van Neerven--Veraar--Weis, Analysis in Banach Spaces,
Volume I (2016), Theorem 4.2.5 (printed p. 282), Corollary 4.2.6
(p. 283), and the explicit operator version in Section 4.6 (p. 359).
Terminal-value equivalence is Lemma 4.2.8 (pp. 283--284).
DOI: https://doi.org/10.1007/978-3-319-48520-1

The reduction is proved locally, including the binary-tree approximation step
for simple terminal functions on finitely generated probability filtrations.
`FiniteFiltrationModel` gives an exact binary-coordinate model of the filtration
and terminal function. `WeightedTreeMeasure` represents its probability law by
branching probabilities and identifies the weighted conditional averages.
`WeightedBinaryEncoding` realizes dyadic branching probabilities by blocks of
independent fair bits. `DyadicProbabilityApproximation` approximates arbitrary
branching probabilities, and `WeightedDyadicBound` passes the same-C estimate
to the limit. `FiniteTreeReduction` transports it back to the original space.
`FiniteFiltrationApproximation` proves simultaneous L2 approximation of the
original conditional expectations by finite sub-filtrations, preserving C.
`DyadicSampled` proves the binary-tree bound for arbitrary increasing selections
of levels, using zero coefficients to suppress auxiliary levels without loss.
`UMDSimpleTerminal` proves the
extension to arbitrary L2 terminal functions by density and continuity of
conditional expectation. `UMDProbabilityReduction` proves terminal centering,
normalization of finite measures, and localization from sigma-finite spaces.
All these steps preserve the original constant and sample-space universe.

The following specialization reduces finite dyadic terminal tests to the
original operator UMD inequality using those checked reductions.
The concrete model is the full binary tree `Leaf d` with uniform mass 2^-d,
the depth filtration, and the coordinate averages `leafAverage`. Its
cardinality, averaging identities, measurability and martingale property
are independently checked in DyadicLower/DyadicMartingale. The reverse
implication at p=2 is proved locally in DyadicTerminal by the source's
independent-sign argument, including its operator adaptation.

This reduction contains no graph norms, matrix estimates, n-dependent
constants, or assertion of Proposition 2.2. The sample-space universe of
UMDBound remains an explicit parameter. `UMD/UniverseIndependence` combines
this reduction with the reverse implication to prove equality of the p=2
constants across sample-space universes.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace HilbertUMD.Interfaces

universe uΩ

/-- The finite-tree proof preserves its constant over either scalar field. -/
theorem umdBound_of_finiteDyadicTerminalBound
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) (C : ℝ≥0) (h : FiniteDyadicTerminalBound 2 T C) :
    UMDBound.{uΩ} 2 T C := by
  exact umdBound_of_probabilityFiniteTerminalBound h.sampled.weighted.probabilityFinite

/-- Proved CF02 complex operator reduction, with all unimodular complex
coefficients. The real scalar structure on the domain is the compatible
restriction of its complex structure. -/
theorem complex_umdBound_of_finiteDyadicTerminalBound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (C : ℝ≥0) (h : FiniteDyadicTerminalBound 2 T C) :
    UMDBound.{uΩ} 2 T C := by
  exact umdBound_of_probabilityFiniteTerminalBound h.sampled.weighted.probabilityFinite

end HilbertUMD.Interfaces
