import HilbertUMD.Hilbert.HilbertConstant
import HilbertUMD.Analysis.MixedNorm
import HilbertUMD.Hilbert.HilbertThreeConstruction
import HilbertUMD.Hilbert.CotlarExtension
import HilbertUMD.Analysis.GaussianAmplification

/-!
Real-line scalar analysis used by `Cotlar.lean`.

1. C. Carton-Lebrun, *Product properties of Hilbert transforms*, Journal of
Approximation Theory 21 (1977), 356–360, DOI 10.1016/0021-9045(77)90006-5.
The publisher abstract states the polarized identity on R for Lp and Lq
with 1/p+1/q ≤ 1. We specialize to p=q=3. The full publisher text was not
accessible in this audit; no unverified theorem number is assigned.
The normalization and real-line identity are independently checked in
L. Grafakos, *Classical Fourier Analysis*, 3rd ed. (2014), (5.1.23),
pp. 320–321. That displayed identity is initially for real Schwartz
functions, whereas Carton-Lebrun supplies the stated Lp/Lq scope.
Grafakos Theorem 5.1.12, p. 323, identifies the Lp realization with the a.e.
principal-value limit. Thus the imported claim uses exactly our normalized
one-cutoff `IsHilbertPVAe`, not the periodic transform. The identity is now
proved locally: `CotlarFourier.lean` proves the Fourier identity on Schwartz
functions, and `CotlarExtension.lean` extends it by Holder continuity and
Schwartz density, using the proved L(3/2) realization and L2 PV extension.

2. The scalar L3 realization with bound 6 is derived locally in
`HilbertThreeConstruction.lean` from the existing L(3/2) realization and
L2 PV extension. It is no longer a separate imported statement. The checked
proof uses skew pairing, power tests, dense extension, and PV localization.

3. Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach Spaces*, Volume I
(2016), Theorem 2.1.9: the Hilbert-space extension of a scalar Lp→Lp
operator has the same norm. The finite real Hilbert-space case at p=3 is
proved locally in `GaussianAmplification.lean` by Gaussian averaging and
Tonelli. No Cotlar family estimate or manuscript matrix bound is imported.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace HilbertUMD.Interfaces

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

/-- The nonperiodic polarized product identity, p=q=3, proved from the
Fourier identity and the existing L2 and L(3/2) PV realizations. -/
theorem cotlar_real_pv {u v Hu Hv : ℝ → ℝ}
    (hu : MemLp u 3 volume) (hv : MemLp v 3 volume)
    (hHu : IsHilbertPVAe u Hu) (hHv : IsHilbertPVAe v Hv) :
    IsHilbertPVAe (fun t => u t * Hv t + v t * Hu t)
      (fun t => Hu t * Hv t - u t * v t) := by
  obtain ⟨R, _, hR⟩ := HilbertUMD.exists_real_hilbert_three_of_three_halves
  obtain ⟨T, _, hT⟩ := exists_real_hilbert_three_halves
  exact CotlarExtension.cotlar_of_realizations R T hR hT realHilbertL2_pv_all
    hu hv hHu hHv

/-- Derived from the existing L(3/2) realization and L2 PV extension,
with the original explicit bound 6 and PV identification on every L3 input. -/
theorem exists_real_hilbert_three :
    ∃ R : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 (volume : Measure ℝ),
      ‖R‖₊ ≤ 6 ∧ ∀ (f : ℝ → ℝ) (hf : MemLp f 3 volume),
        IsHilbertPVAe f (R (hf.toLp f)) :=
  HilbertUMD.exists_real_hilbert_three_of_three_halves

/-- HNVW I, Theorem 2.1.9, for finite real Hilbert targets at p=3,
proved by Gaussian averaging. The same operator acts on each coordinate. -/
theorem scalar_operator_hilbert_extension_three {ι : Type*} [Fintype ι]
    (R : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 (volume : Measure ℝ))
    (f : ℝ → ι → ℝ) (hf : ∀ i, MemLp (fun t => f t i) 3 volume) :
    mixedNorm 3 2 volume (fun t i => R ((hf i).toLp (fun s => f s i)) t) ≤
      (‖R‖₊ : ℝ≥0∞) * mixedNorm 3 2 volume f := by
  have h := scalar_operator_hilbert_extension_three_lp R
    (fun i => (hf i).toLp (fun t => f t i))
  have heq : mixedNorm 3 2 volume (fun t i => (hf i).toLp (fun s => f s i) t) =
      mixedNorm 3 2 volume f := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_all_iff.2 (fun i => (hf i).coeFn_toLp)] with t ht
    congr 1
    exact funext ht
  simpa only [heq] using h

end HilbertUMD.Interfaces
