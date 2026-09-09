import HilbertUMD.Interfaces.HilbertLpAnalysis
import HilbertUMD.Interfaces.HilbertPV
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
Compatible scalar L2, L3 and L(3/2) Hilbert realizations on R.
The Fourier L2 operator and its skew identity were proved in HilbertL2.
Compatibility is proved by testing against compact smooth functions and
using mathlib's fundamental lemma for distributions. The scalar Lp and PV
realizations are proved in this project; scalar duality is deduced
from smooth density and the L2 skew identity in `HilbertLpDuality`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace HilbertUMD

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 3 / 2) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num⟩

def realHilbertThreeHalves : Lp ℝ (3 / 2) (volume : Measure ℝ) →L[ℝ]
    Lp ℝ (3 / 2) (volume : Measure ℝ) :=
  Interfaces.exists_real_hilbert_three_halves.choose

theorem realHilbertThreeHalves_nnnorm_le : ‖realHilbertThreeHalves‖₊ ≤ 6 :=
  Interfaces.exists_real_hilbert_three_halves.choose_spec.1

theorem realHilbertThreeHalves_pv (f : ℝ → ℝ) (hf : MemLp f (3 / 2) volume) :
    IsHilbertPVAe f (realHilbertThreeHalves (hf.toLp f)) :=
  Interfaces.exists_real_hilbert_three_halves.choose_spec.2 f hf

theorem realHilbertL2_integral_skew (f g : RealL2) :
    (∫ t, realHilbertL2 f t * g t) = -(∫ t, f t * realHilbertL2 g t) := by
  simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using realHilbertL2_skew f g

theorem realHilbertThreeHalves_agrees_two_test (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    realHilbertThreeHalves ((hilbertTest_memLp hf hc (3 / 2)).toLp f) =ᵐ[volume]
      realHilbertL2 ((hilbertTest_memLp hf hc 2).toLp f) := by
  obtain ⟨g, hg, hpv, heq⟩ := Interfaces.real_scalar_pv_fourier f hf hc
  have hg' := hg.coeFn_toLp.symm
  rw [heq] at hg'
  exact ((realHilbertThreeHalves_pv f _).unique hpv.ae).trans hg'

/-- Compatibility on all L2∩L3 inputs, proved by testing against Cc∞.
No general Fourier/PV identification on L2 is admitted here. -/
theorem realHilbertThree_agrees_two (f : ℝ → ℝ)
    (h2 : MemLp f 2 volume) (h3 : MemLp f 3 volume) :
    realHilbertThree (h3.toLp f) =ᵐ[volume] realHilbertL2 (h2.toLp f) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num))
    ((Lp.memLp _).locallyIntegrable (by norm_num))
  intro φ hφ hc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hφ2 := hilbertTest_memLp hφ1 hc 2
  have hφh := hilbertTest_memLp hφ1 hc (3 / 2)
  have hdual := Interfaces.real_hilbert_duality h3 hφh
    (realHilbertThree_pv f h3) (realHilbertThreeHalves_pv φ hφh)
  have htest := realHilbertThreeHalves_agrees_two_test φ hφ1 hc
  have hright : (∫ t, f t * realHilbertThreeHalves (hφh.toLp φ) t) =
      ∫ t, h2.toLp f t * realHilbertL2 (hφ2.toLp φ) t := by
    apply integral_congr_ae
    filter_upwards [htest, h2.coeFn_toLp] with t ht hf
    rw [ht, hf]
  rw [hright] at hdual
  have hskew := realHilbertL2_integral_skew (h2.toLp f) (hφ2.toLp φ)
  have heq : (∫ t, realHilbertL2 (h2.toLp f) t * hφ2.toLp φ t) =
      ∫ t, realHilbertL2 (h2.toLp f) t * φ t := by
    apply integral_congr_ae
    filter_upwards [hφ2.coeFn_toLp] with t ht
    rw [ht]
  rw [heq] at hskew
  simpa only [smul_eq_mul, mul_comm] using hdual.trans hskew.symm

theorem realHilbertThree_threeHalves_duality
    (f : Lp ℝ 3 (volume : Measure ℝ)) (g : Lp ℝ (3 / 2) (volume : Measure ℝ)) :
    (∫ t, realHilbertThree f t * g t) = -(∫ t, f t * realHilbertThreeHalves g t) := by
  have hf := realHilbertThree_pv f (Lp.memLp f)
  have hg := realHilbertThreeHalves_pv g (Lp.memLp g)
  rw [Lp.toLp_coeFn] at hf hg
  exact Interfaces.real_hilbert_duality (Lp.memLp f) (Lp.memLp g) hf hg

end HilbertUMD
