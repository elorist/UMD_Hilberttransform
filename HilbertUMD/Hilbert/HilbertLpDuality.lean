import HilbertUMD.Hilbert.HilbertConstant
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.Holder

/-!
# Hilbert skew duality by smooth approximation

Extend a skew pairing of bounded operators from compact smooth tests to
conjugate finite exponents. The Hilbert-transform specialization takes the
bounded PV realizations and the smooth-test PV/Fourier identification as
explicit hypotheses; it does not use general L2/Lp compatibility.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace HilbertUMD

/-- A skew pairing of bounded operators extends from compact smooth tests
to all of two conjugate finite Lp spaces. -/
theorem integral_mul_skew_of_smooth_tests {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (R : Lp ℝ p (volume : Measure ℝ) →L[ℝ] Lp ℝ p volume)
    (T : Lp ℝ q (volume : Measure ℝ) →L[ℝ] Lp ℝ q volume)
    (htest : ∀ (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
      (hg : ContDiff ℝ 1 g) (hd : HasCompactSupport g),
      (∫ t, R ((hilbertTest_memLp hf hc p).toLp f) t * g t) =
        -(∫ t, f t * T ((hilbertTest_memLp hg hd q).toLp g) t))
    (f : Lp ℝ p (volume : Measure ℝ)) (g : Lp ℝ q (volume : Measure ℝ)) :
    (∫ t, R f t * g t) = -(∫ t, f t * T g t) := by
  let B := (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume : Measure ℝ) p q
  have hB (u : Lp ℝ p (volume : Measure ℝ)) (v : Lp ℝ q (volume : Measure ℝ)) :
      B u v = ∫ t, u t * v t :=
    ContinuousLinearMap.lpPairing_eq_integral _ u v
  suffices h : B (R f) g = -B f (T g) by simpa only [hB] using h
  have houter := Lp.dense_hasCompactSupport_contDiff (E := ℝ) (F := ℝ)
    (μ := (volume : Measure ℝ)) hp
  have hinner := Lp.dense_hasCompactSupport_contDiff (E := ℝ) (F := ℝ)
    (μ := (volume : Measure ℝ)) hq
  refine congrFun (Continuous.ext_on houter
    ((B.flip g).continuous.comp R.continuous)
    ((B.flip (T g)).continuous.neg) ?_) f
  rintro u ⟨φ, hu, hc, hφ⟩
  refine congrFun (Continuous.ext_on hinner (B (R u)).continuous
    (((B u).continuous.comp T.continuous).neg) ?_) g
  rintro v ⟨ψ, hv, hd, hψ⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hu' : u = (hilbertTest_memLp hφ1 hc p).toLp φ :=
    Lp.ext (hu.trans (hilbertTest_memLp hφ1 hc p).coeFn_toLp.symm)
  have hv' : v = (hilbertTest_memLp hψ1 hd q).toLp ψ :=
    Lp.ext (hv.trans (hilbertTest_memLp hψ1 hd q).coeFn_toLp.symm)
  change B (R u) v = -B u (T v)
  rw [hB, hB]
  calc
    (∫ t, R u t * v t) = ∫ t, R ((hilbertTest_memLp hφ1 hc p).toLp φ) t * ψ t := by
      rw [hu']
      apply integral_congr_ae
      filter_upwards [hv] with t ht
      rw [ht]
    _ = -(∫ t, φ t * T ((hilbertTest_memLp hψ1 hd q).toLp ψ) t) :=
      htest φ ψ hφ1 hc hψ1 hd
    _ = -(∫ t, u t * T v t) := by
      rw [hv']
      congr 1
      apply integral_congr_ae
      filter_upwards [hu] with t ht
      rw [ht]

/-- Bounded PV realizations are skew duals if their smooth tests agree with
the Fourier L2 transform. All analytic existence inputs are explicit. -/
theorem real_hilbert_duality_of_realizations {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (R : Lp ℝ p (volume : Measure ℝ) →L[ℝ] Lp ℝ p volume)
    (T : Lp ℝ q (volume : Measure ℝ) →L[ℝ] Lp ℝ q volume)
    (hR : ∀ (f : ℝ → ℝ) (hf : MemLp f p volume), IsHilbertPVAe f (R (hf.toLp f)))
    (hT : ∀ (g : ℝ → ℝ) (hg : MemLp g q volume), IsHilbertPVAe g (T (hg.toLp g)))
    (hL2 : ∀ (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f),
      IsHilbertPVAe f (realHilbertL2 ((hilbertTest_memLp hf hc 2).toLp f)))
    {f g Hf Hg : ℝ → ℝ} (hf : MemLp f p volume) (hg : MemLp g q volume)
    (hpf : IsHilbertPVAe f Hf) (hpg : IsHilbertPVAe g Hg) :
    (∫ t, Hf t * g t) = -(∫ t, f t * Hg t) := by
  have htest (φ ψ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
      (hψ : ContDiff ℝ 1 ψ) (hd : HasCompactSupport ψ) :
      (∫ t, R ((hilbertTest_memLp hφ hc p).toLp φ) t * ψ t) =
        -(∫ t, φ t * T ((hilbertTest_memLp hψ hd q).toLp ψ) t) := by
    have hφR := (hR φ (hilbertTest_memLp hφ hc p)).unique (hL2 φ hφ hc)
    have hψT := (hT ψ (hilbertTest_memLp hψ hd q)).unique (hL2 ψ hψ hd)
    have hskew := realHilbertL2_skew
      ((hilbertTest_memLp hφ hc 2).toLp φ) ((hilbertTest_memLp hψ hd 2).toLp ψ)
    simp only [L2.inner_def, RCLike.inner_apply, conj_trivial] at hskew
    calc
      _ = ∫ t, (hilbertTest_memLp hψ hd 2).toLp ψ t *
          realHilbertL2 ((hilbertTest_memLp hφ hc 2).toLp φ) t := by
        apply integral_congr_ae
        filter_upwards [hφR, (hilbertTest_memLp hψ hd 2).coeFn_toLp] with t ht hψt
        rw [ht, hψt, mul_comm]
      _ = -(∫ t, realHilbertL2 ((hilbertTest_memLp hψ hd 2).toLp ψ) t *
          (hilbertTest_memLp hφ hc 2).toLp φ t) := hskew
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hψT, (hilbertTest_memLp hφ hc 2).coeFn_toLp] with t ht hφt
        rw [ht, hφt, mul_comm]
  have hdual := integral_mul_skew_of_smooth_tests hp hq R T htest (hf.toLp f) (hg.toLp g)
  have hRf := (hR f hf).unique hpf
  have hTg := (hT g hg).unique hpg
  calc
    _ = ∫ t, R (hf.toLp f) t * hg.toLp g t := by
      apply integral_congr_ae
      filter_upwards [hRf, hg.coeFn_toLp] with t ht hgt
      rw [ht, hgt]
    _ = -(∫ t, hf.toLp f t * T (hg.toLp g) t) := hdual
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hTg] with t hft ht
      rw [hft, ht]

end HilbertUMD
