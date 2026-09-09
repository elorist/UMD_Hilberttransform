import HilbertUMD.Hilbert.HilbertTwoKernel
import HilbertUMD.Hilbert.HilbertPVBounds
import HilbertUMD.Interfaces.HilbertInterval
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-! The existing L2 PV extension determines the Fourier L2 operator by
linearity, its norm bound, and agreement on compact smooth functions. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace HilbertUMD
namespace HilbertTwoPV

private theorem exists_pv (f : RealL2) :
    ∃ g : ℝ → ℝ, MemLp g 2 volume ∧ IsHilbertPVAe f g ∧
      eLpNorm g 2 volume ≤ eLpNorm f 2 volume := by
  obtain ⟨g, hpv, hg, hn⟩ := Interfaces.HilbertBound.l2_pv_extension
    hilbertBound_two_real_scalar f (Lp.memLp f)
  exact ⟨g, hg, by simpa using hpv, by simpa using hn⟩

private def output (f : RealL2) : ℝ → ℝ := (exists_pv f).choose
private theorem output_memLp (f : RealL2) : MemLp (output f) 2 volume :=
  (exists_pv f).choose_spec.1
private def value (f : RealL2) : RealL2 := (output_memLp f).toLp (output f)
private theorem value_pv (f : RealL2) : IsHilbertPVAe f (value f) :=
  (exists_pv f).choose_spec.2.1.congr_output (output_memLp f).coeFn_toLp.symm
private theorem value_norm (f : RealL2) : ‖value f‖ ≤ ‖f‖ := by
  rw [value, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (exists_pv f).choose_spec.2.2

private def linear : RealL2 →ₗ[ℝ] RealL2 where
  toFun := value
  map_add' f g := by
    apply Lp.ext
    have hp := ((value_pv f).add_two (value_pv g) (Lp.memLp f) (Lp.memLp g)).congr_input
      (Lp.coeFn_add f g).symm
    exact ((value_pv (f+g)).unique hp).trans (Lp.coeFn_add (value f) (value g)).symm
  map_smul' c f := by
    apply Lp.ext
    have hp := ((value_pv f).smul_real c).congr_input (Lp.coeFn_smul c f).symm
    exact ((value_pv (c • f)).unique hp).trans (Lp.coeFn_smul c (value f)).symm

private def operator : RealL2 →L[ℝ] RealL2 :=
  linear.mkContinuous 1 (fun f => by simpa [linear] using value_norm f)

private theorem operator_eq_fourier : operator = realHilbertL2.toContinuousLinearMap := by
  apply DFunLike.ext'
  have hd := Lp.dense_hasCompactSupport_contDiff (E := ℝ) (F := ℝ)
    (μ := (volume : Measure ℝ)) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  apply Continuous.ext_on hd operator.continuous realHilbertL2.continuous
  rintro f ⟨φ, hφf, hc, hφ⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  obtain ⟨g, hg, hpv, heq⟩ := Interfaces.real_scalar_pv_fourier φ hφ1 hc
  have hfeq : f = (hilbertTest_memLp hφ1 hc 2).toLp φ :=
    Lp.ext (hφf.trans (hilbertTest_memLp hφ1 hc 2).coeFn_toLp.symm)
  have hout : g =ᵐ[volume] realHilbertL2 f := by
    rw [hfeq, ← heq]
    exact hg.coeFn_toLp.symm
  apply Lp.ext
  exact ((value_pv f).unique (hpv.ae.congr_input hφf.symm)).trans hout

end HilbertTwoPV

/-- The actual Fourier L2 transform realizes PV for every scalar L2 input.
This deduction uses the existing smooth-test identification and L2 extension. -/
theorem realHilbertL2_pv_all (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    IsHilbertPVAe f (realHilbertL2 (hf.toLp f)) := by
  have hp := (HilbertTwoPV.value_pv (hf.toLp f)).congr_input hf.coeFn_toLp
  change IsHilbertPVAe f (HilbertTwoPV.operator (hf.toLp f)) at hp
  rwa [HilbertTwoPV.operator_eq_fourier] at hp

end HilbertUMD
