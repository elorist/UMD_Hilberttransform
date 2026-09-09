import HilbertUMD.Hilbert.HilbertL2

/-!
# Naturality of the Hilbert-valued Fourier and Hilbert transforms

Commutation with continuous complex-linear maps follows first for Schwartz
functions by passing the map through the Fourier integral, then on L² by density.
These results have no admitted dependencies.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace HilbertUMD.HilbertValued

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Continuous complex-linear maps commute with the L² Fourier transform. -/
theorem fourier_compLp (A : F →L[ℂ] G) (f : L2Space F) :
    (Lp.fourierTransformₗᵢ ℝ G) (A.compLpL 2 volume f) =
      A.compLpL 2 volume ((Lp.fourierTransformₗᵢ ℝ F) f) := by
  have hpost (s : SchwartzMap ℝ F) :
      (s.postcompCLM A).toLp 2 = A.compLpL 2 volume (s.toLp 2) := by
    apply Lp.ext
    filter_upwards [(s.postcompCLM A).coeFn_toLp 2,
      A.coeFn_compLp (s.toLp 2), s.coeFn_toLp 2] with x hp hA hs
    change ((s.postcompCLM A).toLp 2) x = A.compLp (s.toLp 2) x
    rw [hp, hA, hs, SchwartzMap.postcompCLM_apply]
  have hfourier (s : SchwartzMap ℝ F) :
      𝓕 (s.postcompCLM A) = (𝓕 s).postcompCLM A := by
    ext x
    change 𝓕 (fun y => A (s y)) x = A (𝓕 (s : ℝ → F) x)
    rw [Real.fourier_eq, Real.fourier_eq,
      ← A.integral_comp_comm ((Real.fourierIntegral_convergent_iff x).mpr s.integrable)]
    simp only [Circle.smul_def, map_smul]
  apply DenseRange.induction_on (p := fun f : L2Space F =>
    (Lp.fourierTransformₗᵢ ℝ G) (A.compLpL 2 volume f) =
      A.compLpL 2 volume ((Lp.fourierTransformₗᵢ ℝ F) f))
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := F)
      (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ ℝ G).continuous.comp (A.compLpL 2 volume).continuous)
      ((A.compLpL 2 volume).continuous.comp (Lp.fourierTransformₗᵢ ℝ F).continuous)
  · intro s
    simp only [SchwartzMap.toLpCLM_apply]
    rw [← hpost]
    change 𝓕 ((s.postcompCLM A).toLp 2) = A.compLpL 2 volume (𝓕 (s.toLp 2))
    rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq, hfourier, hpost]

/-- Continuous complex-linear maps commute with the Hilbert-valued Hilbert transform. -/
theorem hilbertL2_compLp (A : F →L[ℂ] G) (f : L2Space F) :
    hilbertL2 G (A.compLpL 2 volume f) = A.compLpL 2 volume (hilbertL2 F f) := by
  apply (Lp.fourierTransformₗᵢ ℝ G).injective
  rw [fourier_hilbertL2, fourier_compLp, fourier_compLp, fourier_hilbertL2]
  apply Lp.ext
  filter_upwards [multiplier_coeFn G (A.compLpL 2 volume ((Lp.fourierTransformₗᵢ ℝ F) f)),
    A.coeFn_compLpL ((Lp.fourierTransformₗᵢ ℝ F) f),
    A.coeFn_compLpL (multiplier F ((Lp.fourierTransformₗᵢ ℝ F) f)),
    multiplier_coeFn F ((Lp.fourierTransformₗᵢ ℝ F) f)] with x h₁ h₂ h₃ h₄
  change multiplier G (A.compLpL 2 volume ((Lp.fourierTransformₗᵢ ℝ F) f)) x =
    (A.compLpL 2 volume (multiplier F ((Lp.fourierTransformₗᵢ ℝ F) f))) x
  rw [h₁, h₂, h₃, h₄, map_smul]

/-- The Hilbert-valued construction on complex scalars is the scalar construction. -/
theorem hilbertL2_complex (f : ComplexL2) : hilbertL2 ℂ f = HilbertUMD.hilbertL2 f := rfl

end HilbertUMD.HilbertValued
