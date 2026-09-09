import HilbertUMD.Interfaces.MartingaleReduction

/-! At exponent two, the UMD bound and operator constant are independent of
the sample-space universe. Every universe gives the same finite dyadic
terminal tests, with no loss in the constant. The equality includes operators
whose UMD constant is infinite. -/

noncomputable section
open scoped ENNReal NNReal
namespace HilbertUMD

universe uΩ vΩ

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The finite dyadic characterization preserves the constant in every universe. -/
theorem umdBound_two_iff_finiteDyadicTerminalBound (T : E →L[𝕜] F) (C : ℝ≥0) :
    UMDBound.{uΩ} 2 T C ↔ FiniteDyadicTerminalBound 2 T C :=
  ⟨UMDBound.finiteDyadicTerminal_two,
    Interfaces.umdBound_of_finiteDyadicTerminalBound T C⟩

/-- Change the sample-space universe without changing the exponent-two bound. -/
theorem UMDBound.changeUniverse_two {T : E →L[𝕜] F} {C : ℝ≥0}
    (hC : UMDBound.{uΩ} 2 T C) : UMDBound.{vΩ} 2 T C :=
  (umdBound_two_iff_finiteDyadicTerminalBound T C).mpr
    ((umdBound_two_iff_finiteDyadicTerminalBound T C).mp hC)

/-- The operator UMD constant at exponent two is the same in any two universes. -/
theorem umdConstant_two_universe_eq (T : E →L[𝕜] F) :
    umdConstant.{uΩ} 2 T = umdConstant.{vΩ} 2 T := by
  apply le_antisymm
  · exact le_umdConstant fun _ hC => umdConstant_le hC.changeUniverse_two
  · exact le_umdConstant fun _ hC => umdConstant_le hC.changeUniverse_two

end HilbertUMD
