import HilbertUMD.UMD.UMD

/-! Transport finite-measure martingale tests into any sample-space universe.
The lifted process has exactly the same local integral identities and Lp norms.
No exponent restriction is needed for this transport. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace HilbertUMD

universe uΩ

/-- Lift each sigma algebra along the canonical equivalence with `ULift`. -/
def liftedFiltration {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    (ℱ : Filtration ι ‹MeasurableSpace Ω›) :
    Filtration ι (inferInstance : MeasurableSpace (ULift.{uΩ} Ω)) where
  seq i := (ℱ i).map ULift.up
  mono' := fun _ _ hij _ hs => ℱ.mono hij _ hs
  le' := fun i _ hs => ℱ.le i _ hs

theorem IsLpMartingale.ulift {Ω ι E : Type*} [MeasurableSpace Ω] [Preorder ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ℱ : Filtration ι ‹MeasurableSpace Ω›} {p : ℝ≥0∞} {μ : Measure Ω}
    {f : ι → Ω → E} (hf : IsLpMartingale f ℱ p μ) :
    IsLpMartingale (fun i (x : ULift.{uΩ} Ω) => f i x.down)
      (liftedFiltration ℱ) p (μ.map ULift.up) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (hf.stronglyAdapted i).comp_measurable
      (@measurable_down Ω (ℱ i))
  · intro i
    exact MeasurableEquiv.ulift.symm.memLp_map_measure_iff.mpr (hf.memLp i)
  · intro i j hij s hs hμs
    have he : MeasurableEmbedding (ULift.up : Ω → ULift.{uΩ} Ω) :=
      MeasurableEquiv.ulift.symm.measurableEmbedding
    rw [he.setIntegral_map, he.setIntegral_map]
    exact hf.setIntegral_eq i j hij (ULift.up ⁻¹' s) hs
      (by rwa [he.map_apply] at hμs)

/-- A UMD bound in any universe applies, with the same constant, to every
finite-measure test whose sample space lies in `Type 0`. -/
theorem UMDBound.test_finiteMeasure
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {p : ℝ≥0∞} {T : E →L[𝕜] F} {C : ℝ≥0} (hC : UMDBound.{uΩ} p T C)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : ℕ} (hm : 1 ≤ m) (ℱ : Filtration (Fin (m + 1)) ‹MeasurableSpace Ω›)
    (f : Fin (m + 1) → Ω → E) (hf : IsLpMartingale f ℱ p μ)
    (ε : Fin m → 𝕜) (hε : ∀ k, ‖ε k‖ = 1) :
    eLpNorm (martingaleTransform T ε f) p μ ≤
      (C : ℝ≥0∞) * eLpNorm (differenceSum f) p μ := by
  have h := hC (ULift.{uΩ} Ω) inferInstance (μ.map ULift.up) inferInstance
    m hm (liftedFiltration ℱ) inferInstance _ hf.ulift ε hε
  have he : MeasurableEmbedding (ULift.up : Ω → ULift.{uΩ} Ω) :=
    MeasurableEquiv.ulift.symm.measurableEmbedding
  rw [he.eLpNorm_map_measure, he.eLpNorm_map_measure] at h
  exact h

end HilbertUMD
