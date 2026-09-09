import HilbertUMD.UMD.UMD
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Reduction of UMD tests to probability-space terminal values

This module proves the measure-theoretic and terminal-value parts of the
Paley-Walsh reduction, without assuming the binary-tree approximation theorem.
The sample-space universe and the bound are preserved throughout.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace HilbertUMD

universe uΩ

section Restriction

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {m : ℕ} {ℱ : Filtration (Fin (m + 1)) ‹MeasurableSpace Ω›}
  {p : ℝ≥0∞} {f : Fin (m + 1) → Ω → E}

/-- Restricting to an event known initially preserves the martingale property. -/
theorem IsLpMartingale.restrict_initial (hf : IsLpMartingale f ℱ p μ)
    {s : Set Ω} (hs : MeasurableSet[ℱ 0] s) :
    IsLpMartingale f ℱ p (μ.restrict s) := by
  refine ⟨hf.stronglyAdapted, fun i => (hf.memLp i).restrict s, ?_⟩
  intro i j hij t ht hμt
  have hs' : MeasurableSet s := ℱ.le 0 s hs
  rw [Measure.restrict_restrict (ℱ.le i t ht)]
  apply hf.setIntegral_eq i j hij (t ∩ s)
  · exact ht.inter (ℱ.mono (Fin.zero_le i) s hs)
  · simpa only [Measure.restrict_apply' hs'] using hμt

/-- Multiplying a finite measure by a finite scalar preserves Lp martingales. -/
theorem IsLpMartingale.smul_finite_measure [IsFiniteMeasure μ]
    (hf : IsLpMartingale f ℱ p μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    IsLpMartingale f ℱ p (c • μ) := by
  refine ⟨hf.stronglyAdapted, fun i => (hf.memLp i).smul_measure hc, ?_⟩
  intro i j hij s hs _
  simp only [Measure.restrict_smul, integral_smul_measure]
  rw [hf.setIntegral_eq i j hij s hs (measure_lt_top μ s)]

end Restriction

section Bounds

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The original UMD inequality tested only on finite measure spaces. -/
def FiniteMeasureUMDBound (p : ℝ≥0∞) (T : E →L[𝕜] F) (C : ℝ≥0) : Prop :=
  ∀ (Ω : Type uΩ) (mΩ : MeasurableSpace Ω) (μ : Measure Ω), IsFiniteMeasure μ →
  ∀ (m : ℕ), 1 ≤ m →
  ∀ (ℱ : Filtration (Fin (m + 1)) mΩ)
    (f : Fin (m + 1) → Ω → E), IsLpMartingale f ℱ p μ →
  ∀ (ε : Fin m → 𝕜), (∀ k, ‖ε k‖ = 1) →
    eLpNorm (martingaleTransform T ε f) p μ ≤
      (C : ℝ≥0∞) * eLpNorm (differenceSum f) p μ

/-- Finite-measure tests imply the original sigma-finite inequality with the
same constant. The exhaustion is measurable in the initial sigma algebra. -/
theorem umdBound_of_finiteMeasureUMDBound {p : ℝ≥0∞} {T : E →L[𝕜] F} {C : ℝ≥0}
    (h : FiniteMeasureUMDBound.{uΩ} p T C) : UMDBound.{uΩ} p T C := by
  intro Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε
  let μ₀ := μ.trim (ℱ.le 0)
  let s : ℕ → Set Ω := @spanningSets Ω (ℱ 0) μ₀ inferInstance
  have hs₀ (n : ℕ) : MeasurableSet[ℱ 0] (s n) :=
    @measurableSet_spanningSets Ω (ℱ 0) μ₀ _ n
  have hs (n : ℕ) : MeasurableSet (s n) := ℱ.le 0 _ (hs₀ n)
  have hsfin (n : ℕ) : μ (s n) < ∞ := by
    rw [← trim_measurableSet_eq (ℱ.le 0) (hs₀ n)]
    exact @measure_spanningSets_lt_top Ω (ℱ 0) μ₀ _ n
  have hbound (n : ℕ) :
      eLpNorm ((s n).indicator (martingaleTransform T ε f)) p μ ≤
        (C : ℝ≥0∞) * eLpNorm (differenceSum f) p μ := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hs n)]
    have hfin : IsFiniteMeasure (μ.restrict (s n)) := ⟨by simpa using hsfin n⟩
    exact (h Ω mΩ (μ.restrict (s n)) hfin m hm ℱ f
      (hf.restrict_initial (hs₀ n)) ε hε).trans
        (mul_le_mul' le_rfl (eLpNorm_restrict_le _ _ _ _))
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop (α := ℕ)) (Eventually.of_forall hbound)
    (fun n => (martingaleTransform_memLp T ε hf.memLp).aestronglyMeasurable.indicator (hs n))
  exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
    ((@eventually_mem_spanningSets Ω (ℱ 0) μ₀ _ x).mono fun n hn =>
      (Set.indicator_of_mem hn _).symm)

variable [CompleteSpace E]

/-- Terminal conditional-expectation tests on probability spaces. -/
def ProbabilityTerminalBound (p : ℝ≥0∞) (T : E →L[𝕜] F) (C : ℝ≥0) : Prop :=
  ∀ (Ω : Type uΩ) (mΩ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
  ∀ (m : ℕ), 1 ≤ m →
  ∀ (ℱ : Filtration (Fin (m + 1)) mΩ) (g : Ω → E), MemLp g p μ →
  ∀ (ε : Fin m → 𝕜), (∀ k, ‖ε k‖ = 1) →
    eLpNorm (martingaleTransform T ε (fun k => μ[g | ℱ k])) p μ ≤
      (C : ℝ≥0∞) * eLpNorm g p μ

/-- A finite-measure martingale is the conditional-expectation process of its
terminal value. Subtracting its initial value does not alter its transform. -/
theorem martingaleTransform_condExp_differenceSum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {m : ℕ}
    {ℱ : Filtration (Fin (m + 1)) ‹MeasurableSpace Ω›}
    {f : Fin (m + 1) → Ω → E} (hf : IsLpMartingale f ℱ p μ)
    (T : E →L[𝕜] F) (ε : Fin m → 𝕜) :
    martingaleTransform T ε (fun k => μ[differenceSum f | ℱ k]) =ᵐ[μ]
      martingaleTransform T ε f := by
  have hfm := hf.martingale (fun k => (hf.memLp k).integrable hp)
  have heq (k : Fin (m + 1)) :
      μ[differenceSum f | ℱ k] =ᵐ[μ] fun x => f k x - f 0 x := by
    have hd : differenceSum f = f (Fin.last m) - f 0 := funext (differenceSum_eq f)
    rw [hd]
    refine (condExp_sub (hfm.integrable _) (hfm.integrable _) _).trans ?_
    rw [condExp_of_stronglyMeasurable (ℱ.le k)
      ((hf.stronglyAdapted 0).mono (ℱ.mono (Fin.zero_le k))) (hfm.integrable 0)]
    exact (hfm.condExp_ae_eq (Fin.le_last k)).sub (EventuallyEq.rfl)
  filter_upwards [ae_all_iff.mpr heq] with x hx
  simp only [martingaleTransform, hx]
  congr 1
  ext k
  congr 2
  abel

/-- Normalization of finite measures and centering the terminal value preserve
the constant in the martingale-transform inequality. -/
theorem finiteMeasureUMDBound_of_probabilityTerminalBound
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {T : E →L[𝕜] F} {C : ℝ≥0} (h : ProbabilityTerminalBound.{uΩ} p T C) :
    FiniteMeasureUMDBound.{uΩ} p T C := by
  intro Ω mΩ μ hμ m hm ℱ f hf ε hε
  by_cases hzero : μ = 0
  · simp [hzero]
  have hmass : μ Set.univ ≠ 0 := by simpa using hzero
  let ν : Measure Ω := (μ Set.univ)⁻¹ • μ
  have hν : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass (measure_ne_top μ _)⟩
  have hfν : IsLpMartingale f ℱ p ν :=
    hf.smul_finite_measure (ENNReal.inv_ne_top.mpr hmass)
  have heq := martingaleTransform_condExp_differenceSum hp hfν T ε
  have hb := h Ω mΩ ν hν m hm ℱ (differenceSum f)
    (differenceSum_memLp hfν.memLp) ε hε
  rw [eLpNorm_congr_ae heq] at hb
  have hμν : μ = μ Set.univ • ν := by
    simp only [ν, smul_smul, ENNReal.mul_inv_cancel hmass (measure_ne_top μ _), one_smul]
  rw [hμν]
  simp only [eLpNorm_smul_measure_of_ne_top (μ := ν) hp_top]
  simpa only [smul_eq_mul, mul_left_comm (C : ℝ≥0∞)] using
    mul_le_mul' (le_refl ((μ Set.univ) ^ (1 / p).toReal)) hb

/-- The original UMD bound follows from probability-space terminal tests. -/
theorem umdBound_of_probabilityTerminalBound
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {T : E →L[𝕜] F} {C : ℝ≥0} (h : ProbabilityTerminalBound.{uΩ} p T C) :
    UMDBound.{uΩ} p T C :=
  umdBound_of_finiteMeasureUMDBound
    (finiteMeasureUMDBound_of_probabilityTerminalBound hp hp_top h)

end Bounds

end HilbertUMD
