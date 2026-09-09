import HilbertUMD.UMD.UMDProbabilityReduction
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Simple terminal values suffice for the probability-space UMD tests

Conditional expectation acts contractively on Banach-valued L2. Thus a fixed
finite martingale transform is continuous as a function of its terminal value.
Density of simple functions extends a bound with the exact same constant.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace HilbertUMD

universe uΩ

namespace UMDTerminal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Banach-valued conditional expectation viewed as a map on L2. -/
def conditionalL2 (s : MeasurableSpace Ω) (g : Lp E 2 μ) : Lp E 2 μ :=
  ((Lp.memLp g).condExp (m := s) (by norm_num)).toLp (μ[g | s])

omit [IsFiniteMeasure μ] in
theorem conditionalL2_ae_eq (s : MeasurableSpace Ω) (g : Lp E 2 μ) :
    conditionalL2 (mΩ := mΩ) μ s g =ᵐ[μ] μ[g | s] := MemLp.coeFn_toLp _

theorem conditionalL2_lipschitz (s : MeasurableSpace Ω) :
    LipschitzWith 1 (conditionalL2 (mΩ := mΩ) (E := E) μ s) := by
  let : MeasurableSpace Ω := mΩ
  apply LipschitzWith.mk_one
  intro g h
  simp only [dist_eq_norm, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top (g - h))
  have heq : ⇑(conditionalL2 μ s g - conditionalL2 μ s h) =ᵐ[μ]
      μ[(⇑g - ⇑h) | s] :=
    (Lp.coeFn_sub _ _).trans (((conditionalL2_ae_eq μ s g).sub
      (conditionalL2_ae_eq μ s h)).trans
        (condExp_sub ((Lp.memLp g).integrable (by norm_num))
          ((Lp.memLp h).integrable (by norm_num)) s).symm)
  rw [eLpNorm_congr_ae heq, eLpNorm_congr_ae (Lp.coeFn_sub g h)]
  exact eLpNorm_condExp_le_eLpNorm _ (by norm_num)

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {m : ℕ} (ℱ : Filtration (Fin (m + 1)) ‹MeasurableSpace Ω›)
  (T : E →L[𝕜] F) (ε : Fin m → 𝕜)

/-- A fixed terminal martingale transform on the L2 quotient spaces. -/
def transformL2 (g : Lp E 2 μ) : Lp F 2 μ :=
  ∑ k : Fin m, ε k • (T.compLpL 2 μ)
    (conditionalL2 μ (ℱ k.succ) g - conditionalL2 μ (ℱ k.castSucc) g)

theorem transformL2_continuous : Continuous (transformL2 μ ℱ T ε) := by
  apply continuous_finsetSum
  intro k _
  exact ((T.compLpL 2 μ).continuous.comp
    ((conditionalL2_lipschitz μ _).continuous.sub
      (conditionalL2_lipschitz μ _).continuous)).const_smul (ε k)

omit [IsFiniteMeasure μ] in
theorem transformL2_ae_eq (g : Lp E 2 μ) :
    transformL2 μ ℱ T ε g =ᵐ[μ]
      martingaleTransform T ε (fun k => μ[g | ℱ k]) := by
  have hterm (k : Fin m) :
      ⇑(ε k • (T.compLpL 2 μ)
        (conditionalL2 μ (ℱ k.succ) g - conditionalL2 μ (ℱ k.castSucc) g)) =ᵐ[μ]
      fun x => ε k • T (μ[g | ℱ k.succ] x - μ[g | ℱ k.castSucc] x) := by
    filter_upwards [Lp.coeFn_smul (ε k) ((T.compLpL 2 μ)
        (conditionalL2 μ (ℱ k.succ) g - conditionalL2 μ (ℱ k.castSucc) g)),
      T.coeFn_compLpL (p := 2) (μ := μ)
        (conditionalL2 μ (ℱ k.succ) g - conditionalL2 μ (ℱ k.castSucc) g),
      Lp.coeFn_sub (conditionalL2 μ (ℱ k.succ) g) (conditionalL2 μ (ℱ k.castSucc) g),
      conditionalL2_ae_eq μ (ℱ k.succ) g, conditionalL2_ae_eq μ (ℱ k.castSucc) g]
      with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.smul_apply, Pi.sub_apply] at h₁ h₃
    rw [h₁, h₂, h₃, h₄, h₅]
  exact (Lp.coeFn_fun_finsetSum _ _).trans
    ((ae_all_iff.mpr hterm).mono fun x hx => Finset.sum_congr rfl (fun k _ => hx k))

omit [IsFiniteMeasure μ] in
theorem transformL2_toLp_ae_eq {g : Ω → E} (hg : MemLp g 2 μ) :
    transformL2 μ ℱ T ε (hg.toLp g) =ᵐ[μ]
      martingaleTransform T ε (fun k => μ[g | ℱ k]) := by
  refine (transformL2_ae_eq μ ℱ T ε _).trans ?_
  have heq (k : Fin (m + 1)) : μ[hg.toLp g | ℱ k] =ᵐ[μ] μ[g | ℱ k] :=
    condExp_congr_ae hg.coeFn_toLp
  filter_upwards [ae_all_iff.mpr heq] with x hx
  simp only [martingaleTransform, hx]

/-- Bounds on simple terminal values extend to arbitrary L2 terminal values. -/
theorem bound_of_simple (C : ℝ≥0)
    (h : ∀ g : SimpleFunc Ω E,
      eLpNorm (martingaleTransform T ε (fun k => μ[g | ℱ k])) 2 μ ≤
        (C : ℝ≥0∞) * eLpNorm g 2 μ)
    {g : Ω → E} (hg : MemLp g 2 μ) :
    eLpNorm (martingaleTransform T ε (fun k => μ[g | ℱ k])) 2 μ ≤
      (C : ℝ≥0∞) * eLpNorm g 2 μ := by
  have hb (v : Lp E 2 μ) : ‖transformL2 μ ℱ T ε v‖ ≤ (C : ℝ) * ‖v‖ := by
    refine (Lp.simpleFunc.denseRange (E := E) (μ := μ) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).induction_on
      (p := fun v : Lp E 2 μ => ‖transformL2 μ ℱ T ε v‖ ≤ (C : ℝ) * ‖v‖) v
      (isClosed_le (transformL2_continuous μ ℱ T ε).norm
        (continuous_const.mul continuous_norm)) ?_
    intro v
    let f := Lp.simpleFunc.toSimpleFunc v
    have hv : (v : Lp E 2 μ) = (Lp.simpleFunc.memLp v).toLp f :=
      Lp.ext ((Lp.simpleFunc.toSimpleFunc_eq_toFun v).symm.trans
        (Lp.simpleFunc.memLp v).coeFn_toLp.symm)
    rw [hv, Lp.norm_def,
      eLpNorm_congr_ae (transformL2_toLp_ae_eq μ ℱ T ε (Lp.simpleFunc.memLp v)),
      Lp.norm_toLp]
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.simpleFunc.memLp v).eLpNorm_ne_top) (h f)
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hh
  have hh := ENNReal.ofReal_le_ofReal (hb (hg.toLp g))
  simpa only [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ofReal_norm,
    Lp.enorm_def, eLpNorm_congr_ae (transformL2_toLp_ae_eq μ ℱ T ε hg),
    eLpNorm_congr_ae hg.coeFn_toLp] using hh

end UMDTerminal

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Probability-space terminal tests restricted to finite-valued functions. -/
def ProbabilitySimpleTerminalBound (T : E →L[𝕜] F) (C : ℝ≥0) : Prop :=
  ∀ (Ω : Type uΩ) (mΩ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
  ∀ (m : ℕ), 1 ≤ m →
  ∀ (ℱ : Filtration (Fin (m + 1)) mΩ) (g : SimpleFunc Ω E)
    (ε : Fin m → 𝕜), (∀ k, ‖ε k‖ = 1) →
    eLpNorm (martingaleTransform T ε (fun k => μ[g | ℱ k])) 2 μ ≤
      (C : ℝ≥0∞) * eLpNorm g 2 μ

theorem probabilityTerminalBound_of_simple {T : E →L[𝕜] F} {C : ℝ≥0}
    (h : ProbabilitySimpleTerminalBound.{uΩ} T C) : ProbabilityTerminalBound.{uΩ} 2 T C := by
  intro Ω mΩ μ hμ m hm ℱ g hg ε hε
  exact UMDTerminal.bound_of_simple μ ℱ T ε C
    (fun g => h Ω mΩ μ hμ m hm ℱ g ε hε) hg

/-- Simple probability-space terminal tests imply all sigma-finite UMD tests. -/
theorem umdBound_of_probabilitySimpleTerminalBound {T : E →L[𝕜] F} {C : ℝ≥0}
    (h : ProbabilitySimpleTerminalBound.{uΩ} T C) : UMDBound.{uΩ} 2 T C :=
  umdBound_of_probabilityTerminalBound (by norm_num) (by norm_num)
    (probabilityTerminalBound_of_simple h)

end HilbertUMD
