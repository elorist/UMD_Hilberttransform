import HilbertUMD.Hilbert.HilbertFourBound
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compatibility of the independent L4 extension with Fourier L2

Smooth localization lets us use Schwartz density in L4 while controlling
both the L2 and L4 limits. Uniqueness in measure identifies the outputs.
No principal-value extension theorem is used.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace HilbertUMD.HilbertFourCompatibility

local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
private instance : ENNReal.HolderTriple 4 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by simp)).mp
  norm_num [ENNReal.toReal_add]⟩

open HilbertFourBound

/-- Continuous maps into different Lp spaces retain a.e. agreement under common limits. -/
theorem ae_eq_of_common_limit {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {F : ℕ → Lp ℝ p (volume : Measure ℝ)} {G : ℕ → Lp ℝ q (volume : Measure ℝ)}
    {f : Lp ℝ p (volume : Measure ℝ)} {g : Lp ℝ q (volume : Measure ℝ)}
    (hF : Tendsto F atTop (𝓝 f)) (hG : Tendsto G atTop (𝓝 g))
    (hFG : ∀ n, F n =ᵐ[volume] G n) : f =ᵐ[volume] g := by
  apply tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_Lp hF)
  exact (tendstoInMeasure_of_tendsto_Lp hG).congr_left (fun n => (hFG n).symm)

private theorem exists_schwartz_seq (f : Lp ℝ 4 (volume : Measure ℝ)) :
    ∃ u : ℕ → SchwartzMap ℝ ℝ, Tendsto (fun n => (u n).toLp 4) atTop (𝓝 f) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℝ)
    (p := 4) (μ := (volume : Measure ℝ)) (by norm_num)
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp (hd f)
  choose u hu using hv
  refine ⟨u, ?_⟩
  exact ht.congr' (Eventually.of_forall fun n => (hu n).symm)

def multiplyToTwo (η : SchwartzMap ℝ ℝ) :
    Lp ℝ 4 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL volume 4 4 2 (η.toLp 4)

def multiplyToFour (η : SchwartzMap ℝ ℝ) :
    Lp ℝ 4 (volume : Measure ℝ) →L[ℝ] Lp ℝ 4 (volume : Measure ℝ) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL volume ∞ 4 4 (η.toLp ∞)

theorem multiplyToTwo_ae (η : SchwartzMap ℝ ℝ) (f : Lp ℝ 4 (volume : Measure ℝ)) :
    multiplyToTwo η f =ᵐ[volume] fun x => η x * f x := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (η.toLp 4) f,
    η.coeFn_toLp 4] with x hx hη
  change multiplyToTwo η f x = _ at hx
  simpa only [ContinuousLinearMap.mul_apply', hη] using hx

theorem multiplyToFour_ae (η : SchwartzMap ℝ ℝ) (f : Lp ℝ 4 (volume : Measure ℝ)) :
    multiplyToFour η f =ᵐ[volume] fun x => η x * f x := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 4) (η.toLp ∞) f,
    η.coeFn_toLp ∞] with x hx hη
  change multiplyToFour η f x = _ at hx
  simpa only [ContinuousLinearMap.mul_apply', hη] using hx

private def product (η u : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (η : ℝ → ℝ) u

private theorem product_apply (η u : SchwartzMap ℝ ℝ) (x : ℝ) :
    product η u x = η x * u x := by
  simp only [product, SchwartzMap.smulLeftCLM_apply_apply η.hasTemperateGrowth, smul_eq_mul]

private theorem multiplyToTwo_schwartz (η u : SchwartzMap ℝ ℝ) :
    multiplyToTwo η (u.toLp 4) = (product η u).toLp 2 := by
  apply Lp.ext
  filter_upwards [multiplyToTwo_ae η (u.toLp 4), u.coeFn_toLp 4,
    (product η u).coeFn_toLp 2] with x hη hu hp
  rw [hη, hu, hp, product_apply]

private theorem multiplyToFour_schwartz (η u : SchwartzMap ℝ ℝ) :
    multiplyToFour η (u.toLp 4) = (product η u).toLp 4 := by
  apply Lp.ext
  filter_upwards [multiplyToFour_ae η (u.toLp 4), u.coeFn_toLp 4,
    (product η u).coeFn_toLp 4] with x hη hu hp
  rw [hη, hu, hp, product_apply]

/-- Compatibility after multiplying an arbitrary L4 input by a Schwartz cutoff. -/
theorem agree_localized (η : SchwartzMap ℝ ℝ) (f : Lp ℝ 4 (volume : Measure ℝ)) :
    realHilbertFour (multiplyToFour η f) =ᵐ[volume] realHilbertL2 (multiplyToTwo η f) := by
  obtain ⟨u, hu⟩ := exists_schwartz_seq f
  apply ae_eq_of_common_limit
    ((realHilbertFour.continuous.tendsto _).comp ((multiplyToFour η).continuous.tendsto _ |>.comp hu))
    ((realHilbertL2.continuous.tendsto _).comp ((multiplyToTwo η).continuous.tendsto _ |>.comp hu))
  intro n
  simp only [Function.comp_apply]
  rw [multiplyToFour_schwartz, multiplyToTwo_schwartz]
  exact realHilbertFour_schwartz _

def cutoffBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := n + 1
  rOut := n + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def cutoff (n : ℕ) : SchwartzMap ℝ ℝ :=
  (cutoffBump n).hasCompactSupport.toSchwartzMap (cutoffBump n).contDiff

theorem cutoff_bounds (n : ℕ) (x : ℝ) : 0 ≤ cutoff n x ∧ cutoff n x ≤ 1 :=
  ⟨(cutoffBump n).nonneg, (cutoffBump n).le_one⟩

theorem eventually_cutoff_one (x : ℝ) : ∀ᶠ n : ℕ in atTop, cutoff n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  apply (cutoffBump n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  change |x| ≤ (n : ℝ) + 1
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem cutoff_memLp {p : ℝ≥0∞} {f : ℝ → ℝ} (hf : MemLp f p volume) (n : ℕ) :
    MemLp (fun x => cutoff n x * f x) p volume := by
  apply hf.of_le ((cutoff n).continuous.aestronglyMeasurable.mul hf.1)
  filter_upwards with x
  change ‖cutoff n x * f x‖ ≤ ‖f x‖
  rw [norm_mul, Real.norm_of_nonneg (cutoff_bounds n x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_bounds n x).2

/-- The same sequence of smooth cutoffs converges in every finite positive integer Lp. -/
theorem cutoff_tendsto {p : ℕ} (hp : p ≠ 0) [Fact ((1 : ℝ≥0∞) ≤ p)]
    {f : ℝ → ℝ} (hf : MemLp f p volume) :
    Tendsto (fun n => (cutoff_memLp hf n).toLp (fun x => cutoff n x * f x))
      atTop (𝓝 (hf.toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  have hi := hf.integrable_norm_pow hp
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => ‖cutoff n x * f x - f x‖ ^ p) volume :=
    ((cutoff_memLp hf n).1.sub hf.1).norm.pow p
  have hb (n : ℕ) : ∀ᵐ x ∂volume,
      ‖‖cutoff n x * f x - f x‖ ^ p‖ ≤ ‖f x‖ ^ p := by
    filter_upwards with x
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [← sub_one_mul, norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (abs_le.mpr ⟨by linarith [(cutoff_bounds n x).1], by linarith [(cutoff_bounds n x).2]⟩)
  have hl : ∀ᵐ x ∂volume, Tendsto (fun n => ‖cutoff n x * f x - f x‖ ^ p)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_cutoff_one x] with n hn
    simp [hn, hp]
  have hc := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ ^ p) hm hi hb hl
  simp only [integral_zero] at hc
  have hp' : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hr := hc.rpow_const (p := (p : ℝ)⁻¹) (Or.inr (by positivity))
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  convert he using 1
  · funext n
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hp) (by finiteness)
      ((cutoff_memLp hf n).sub hf)]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Function.comp_apply, Pi.sub_apply]
  · simp [Real.zero_rpow (inv_ne_zero (ne_of_gt hp'))]

private theorem multiplyToFour_toLp (η : SchwartzMap ℝ ℝ) {f : ℝ → ℝ}
    (hf : MemLp f 4 volume) (hηf : MemLp (fun x => η x * f x) 4 volume) :
    multiplyToFour η (hf.toLp f) = hηf.toLp _ := by
  apply Lp.ext
  filter_upwards [multiplyToFour_ae η (hf.toLp f), hf.coeFn_toLp, hηf.coeFn_toLp]
    with x hmul hfx hηfx
  rw [hmul, hfx, hηfx]

private theorem multiplyToTwo_toLp (η : SchwartzMap ℝ ℝ) {f : ℝ → ℝ}
    (hf : MemLp f 4 volume) (hηf : MemLp (fun x => η x * f x) 2 volume) :
    multiplyToTwo η (hf.toLp f) = hηf.toLp _ := by
  apply Lp.ext
  filter_upwards [multiplyToTwo_ae η (hf.toLp f), hf.coeFn_toLp, hηf.coeFn_toLp]
    with x hmul hfx hηfx
  rw [hmul, hfx, hηfx]

/-- The independent L4 extension agrees with Fourier L2 on the full intersection. -/
theorem realHilbertFour_agrees_two (f : ℝ → ℝ) (h2 : MemLp f 2 volume)
    (h4 : MemLp f 4 volume) :
    realHilbertFour (h4.toLp f) =ᵐ[volume] realHilbertL2 (h2.toLp f) := by
  let : Fact ((1 : ℝ≥0∞) ≤ (4 : ℕ)) := ⟨by norm_num⟩
  let : Fact ((1 : ℝ≥0∞) ≤ (2 : ℕ)) := ⟨by norm_num⟩
  apply ae_eq_of_common_limit
    ((realHilbertFour.continuous.tendsto _).comp (cutoff_tendsto (by norm_num) h4))
    ((realHilbertL2.continuous.tendsto _).comp (cutoff_tendsto (by norm_num) h2))
  intro n
  have hn := agree_localized (cutoff n) (h4.toLp f)
  rw [multiplyToFour_toLp _ h4 (cutoff_memLp h4 n),
    multiplyToTwo_toLp _ h4 (cutoff_memLp h2 n)] at hn
  exact hn

/-- The L4 bound applies to the actual Fourier operator on every L2 intersect L4 input. -/
theorem realHilbertL2_eLpNorm_four_le (f : ℝ → ℝ) (h2 : MemLp f 2 volume)
    (h4 : MemLp f 4 volume) :
    eLpNorm (fun x => realHilbertL2 (h2.toLp f) x) 4 volume ≤
      (5 / 2) * eLpNorm f 4 volume := by
  rw [← eLpNorm_congr_ae (realHilbertFour_agrees_two f h2 h4), ← Lp.enorm_def,
    ← Lp.enorm_toLp h4]
  apply realHilbertFour.le_of_opENorm_le
  rw [← ofReal_norm]
  have h := ENNReal.ofReal_le_ofReal realHilbertFour_norm_le
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_ofNat] at h
  exact h

end HilbertUMD.HilbertFourCompatibility
