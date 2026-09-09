import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Approximation at Lebesgue points for kernels with quadratic decay

A dyadic majorant reduces the contribution of a kernel bounded by `C / ε`
near the origin and `C * ε / |y|²` away from it to a summable series of
local averages. This is the pointwise estimate needed to compare smooth
Hilbert kernels with sharp truncations.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace HilbertUMD.LebesgueDecayApproximation

def mean (u : ℝ → ℝ) (x r : ℝ) : ℝ :=
  (2 * r)⁻¹ * ∫ y in closedBall x r, u y

theorem mean_eq_average (u : ℝ → ℝ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    mean u x r = ⨍ y in closedBall x r, u y := by
  rw [setAverage_eq, measureReal_def, Real.volume_closedBall,
    ENNReal.toReal_ofReal (by positivity)]
  rfl

theorem mean_nonneg {u : ℝ → ℝ} (hu : ∀ y, 0 ≤ u y) (x : ℝ) {r : ℝ}
    (hr : 0 ≤ r) : 0 ≤ mean u x r := by
  exact mul_nonneg (inv_nonneg.mpr (by positivity)) (integral_nonneg hu)

def dyadicMean (u : ℝ → ℝ) (x ε : ℝ) : ℝ :=
  ∑' n : ℕ, (1 / 2 : ℝ) ^ n * mean u x ((2 : ℝ) ^ n * ε)

theorem summable_dyadicMean {u : ℝ → ℝ} {x M ε : ℝ}
    (hu : ∀ y, 0 ≤ u y) (hε : 0 < ε)
    (hM : ∀ r > 0, mean u x r ≤ M) :
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n * mean u x ((2 : ℝ) ^ n * ε)) := by
  apply (summable_geometric_two.mul_right M).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (mean_nonneg hu x (by positivity)))]
  exact mul_le_mul_of_nonneg_left (hM _ (by positivity)) (by positivity)

theorem dyadicMean_tendsto_zero {u : ℝ → ℝ} {x M : ℝ}
    (hu : ∀ y, 0 ≤ u y) (hM : ∀ r > 0, mean u x r ≤ M)
    (hlim : Tendsto (mean u x) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (dyadicMean u x) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (summable_geometric_two.mul_right M)
    (f := fun ε n => (1 / 2 : ℝ) ^ n * mean u x ((2 : ℝ) ^ n * ε))
    (g := fun _ => (0 : ℝ)) ?_ ?_
  · unfold dyadicMean
    simpa only [tsum_zero] using h
  · intro n
    have ht : Tendsto (fun ε : ℝ => (2 : ℝ) ^ n * ε) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using hid.const_mul ((2 : ℝ) ^ n)
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n) (show 0 < ε from hε)
    simpa using (hlim.comp ht).const_mul ((1 / 2 : ℝ) ^ n)
  · filter_upwards [self_mem_nhdsWithin] with ε hε n
    have hε : 0 < ε := hε
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (mean_nonneg hu x (by positivity)))]
    exact mul_le_mul_of_nonneg_left (hM _ (by positivity)) (by positivity)

private def coeff (C ε : ℝ) (n : ℕ) : ℝ :=
  4 * C / (ε * ((2 : ℝ) ^ n) ^ 2)

private theorem coeff_integral (u : ℝ → ℝ) (x C : ℝ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    coeff C ε n * (∫ y in closedBall x ((2 : ℝ) ^ n * ε), u y) =
      8 * C * ((1 / 2 : ℝ) ^ n * mean u x ((2 : ℝ) ^ n * ε)) := by
  simp only [coeff, mean, one_div, inv_pow]
  field_simp
  ring

private theorem exists_coeff_bound {C ε d : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (_hd : 0 ≤ d) :
    ∃ n : ℕ, d ≤ (2 : ℝ) ^ n * ε ∧
      (if d ≤ ε then C / ε else C * ε / d ^ 2) ≤ coeff C ε n := by
  by_cases h : d ≤ ε
  · refine ⟨0, by simpa, ?_⟩
    simp only [h, ↓reduceIte, coeff, pow_zero, one_pow, mul_one]
    gcongr
    linarith
  · have hed : ε < d := lt_of_not_ge h
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ d / ε by
      exact (le_div_iff₀ hε).mpr (by linarith)) (show (1 : ℝ) < 2 by norm_num)
    refine ⟨n + 1, ((div_lt_iff₀ hε).mp hn').le, ?_⟩
    rw [if_neg h]
    have hn0 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hnle : (2 : ℝ) ^ n * ε ≤ d := (le_div_iff₀ hε).mp hn
    calc
      C * ε / d ^ 2 ≤ C * ε / (((2 : ℝ) ^ n * ε) ^ 2) := by gcongr
      _ = coeff C ε (n + 1) := by
        simp only [coeff, pow_succ]
        field_simp
        ring

/-- The integral estimate does not presuppose integrability of the kernel. -/
theorem lintegral_decay_bound {u : ℝ → ℝ} {x C M ε : ℝ} {v : ℝ → ℝ}
    (hu : ∀ y, 0 ≤ u y) (hi : LocallyIntegrable u volume)
    (hC : 0 ≤ C) (hε : 0 < ε) (hM : ∀ r > 0, mean u x r ≤ M)
    (hv : ∀ y, ‖v y‖ ≤
      (if |x - y| ≤ ε then C / ε else C * ε / |x - y| ^ 2) * u y) :
    (∫⁻ y, ‖v y‖ₑ) ≤ ENNReal.ofReal (8 * C * dyadicMean u x ε) := by
  let F : ℕ → ℝ → ℝ := fun n =>
    (closedBall x ((2 : ℝ) ^ n * ε)).indicator (fun y => coeff C ε n * u y)
  have hF (n : ℕ) : Integrable (F n) := by
    apply (integrable_indicator_iff measurableSet_closedBall).mpr
    exact (hi.integrableOn_isCompact (isCompact_closedBall _ _)).const_mul _
  have hFn (n : ℕ) (y : ℝ) : 0 ≤ F n y := by
    apply indicator_nonneg _
    intro z hz
    exact mul_nonneg (by dsimp [coeff]; positivity) (hu z)
  have hFi (n : ℕ) : (∫ y, F n y) =
      8 * C * ((1 / 2 : ℝ) ^ n * mean u x ((2 : ℝ) ^ n * ε)) := by
    rw [show (∫ y, F n y) = coeff C ε n * ∫ y in closedBall x ((2 : ℝ) ^ n * ε), u y by
      dsimp [F]; rw [integral_indicator measurableSet_closedBall, integral_const_mul]]
    exact coeff_integral u x C hε n
  calc
    (∫⁻ y, ‖v y‖ₑ) ≤ ∫⁻ y, ∑' n, ENNReal.ofReal (F n y) := by
      apply lintegral_mono
      intro y
      obtain ⟨n, hn, hnc⟩ := exists_coeff_bound hC hε (abs_nonneg (x - y))
      have hym : y ∈ closedBall x ((2 : ℝ) ^ n * ε) := by
        simpa only [mem_closedBall, Real.dist_eq, abs_sub_comm] using hn
      apply le_trans _ (ENNReal.le_tsum n)
      dsimp only
      rw [Real.enorm_eq_ofReal_abs]
      apply ENNReal.ofReal_le_ofReal
      change |v y| ≤ (closedBall x _).indicator _ y
      rw [indicator_of_mem hym]
      exact (hv y).trans (mul_le_mul_of_nonneg_right hnc (hu y))
    _ = ∑' n, ∫⁻ y, ENNReal.ofReal (F n y) := by
      exact lintegral_tsum (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    _ = ∑' n, ENNReal.ofReal (8 * C * ((1 / 2 : ℝ) ^ n *
        mean u x ((2 : ℝ) ^ n * ε))) := by
      congr 1
      funext n
      rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Eventually.of_forall (hFn n)), hFi]
    _ = ENNReal.ofReal (8 * C * dyadicMean u x ε) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by
        exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (mean_nonneg hu x (by positivity))))
        ((summable_dyadicMean hu hε hM).mul_left (8 * C)), tsum_mul_left]
      rfl

theorem integral_decay_tendsto_zero {u : ℝ → ℝ} {x C M : ℝ} {v : ℝ → ℝ → ℝ}
    (hu : ∀ y, 0 ≤ u y) (hi : LocallyIntegrable u volume) (hC : 0 ≤ C)
    (hM : ∀ r > 0, mean u x r ≤ M)
    (hlim : Tendsto (mean u x) (𝓝[>] 0) (𝓝 0))
    (hv : ∀ ε > 0, ∀ y, ‖v ε y‖ ≤
      (if |x - y| ≤ ε then C / ε else C * ε / |x - y| ^ 2) * u y) :
    Tendsto (fun ε => ∫ y, v ε y) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun ε => 8 * C * dyadicMean u x ε)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    have hb := (enorm_integral_le_lintegral_enorm (v ε)).trans
      (lintegral_decay_bound hu hi hC hε hM (hv ε hε))
    rw [Real.enorm_eq_ofReal_abs] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
      (tsum_nonneg fun n => mul_nonneg (by positivity) (mean_nonneg hu x (by positivity))))).mp hb
  · simpa using (dyadicMean_tendsto_zero hu hM hlim).const_mul (8 * C)

theorem exists_bound_mean {u g : ℝ → ℝ} {x A : ℝ}
    (hi : LocallyIntegrable u volume) (hg : Integrable g volume) (hgn : ∀ y, 0 ≤ g y)
    (hug : ∀ y, u y ≤ A + g y)
    (hlim : Tendsto (mean u x) (𝓝[>] 0) (𝓝 0)) :
    ∃ M : ℝ, ∀ r > 0, mean u x r ≤ M := by
  obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim 1 zero_lt_one
  refine ⟨max 1 (A + (∫ y, g y) / (2 * δ)), ?_⟩
  intro r hr
  by_cases hrd : r < δ
  · apply le_trans _ (le_max_left _ _)
    have hh := hd hr (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hrd)
    exact (le_abs_self _).trans (by simpa only [Real.dist_eq, sub_zero] using hh.le)
  · apply le_trans _ (le_max_right _ _)
    have hball := hi.integrableOn_isCompact (isCompact_closedBall x r)
    have hc : IntegrableOn (fun _ : ℝ => A) (closedBall x r) volume :=
      integrableOn_const (measure_closedBall_lt_top.ne)
    have hb : (∫ y in closedBall x r, u y) ≤ A * (2 * r) + ∫ y, g y := by
      calc
        _ ≤ ∫ y in closedBall x r, A + g y :=
          integral_mono hball (hc.add hg.integrableOn) hug
        _ = A * (2 * r) + ∫ y in closedBall x r, g y := by
          rw [integral_add hc hg.integrableOn, integral_const]
          simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_closedBall,
            ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r), smul_eq_mul, mul_comm A]
        _ ≤ _ := by
          exact add_le_add le_rfl (setIntegral_le_integral hg (Eventually.of_forall hgn))
    calc
      mean u x r ≤ A + (∫ y, g y) / (2 * r) := by
        rw [mean, ← div_eq_inv_mul]
        apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
        rw [add_mul, div_mul_cancel₀ _ (by positivity : 2 * r ≠ 0)]
        exact hb
      _ ≤ A + (∫ y, g y) / (2 * δ) := by
        gcongr
        · exact integral_nonneg hgn
        · exact le_of_not_gt hrd

/-- Almost every point of an Lp function has vanishing local oscillation and
globally bounded averages of that oscillation. -/
theorem ae_mean_norm_sub {p : ℝ≥0∞} {f : ℝ → ℝ} (hf : MemLp f p volume)
    (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    ∀ᵐ x ∂volume,
      Tendsto (mean (fun y => ‖f y - f x‖) x) (𝓝[>] 0) (𝓝 0) ∧
      ∃ M : ℝ, ∀ r > 0, mean (fun y => ‖f y - f x‖) x r ≤ M := by
  have hloc := hf.locallyIntegrable hp
  filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average_norm_sub hloc] with x hx
  have ht : Tendsto (mean (fun y => ‖f y - f x‖) x) (𝓝[>] 0) (𝓝 0) := by
    apply (hx.comp (Besicovitch.tendsto_filterAt volume x)).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (mean_eq_average _ x (show 0 ≤ r from le_of_lt hr)).symm
  refine ⟨ht, ?_⟩
  have hu : LocallyIntegrable (fun y => ‖f y - f x‖) volume := by
    rw [← locallyIntegrableOn_univ]
    exact ((hloc.sub (locallyIntegrable_const (f x))).locallyIntegrableOn univ).norm
  apply exists_bound_mean hu (hf.integrable_norm_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt)
    (fun y => Real.rpow_nonneg (norm_nonneg _) _) (A := 1 + ‖f x‖) _ ht
  intro y
  have hpower : ‖f y‖ ≤ 1 + ‖f y‖ ^ p.toReal := by
    by_cases hy : ‖f y‖ ≤ 1
    · exact hy.trans (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
    · have hp' : (1 : ℝ) ≤ p.toReal := by
        exact_mod_cast (ENNReal.toReal_mono hpt hp)
      exact (Real.self_le_rpow_of_one_le (le_of_not_ge hy) hp').trans
        (le_add_of_nonneg_left zero_le_one)
  exact (norm_sub_le _ _).trans (by linarith)

end HilbertUMD.LebesgueDecayApproximation
