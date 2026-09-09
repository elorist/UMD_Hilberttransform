import HilbertUMD.Analysis.ScalarThreeNorming
import HilbertUMD.Analysis.CubicLp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.InnerProductSpace.NormPow

/-! Scalar real L³ dual representation, proved by minimizing the cubic energy. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace HilbertUMD.ScalarLpDualRepresentation

private theorem exists_minimum_of_cubic_gap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : E → ℝ) (hF : Continuous F)
    (hb : BddBelow (range F))
    (hgap : ∀ x y, ‖x - y‖ ^ 3 ≤ 4 * (F x + F y - 2 * F ((2 : ℝ)⁻¹ • (x + y)))) :
    ∃ x, ∀ y, F x ≤ F y := by
  obtain ⟨v, _, ht, hv⟩ := exists_seq_tendsto_sInf (range_nonempty F) hb
  choose u hu using hv
  have ht' : Tendsto (fun n => F (u n)) atTop (𝓝 (sInf (range F))) := by
    simpa only [hu] using ht
  have hlo (x : E) : sInf (range F) ≤ F x := csInf_le hb (mem_range_self x)
  have hc : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have he : 0 < ε ^ 3 / 8 := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (ht'.eventually (gt_mem_nhds (show sInf (range F) < sInf (range F) + ε ^ 3 / 8 by linarith)))
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hg := hgap (u m) (u n)
    have hl := hlo ((2 : ℝ)⁻¹ • (u m + u n))
    have hm' := hN m hm
    have hn' := hN n hn
    have hp : ‖u m - u n‖ ^ 3 < ε ^ 3 := by linarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le (by norm_num : (3 : ℕ) ≠ 0)).mp hp
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  have heq : F x = sInf (range F) := tendsto_nhds_unique (hF.tendsto x |>.comp hx) ht'
  exact ⟨x, fun y => heq ▸ hlo y⟩

private theorem clarkson_cube (a b : ℝ) :
    |a + b| ^ 3 + |a - b| ^ 3 ≤ 4 * (|a| ^ 3 + |b| ^ 3) := by
  have h (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a) :
      (a + b) ^ 3 + (a - b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
    nlinarith [mul_nonneg (sq_nonneg (a - b)) (by linarith : 0 ≤ a + 2 * b)]
  have h' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      |a + b| ^ 3 + |a - b| ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
    rw [abs_of_nonneg (add_nonneg ha hb)]
    rcases le_total b a with hab | hab
    · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      exact h a b ha hb hab
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      nlinarith [h b a hb ha hab]
  have hp := h' |a| |b| (abs_nonneg _) (abs_nonneg _)
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · simpa only [abs_of_nonneg ha, abs_of_nonneg hb] using hp
  · simpa only [abs_of_nonneg ha, abs_of_nonpos hb, sub_neg_eq_add,
      ← sub_eq_add_neg, add_comm] using hp
  · have e1 : -a + b = -(a - b) := by ring
    have e2 : -a - b = -(a + b) := by ring
    rw [abs_of_nonpos ha, abs_of_nonneg hb, e1, e2, abs_neg, abs_neg] at hp
    rw [abs_of_nonpos ha, abs_of_nonneg hb]
    linarith
  · simpa only [abs_of_nonpos ha, abs_of_nonpos hb, ← neg_add, abs_neg,
      neg_sub_neg, abs_sub_comm] using hp

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

private theorem norm_cube (f : Lp ℝ 3 μ) :
    ‖f‖ ^ 3 = ∫ x, ‖f x‖ ^ 3 ∂μ :=
  (ScalarThreeNorming.integral_norm_cube μ (Lp.memLp f)).symm

private theorem lp_clarkson_cube (f g : Lp ℝ 3 μ) :
    ‖f + g‖ ^ 3 + ‖f - g‖ ^ 3 ≤ 4 * (‖f‖ ^ 3 + ‖g‖ ^ 3) := by
  simp only [norm_cube]
  rw [← integral_add ((Lp.memLp (f + g)).integrable_norm_pow (by norm_num))
    ((Lp.memLp (f - g)).integrable_norm_pow (by norm_num)),
    ← integral_add ((Lp.memLp f).integrable_norm_pow (by norm_num))
      ((Lp.memLp g).integrable_norm_pow (by norm_num)), ← integral_const_mul]
  apply integral_mono_ae
  · exact ((Lp.memLp (f + g)).integrable_norm_pow (by norm_num)).add
      ((Lp.memLp (f - g)).integrable_norm_pow (by norm_num))
  · exact (((Lp.memLp f).integrable_norm_pow (by norm_num)).add
      ((Lp.memLp g).integrable_norm_pow (by norm_num))).const_mul 4
  · filter_upwards [Lp.coeFn_add f g, Lp.coeFn_sub f g] with x ha hs
    simpa only [ha, hs, Pi.add_apply, Pi.sub_apply, Real.norm_eq_abs] using clarkson_cube (f x) (g x)

private theorem exists_cubic_minimum (ℓ : StrongDual ℝ (Lp ℝ 3 μ)) :
    ∃ f : Lp ℝ 3 μ, ∀ g, ‖f‖ ^ 3 - ℓ f ≤ ‖g‖ ^ 3 - ℓ g := by
  apply exists_minimum_of_cubic_gap (fun f => ‖f‖ ^ 3 - ℓ f) (by fun_prop)
  · refine ⟨-(‖ℓ‖ + 1) ^ 2, ?_⟩
    rintro _ ⟨f, rfl⟩
    have hl : ℓ f ≤ ‖ℓ‖ * ‖f‖ := (le_abs_self _).trans (ℓ.le_opNorm f)
    have hn := norm_nonneg f
    have hc := norm_nonneg ℓ
    by_cases hf : ‖f‖ ≤ ‖ℓ‖ + 1
    · have hp := pow_nonneg hn 3
      nlinarith [mul_le_mul_of_nonneg_left hf hc]
    · have hh : 1 ≤ ‖f‖ := by linarith
      have hs : ‖ℓ‖ ≤ ‖f‖ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hs hn, sq_nonneg (‖ℓ‖ + 1)]
  · intro f g
    have h := lp_clarkson_cube μ f g
    simp only [norm_smul, Real.norm_eq_abs, map_smul, map_add, smul_eq_mul]
    norm_num
    nlinarith

private theorem hasDerivAt_cube (a b t : ℝ) :
    HasDerivAt (fun t : ℝ => ‖a + t * b‖ ^ 3)
      (3 * ‖a + t * b‖ * (a + t * b) * b) t := by
  convert! (hasDerivAt_norm_rpow (a + t * b) (p := 3) (by norm_num)).comp t
    (((hasDerivAt_id t).mul_const b).const_add a) using 1 <;>
    norm_num [Function.comp_def]

private theorem hasDerivAt_integral_cube (f g : Lp ℝ 3 μ) :
    HasDerivAt (fun t : ℝ => ∫ x, ‖f x + t * g x‖ ^ 3 ∂μ)
      (∫ x, 3 * ‖f x‖ * f x * g x ∂μ) 0 := by
  let B : S → ℝ := fun x => 3 * (‖f x‖ + ‖g x‖) ^ 3
  have hB : Integrable B μ :=
    (((Lp.memLp f).norm.add (Lp.memLp g).norm).integrable_norm_pow
      (by norm_num : (3 : ℕ) ≠ 0)).congr
      (Eventually.of_forall (fun x => by
        simp only [Pi.add_apply,
          Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))])) |>.const_mul 3
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun t x => ‖f x + t * g x‖ ^ 3)
    (F' := fun t x => 3 * ‖f x + t * g x‖ * (f x + t * g x) * g x)
    (bound := B) (s := Metric.ball 0 1) (x₀ := 0)
    (Metric.ball_mem_nhds _ (by norm_num))
    (Eventually.of_forall (fun t => ((Lp.memLp f).1.add ((Lp.memLp g).1.const_mul t)).norm.pow 3))
    (by simpa using (Lp.memLp f).integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0))
    (by simpa only [zero_mul, add_zero, Pi.mul_apply] using!
      (((Lp.memLp f).1.norm.const_mul 3).mul (Lp.memLp f).1).mul (Lp.memLp g).1)
    ?_ hB (Eventually.of_forall (fun x t _ => hasDerivAt_cube (f x) (g x) t))
  · simpa only [zero_mul, add_zero] using hd.2
  · filter_upwards with x
    intro t ht
    have ht' : ‖t‖ ≤ 1 := (by simpa only [Metric.mem_ball, dist_zero_right] using ht : ‖t‖ < 1).le
    have hfg : ‖f x + t * g x‖ ≤ ‖f x‖ + ‖g x‖ := by
      calc
        _ ≤ ‖f x‖ + ‖t * g x‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_mul]; nlinarith [norm_nonneg (g x)]
    simp only [norm_mul, norm_norm]
    norm_num only [Real.norm_ofNat]
    dsimp [B]
    have hg : ‖g x‖ ≤ ‖f x‖ + ‖g x‖ := by linarith [norm_nonneg (f x)]
    simp only [Real.norm_eq_abs] at hfg hg ⊢
    calc
      _ ≤ 3 * (|f x| + |g x|) * (|f x| + |g x|) * (|f x| + |g x|) := by gcongr
      _ = _ := by ring

/-- Every real functional on L³ is integration against an L(3/2) function.
Only the scalar exponent needed for the finite-coordinate construction is proved. -/
theorem exists_representation (ℓ : StrongDual ℝ (Lp ℝ 3 μ)) :
    ∃ w : Lp ℝ (3 / 2) μ, ∀ g : Lp ℝ 3 μ, ℓ g = ∫ x, g x * w x ∂μ := by
  obtain ⟨f, hf⟩ := exists_cubic_minimum μ ℓ
  have hw := (ScalarThreeNorming.powerTest_mem_three_halves μ (Lp.memLp f)).const_mul 3
  refine ⟨hw.toLp _, fun g => ?_⟩
  have hn (t : ℝ) : ‖f + t • g‖ ^ 3 = ∫ x, ‖f x + t * g x‖ ^ 3 ∂μ := by
    rw [norm_cube]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f (t • g), Lp.coeFn_smul t g] with x ha hs
    simp only [ha, hs, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hmin : IsLocalMin
      (fun t : ℝ => (∫ x, ‖f x + t * g x‖ ^ 3 ∂μ) - (ℓ f + t * ℓ g)) 0 := by
    apply Eventually.of_forall
    intro t
    simp only [zero_mul, add_zero]
    rw [← norm_cube, ← hn]
    simpa only [map_add, map_smul, smul_eq_mul] using hf (f + t • g)
  have hd := hmin.hasDerivAt_eq_zero ((hasDerivAt_integral_cube μ f g).sub
    (((hasDerivAt_id 0).mul_const (ℓ g)).const_add (ℓ f)))
  have he : ℓ g = ∫ x, 3 * ‖f x‖ * f x * g x ∂μ := by
    simpa using (sub_eq_zero.mp hd).symm
  rw [he]
  apply integral_congr_ae
  filter_upwards [hw.coeFn_toLp] with x hx
  rw [hx]
  simp only [ScalarThreeNorming.powerTest, Real.norm_eq_abs]
  ring

end HilbertUMD.ScalarLpDualRepresentation
