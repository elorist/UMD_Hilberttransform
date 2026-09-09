import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Scalar L3 membership from bounded dual pairings on L2 intersect L(3/2).
The proof uses explicit bounded truncations, power tests and Fatou's lemma.
No prior L3 membership or sigma-finiteness assumption is required. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace HilbertUMD.ScalarThreeNorming

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

def truncate (h : S → ℝ) (N : ℝ) : S → ℝ := {x | ‖h x‖ ≤ N}.indicator h

def powerTest (f : S → ℝ) (x : S) : ℝ := f x * |f x|

omit [MeasurableSpace S] in
theorem norm_powerTest (f : S → ℝ) (x : S) : ‖powerTest f x‖ = ‖f x‖ ^ 2 := by
  simp [powerTest, Real.norm_eq_abs, pow_two]

omit [MeasurableSpace S] in
theorem self_pair_powerTest (f : S → ℝ) (x : S) :
    f x * powerTest f x = ‖f x‖ ^ 3 := by
  simp only [powerTest, Real.norm_eq_abs]
  calc
    _ = (f x) ^ 2 * |f x| := by ring
    _ = |f x| ^ 2 * |f x| := by rw [sq_abs]
    _ = _ := by ring

theorem powerTest_eLpNorm (f : S → ℝ) :
    eLpNorm (powerTest f) (3 / 2) μ = (eLpNorm f 3 μ) ^ 2 := by
  calc
    _ = eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) (3 / 2) μ := by
      apply eLpNorm_congr_norm_ae
      filter_upwards with x
      rw [norm_powerTest, Real.rpow_two]
      exact (Real.norm_of_nonneg (sq_nonneg ‖f x‖)).symm
    _ = _ := by
      rw [eLpNorm_norm_rpow _ (by norm_num)]
      norm_num [ENNReal.rpow_two]
      congr 2
      exact ENNReal.div_mul_cancel (by norm_num) (by simp)

theorem integral_norm_cube {f : S → ℝ} (hf : MemLp f 3 μ) :
    (∫ x, ‖f x‖ ^ 3 ∂μ) = (eLpNorm f 3 μ).toReal ^ 3 := by
  have hn : (eLpNorm f 3 μ).toReal =
      (∫ x, ‖f x‖ ^ (3 : ℝ) ∂μ) ^ (3 : ℝ)⁻¹ := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
  rw [hn]
  have hp := Real.rpow_inv_rpow (integral_nonneg (μ := μ)
    (fun x => show 0 ≤ ‖f x‖ ^ (3 : ℝ) by positivity)) (by norm_num : (3 : ℝ) ≠ 0)
  simpa only [Real.rpow_ofNat] using hp.symm

theorem bounded_two_mem_three {f : S → ℝ} (hf : MemLp f 2 μ) {N : ℝ}
    (_hN : 0 ≤ N) (hbound : ∀ x, ‖f x‖ ≤ N) : MemLp f 3 μ := by
  have hcube : Integrable (fun x => ‖f x‖ ^ 3) μ := by
    apply ((hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul N).mono'
      (hf.1.norm.pow 3)
    filter_upwards with x
    change ‖‖f x‖ ^ 3‖ ≤ N * ‖f x‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := mul_le_mul_of_nonneg_right (hbound x) (sq_nonneg ‖f x‖)
    nlinarith
  apply (integrable_norm_rpow_iff hf.1 (p := 3) (by norm_num) (by norm_num)).mp
  simpa using hcube

theorem powerTest_mem_two {f : S → ℝ} (hf : MemLp f 2 μ) {N : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ N) : MemLp (powerTest f) 2 μ := by
  apply hf.of_le_mul (c := N) (hf.1.mul hf.1.norm)
  filter_upwards with x
  change ‖powerTest f x‖ ≤ N * ‖f x‖
  rw [norm_powerTest]
  have h := mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg (f x))
  nlinarith

theorem powerTest_mem_three_halves {f : S → ℝ} (hf : MemLp f 3 μ) :
    MemLp (powerTest f) (3 / 2) μ := by
  refine ⟨hf.1.mul hf.1.norm, ?_⟩
  rw [powerTest_eLpNorm]
  exact ENNReal.pow_lt_top hf.2

theorem measurable_truncate {h : S → ℝ} (hh : Measurable h) (N : ℝ) :
    Measurable (truncate h N) :=
  hh.indicator (measurableSet_le hh.norm measurable_const)

theorem truncate_mem_two {h : S → ℝ} (hh : Measurable h) (h2 : MemLp h 2 μ) (N : ℝ) :
    MemLp (truncate h N) 2 μ :=
  h2.indicator (measurableSet_le hh.norm measurable_const)

omit [MeasurableSpace S] in
theorem norm_truncate_le {h : S → ℝ} {N : ℝ} (hN : 0 ≤ N) (x : S) :
    ‖truncate h N x‖ ≤ N := by
  by_cases hx : ‖h x‖ ≤ N
  · rw [truncate, Set.indicator_of_mem (show x ∈ {y | ‖h y‖ ≤ N} from hx)]
    exact hx
  · rw [truncate, Set.indicator_of_notMem (show x ∉ {y | ‖h y‖ ≤ N} from hx), norm_zero]
    exact hN

omit [MeasurableSpace S] in
theorem pairing_truncate (h : S → ℝ) (N : ℝ) (x : S) :
    h x * powerTest (truncate h N) x = ‖truncate h N x‖ ^ 3 := by
  by_cases hx : ‖h x‖ ≤ N
  · have ht : truncate h N x = h x :=
      Set.indicator_of_mem (show x ∈ {y | ‖h y‖ ≤ N} from hx) h
    simpa only [powerTest, ht] using self_pair_powerTest h x
  · have ht : truncate h N x = 0 :=
      Set.indicator_of_notMem (show x ∉ {y | ‖h y‖ ≤ N} from hx) h
    simp [powerTest, ht]

theorem truncate_three_bound {h : S → ℝ} (hh : Measurable h) (h2 : MemLp h 2 μ)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ g : S → ℝ, MemLp g 2 μ → MemLp g (3 / 2) μ →
      |∫ x, h x * g x ∂μ| ≤ M * (eLpNorm g (3 / 2) μ).toReal)
    (N : ℝ) (hN : 0 ≤ N) : eLpNorm (truncate h N) 3 μ ≤ ENNReal.ofReal M := by
  let f := truncate h N
  have hf2 : MemLp f 2 μ := truncate_mem_two μ hh h2 N
  have hfb : ∀ x, ‖f x‖ ≤ N := norm_truncate_le hN
  have hf3 : MemLp f 3 μ := bounded_two_mem_three μ hf2 hN hfb
  have ht2 := powerTest_mem_two μ hf2 hfb
  have htq := powerTest_mem_three_halves μ hf3
  have hb := hbound (powerTest f) ht2 htq
  have hpair : (∫ x, h x * powerTest f x ∂μ) = (eLpNorm f 3 μ).toReal ^ 3 := by
    rw [← integral_norm_cube μ hf3]
    apply integral_congr_ae
    exact Eventually.of_forall (pairing_truncate h N)
  rw [hpair, abs_of_nonneg (by positivity), powerTest_eLpNorm, ENNReal.toReal_pow] at hb
  have hle : (eLpNorm f 3 μ).toReal ≤ M := by
    by_cases hz : (eLpNorm f 3 μ).toReal = 0
    · simpa [hz] using hM
    · by_contra hn
      have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) (sq_pos_of_ne_zero hz)
      nlinarith
  rw [← ENNReal.ofReal_toReal hf3.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hle

theorem memLp_three_of_pairing_measurable {h : S → ℝ} (hh : Measurable h)
    (h2 : MemLp h 2 μ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ g : S → ℝ, MemLp g 2 μ → MemLp g (3 / 2) μ →
      |∫ x, h x * g x ∂μ| ≤ M * (eLpNorm g (3 / 2) μ).toReal) :
    MemLp h 3 μ ∧ eLpNorm h 3 μ ≤ ENNReal.ofReal M := by
  have hn : eLpNorm h 3 μ ≤ ENNReal.ofReal M := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun n : ℕ => truncate h n)
      (Eventually.of_forall fun n => truncate_three_bound μ hh h2 hM hbound n (Nat.cast_nonneg n))
      (fun n => (measurable_truncate hh n).aestronglyMeasurable)
    apply Eventually.of_forall
    intro x
    have hev : ∀ᶠ n : ℕ in atTop, ‖h x‖ ≤ (n : ℝ) := by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖h x‖
      exact eventually_atTop.mpr ⟨N, fun n hn => hN.trans (by exact_mod_cast hn)⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    exact (Set.indicator_of_mem (show x ∈ {y | ‖h y‖ ≤ (n : ℝ)} from hn) h).symm
  exact ⟨⟨hh.aestronglyMeasurable, hn.trans_lt ENNReal.ofReal_lt_top⟩, hn⟩

/-- Bounded integral tests against L2 intersect L(3/2) force both L3
membership and the exact L3 bound. This holds for every measure. -/
theorem memLp_three_of_pairing {h : S → ℝ} (hh : MemLp h 2 μ)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ g : S → ℝ, MemLp g 2 μ → MemLp g (3 / 2) μ →
      |∫ x, h x * g x ∂μ| ≤ M * (eLpNorm g (3 / 2) μ).toReal) :
    MemLp h 3 μ ∧ eLpNorm h 3 μ ≤ ENNReal.ofReal M := by
  let h' := hh.1.mk h
  have he : h =ᵐ[μ] h' := hh.1.ae_eq_mk
  have hm : Measurable h' := hh.1.stronglyMeasurable_mk.measurable
  have h2 : MemLp h' 2 μ := hh.ae_eq he
  have hb : ∀ g : S → ℝ, MemLp g 2 μ → MemLp g (3 / 2) μ →
      |∫ x, h' x * g x ∂μ| ≤ M * (eLpNorm g (3 / 2) μ).toReal := by
    intro g hg2 hgq
    have hi : (∫ x, h' x * g x ∂μ) = ∫ x, h x * g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    rw [hi]
    exact hbound g hg2 hgq
  obtain ⟨h3, hb3⟩ := memLp_three_of_pairing_measurable μ hm h2 hM hb
  exact ⟨h3.ae_eq he.symm, (eLpNorm_congr_ae he).le.trans hb3⟩

end HilbertUMD.ScalarThreeNorming
