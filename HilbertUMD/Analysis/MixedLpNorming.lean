import HilbertUMD.Analysis.CubicLp

/-! Explicit finite-coordinate norming tests for Bochner Lp spaces. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace HilbertUMD.CubicLp

/-- Choose the first maximizing coordinate in a fixed enumeration, and put a
sign of modulus one there. Choosing the first occurrence makes ties measurable. -/
theorem exists_measurable_norming_vector {ι : Type*} [Fintype ι] [Nonempty ι] :
    ∃ u : (ι → ℝ) → (ι → ℝ), Measurable u ∧
      ∀ v, (∑ i, |u v i|) = 1 ∧ (∑ i, v i * u v i) = ‖v‖ := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  have hex (v : ι → ℝ) : ∃ n, ‖v (e n)‖ = ‖v‖ := by
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm v).1
    obtain ⟨n, rfl⟩ := he i
    exact ⟨n, hi⟩
  let u (n : ℕ) (v : ι → ℝ) : ι → ℝ :=
    Pi.single (e n) (if 0 ≤ v (e n) then 1 else -1)
  refine ⟨fun v => u (Nat.find (hex v)) v, ?_, ?_⟩
  · apply Measurable.find
    · intro n
      apply measurable_pi_iff.mpr
      intro i
      by_cases hi : i = e n
      · subst i
        simpa [u] using
          (measurable_const.ite (measurableSet_le measurable_const (measurable_pi_apply (e n)))
            measurable_const : Measurable (fun v : ι → ℝ => if 0 ≤ v (e n) then (1 : ℝ) else -1))
      · simp [u, hi]
    · intro n
      exact measurableSet_eq_fun (measurable_pi_apply (e n)).norm measurable_norm
  · intro v
    have hmax := Nat.find_spec (hex v)
    dsimp [u]
    constructor
    · rw [Finset.sum_eq_single (e (Nat.find (hex v)))]
      · simp only [Pi.single_eq_same]
        split <;> norm_num
      · intro i _ hi
        simp [hi]
      · simp
    · rw [Finset.sum_eq_single (e (Nat.find (hex v)))]
      · simp only [Pi.single_eq_same]
        split_ifs with hsign
        · simpa [Real.norm_eq_abs, abs_of_nonneg hsign] using hmax
        · simpa [Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hsign)] using hmax
      · intro i _ hi
        simp [hi]
      · simp

/-- The unnormalized maximizing-coordinate test has exactly the expected
Lq(l1) norm and pairing. -/
theorem exists_power_norming_test {S ι : Type*} [MeasurableSpace S]
    [Fintype ι] [Nonempty ι] (μ : Measure S)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 1 < p) (hp' : p < ⊤) (hq : 1 < q) (hq' : q < ⊤)
    [ENNReal.HolderTriple p q 1] (w : Space (ι := ι) μ p) :
    ∃ g : Space (ι := ι) μ q,
      l1Norm μ q g = ‖w‖ ^ (p.toReal - 1) ∧
      (∫ x, ∑ i, w x i * g x i ∂μ) = ‖w‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans hp)
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans hq)
  have hpr : 1 < p.toReal := by
    exact_mod_cast (ENNReal.toReal_lt_toReal (by simp) hp'.ne).mpr hp
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq'.ne
  have hr : 0 < p.toReal - 1 := sub_pos.mpr hpr
  have hc : p.toReal⁻¹ + q.toReal⁻¹ = 1 := by
    have hc := congrArg ENNReal.toReal
      (ENNReal.HolderConjugate.inv_add_inv_eq_one p q)
    simpa [ENNReal.toReal_add, hp0, hq0] using hc
  have hmul : q.toReal * (p.toReal - 1) = p.toReal := by
    field_simp [ne_of_gt (zero_lt_one.trans hpr), hqr.ne'] at hc
    nlinarith
  have hexp : q * ENNReal.ofReal (p.toReal - 1) = p := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) hp'.ne).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.le]
    exact hmul
  let a : S → ℝ := fun x => ‖w x‖ ^ (p.toReal - 1)
  have ha : MemLp a q μ := by
    refine ⟨((Lp.memLp w).1.norm.aemeasurable.pow_const _).aestronglyMeasurable, ?_⟩
    dsimp [a]
    rw [eLpNorm_norm_rpow _ hr, hexp]
    exact ENNReal.rpow_lt_top_of_nonneg hr.le (Lp.memLp w).2.ne
  have ha0 (x : S) : 0 ≤ a x := Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨u, hu, hu_norm⟩ := exists_measurable_norming_vector (ι := ι)
  let g : S → ι → ℝ := fun x i => a x * u (w x) i
  have hg_sum (x : S) : (∑ i, |g x i|) = a x := by
    simp only [g, abs_mul, abs_of_nonneg (ha0 x), ← Finset.mul_sum,
      (hu_norm (w x)).1, mul_one]
  have hg_pair (x : S) : (∑ i, w x i * g x i) = ‖w x‖ ^ p.toReal := by
    calc
      _ = a x * ∑ i, w x i * u (w x) i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [g]
        ring
      _ = a x * ‖w x‖ := by rw [(hu_norm (w x)).2]
      _ = _ := by
        dsimp [a]
        rw [← Real.rpow_add_one' (norm_nonneg _) (by linarith : p.toReal - 1 + 1 ≠ 0)]
        congr 1
        ring
  have hg : MemLp g q μ := by
    apply memLp_pi_iff.mpr
    intro i
    apply ha.of_le
    · exact (ha.1.aemeasurable.mul
        ((measurable_pi_apply i).comp hu |>.comp_aemeasurable
          (Lp.memLp w).1.aemeasurable)).aestronglyMeasurable
    · filter_upwards with x
      change |g x i| ≤ |a x|
      rw [abs_of_nonneg (ha0 x), ← hg_sum x]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (g x j)) (Finset.mem_univ i)
  refine ⟨hg.toLp g, ?_, ?_⟩
  · rw [l1Norm_apply, Lp.norm_def]
    have he : eLpNorm ((toL1 (ι := ι)).compLpL q μ (hg.toLp g)) q μ =
        eLpNorm a q μ := by
      apply eLpNorm_congr_norm_ae
      filter_upwards [(toL1 (ι := ι)).coeFn_compLpL (hg.toLp g), hg.coeFn_toLp] with x hx hxg
      rw [hx, hxg, norm_toL1, hg_sum, Real.norm_eq_abs, abs_of_nonneg (ha0 x)]
    rw [he]
    dsimp [a]
    rw [eLpNorm_norm_rpow _ hr, hexp, ← ENNReal.toReal_rpow, Lp.norm_def]
  · calc
      _ = ∫ x, ‖w x‖ ^ p.toReal ∂μ := by
        apply integral_congr_ae
        filter_upwards [hg.coeFn_toLp] with x hx
        rw [hx, hg_pair]
      _ = _ := by
        have hn : ‖w‖ = (∫ x, ‖w x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
          rw [Lp.norm_def, (Lp.memLp w).eLpNorm_eq_integral_rpow_norm hp0 hp'.ne,
            ENNReal.toReal_ofReal (by positivity)]
        rw [hn, Real.rpow_inv_rpow (integral_nonneg (fun x => by positivity))
          (ne_of_gt (zero_lt_one.trans hpr))]

/-- Normalize the explicit power test to obtain an exact unit norming test. -/
theorem exists_l1_unit_norming_test {S ι : Type*} [MeasurableSpace S]
    [Fintype ι] [Nonempty ι] (μ : Measure S)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 1 < p) (hp' : p < ⊤) (hq : 1 < q) (hq' : q < ⊤)
    [ENNReal.HolderTriple p q 1] (w : Space (ι := ι) μ p) (hw : w ≠ 0) :
    ∃ g : Space (ι := ι) μ q, l1Norm μ q g = 1 ∧
      (∫ x, ∑ i, w x i * g x i ∂μ) = ‖w‖ := by
  obtain ⟨g, hg_norm, hg_pair⟩ := exists_power_norming_test μ hp hp' hq hq' w
  have hpow : 0 < ‖w‖ ^ (p.toReal - 1) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hw) _
  let c : ℝ := (‖w‖ ^ (p.toReal - 1))⁻¹
  refine ⟨c • g, ?_, ?_⟩
  · rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpow), hg_norm]
    exact inv_mul_cancel₀ hpow.ne'
  · calc
      _ = c * ∫ x, ∑ i, w x i * g x i ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c g] with x hx
        rw [hx, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = ‖w‖ := by
        rw [hg_pair]
        have he : ‖w‖ ^ p.toReal = ‖w‖ ^ (p.toReal - 1) * ‖w‖ := by
          simpa only [sub_add_cancel] using
            Real.rpow_add_one (norm_ne_zero_iff.mpr hw) (p.toReal - 1)
        rw [he, ← mul_assoc]
        exact (congrArg (fun t : ℝ => t * ‖w‖) (inv_mul_cancel₀ hpow.ne')).trans (one_mul _)

/-- Lp(l∞) is normed by the integral pairings with the Lq(l1) unit ball.
This construction works for every measure, without sigma-finiteness. -/
theorem norm_le_of_l1_unit_tests {S ι : Type*} [MeasurableSpace S]
    [Fintype ι] (μ : Measure S)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 1 < p) (hp' : p < ⊤) (hq : 1 < q) (hq' : q < ⊤)
    [ENNReal.HolderTriple p q 1]
    (w : Space (ι := ι) μ p) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ g : Space (ι := ι) μ q, l1Norm μ q g ≤ 1 →
      |∫ x, ∑ i, w x i * g x i ∂μ| ≤ M) : ‖w‖ ≤ M := by
  by_cases hw : w = 0
  · simpa [hw] using hM
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    exfalso
    apply hw
    apply Lp.ext
    filter_upwards with x
    exact Subsingleton.elim _ _
  | inr hi =>
    obtain ⟨g, hg_norm, hg_pair⟩ := exists_l1_unit_norming_test μ hp hp' hq hq' w hw
    simpa [hg_pair, abs_of_nonneg (norm_nonneg w)] using h g hg_norm.le

end HilbertUMD.CubicLp
