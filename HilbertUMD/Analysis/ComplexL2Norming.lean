import HilbertUMD.Analysis.CubicComplex
import Mathlib.MeasureTheory.Function.Holder

/-!
# Finite-coordinate complex L² norming

The bilinear pairing with L²(l¹) norms L²(l∞). Only exponent two is
needed for the interpolation step; no abstract dual representation is used.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Classical

namespace HilbertUMD.ComplexL2Norming

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]

def dotLinear : (ι → ℂ) →ₗ[ℂ] PiLp 1 (fun _ : ι => ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => ∑ i, x i * y i)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [mul_assoc, Finset.mul_sum])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp [mul_left_comm, Finset.mul_sum])

theorem dot_bound (x : ι → ℂ) (y : PiLp 1 (fun _ : ι => ℂ)) :
    ‖dotLinear x y‖ ≤ 1 * ‖x‖ * ‖y‖ := by
  rw [one_mul, PiLp.norm_eq_of_L1, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)

def dot : (ι → ℂ) →L[ℂ] PiLp 1 (fun _ : ι => ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂ dotLinear 1 dot_bound

@[simp] theorem dot_apply (x : ι → ℂ) (y : PiLp 1 (fun _ : ι => ℂ)) :
    dot x y = ∑ i, x i * y i := rfl

theorem dot_norm_le : ‖dot (ι := ι)‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ (by norm_num) _

def pairing (μ : Measure S) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderTriple p q 1] :
    Lp (ι → ℂ) p μ →L[ℂ] Lp (PiLp 1 (fun _ : ι => ℂ)) q μ →L[ℂ] ℂ :=
  (dot (ι := ι)).lpPairing μ p q

theorem pairing_apply (μ : Measure S) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderTriple p q 1]
    (f : Lp (ι → ℂ) p μ) (g : Lp (PiLp 1 (fun _ : ι => ℂ)) q μ) :
    pairing μ p q f g = ∫ x, ∑ i, f x i * g x i ∂μ :=
  ContinuousLinearMap.lpPairing_eq_integral (dot (ι := ι)) f g

theorem pairing_bound (μ : Measure S) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderTriple p q 1]
    (f : Lp (ι → ℂ) p μ) (g : Lp (PiLp 1 (fun _ : ι => ℂ)) q μ) :
    ‖pairing μ p q f g‖ ≤ ‖f‖ * ‖g‖ := by
  calc
    _ ≤ ‖(dot (ι := ι)).holder 1 f g‖ := by
      change ‖L1.integralCLM' ℂ ((dot (ι := ι)).holder 1 f g)‖ ≤ _
      rw [← L1.integral_eq']
      exact L1.norm_integral_le ((dot (ι := ι)).holder 1 f g)
    _ ≤ ‖dot (ι := ι)‖ * ‖f‖ * ‖g‖ := ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ 1 * ‖f‖ * ‖g‖ := by gcongr; exact dot_norm_le
    _ = _ := by rw [one_mul]

/-- A measurable maximizing coordinate, with the conjugate value in that coordinate. -/
theorem exists_measurable_norming_vector [Nonempty ι] :
    ∃ u : (ι → ℂ) → (ι → ℂ), Measurable u ∧
      ∀ v, (∑ i, ‖u v i‖) = ‖v‖ ∧
        (∑ i, v i * u v i) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  have hex (v : ι → ℂ) : ∃ n, ‖v (e n)‖ = ‖v‖ := by
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm v).1
    obtain ⟨n, rfl⟩ := he i
    exact ⟨n, hi⟩
  let u (n : ℕ) (v : ι → ℂ) : ι → ℂ := Pi.single (e n) (star (v (e n)))
  refine ⟨fun v => u (Nat.find (hex v)) v, ?_, ?_⟩
  · apply Measurable.find
    · intro n
      apply measurable_pi_iff.mpr
      intro i
      by_cases hi : i = e n
      · subst i
        simpa [u, Function.comp_def] using
          (Complex.continuous_conj.comp (continuous_apply (e n))).measurable
      · simp [u, hi]
    · intro n
      exact measurableSet_eq_fun (measurable_pi_apply (e n)).norm measurable_norm
  · intro v
    have hmax := Nat.find_spec (hex v)
    constructor
    · rw [Finset.sum_eq_single (e (Nat.find (hex v)))]
      · simpa [u] using hmax
      · intro i _ hi
        simp [u, hi]
      · simp
    · rw [Finset.sum_eq_single (e (Nat.find (hex v)))]
      · simp [u, Complex.mul_conj, Complex.normSq_eq_norm_sq, hmax]
      · intro i _ hi
        simp [u, hi]
      · simp

theorem exists_norming_test (μ : Measure S) [Nonempty ι] (w : Lp (ι → ℂ) 2 μ) :
    ∃ g : Lp (PiLp 1 (fun _ : ι => ℂ)) 2 μ,
      ‖g‖ = ‖w‖ ∧ pairing μ 2 2 w g = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨u, hu, hun⟩ := exists_measurable_norming_vector (ι := ι)
  let g : S → PiLp 1 (fun _ : ι => ℂ) := fun x => CubicLp.complexToL1 (u (w x))
  have hgn (x : S) : ‖g x‖ = ‖w x‖ := by
    rw [CubicLp.norm_complexToL1, (hun (w x)).1]
  have hg : MemLp g 2 μ := (Lp.memLp w).of_le
    ((CubicLp.complexToL1 (ι := ι)).continuous.comp_aestronglyMeasurable
      (hu.comp_aemeasurable (Lp.memLp w).1.aemeasurable).aestronglyMeasurable)
    (Eventually.of_forall (fun x => (hgn x).le))
  refine ⟨hg.toLp g, ?_, ?_⟩
  · rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, hgn]
  · rw [pairing_apply]
    calc
      _ = ∫ x, ((‖w x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hg.coeFn_toLp] with x hx
        rw [hx]
        exact (hun (w x)).2
      _ = ((∫ x, ‖w x‖ ^ 2 ∂μ : ℝ) : ℂ) := integral_ofReal
      _ = _ := by
        congr 1
        have hn : ‖w‖ = Real.sqrt (∫ x, ‖w x‖ ^ 2 ∂μ) := by
          rw [Lp.norm_def, (Lp.memLp w).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
            ENNReal.toReal_ofReal (by positivity)]
          norm_num [Real.sqrt_eq_rpow]
        rw [hn, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))]

theorem norm_le_of_pairing_bound (μ : Measure S) (w : Lp (ι → ℂ) 2 μ)
    (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ g : Lp (PiLp 1 (fun _ : ι => ℂ)) 2 μ, ‖pairing μ 2 2 w g‖ ≤ K * ‖g‖) :
    ‖w‖ ≤ K := by
  by_cases hw : w = 0
  · simpa [hw] using hK
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    exfalso
    apply hw
    apply Lp.ext
    filter_upwards with x
    exact Subsingleton.elim _ _
  | inr hi =>
    obtain ⟨g, hgn, hgp⟩ := exists_norming_test μ w
    have hh := h g
    rw [hgn, hgp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hh
    nlinarith [norm_pos_iff.mpr hw]

end HilbertUMD.ComplexL2Norming
