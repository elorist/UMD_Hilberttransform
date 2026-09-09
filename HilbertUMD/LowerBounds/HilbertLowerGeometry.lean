import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! Geometric and logarithmic estimates for the summation Hilbert lower bound. -/

noncomputable section
open MeasureTheory Filter

namespace HilbertUMD

theorem uniform_cell_iff_floor_eq (N : ℕ) (hN : 0 < N) (j : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    ((j : ℝ) / (N : ℝ) ≤ t ∧ t < ((j : ℝ) + 1) / (N : ℝ)) ↔
      ⌊(N : ℝ) * t⌋₊ = j := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Nat.floor_eq_iff (mul_nonneg hNp.le ht), div_le_iff₀ hNp, lt_div_iff₀ hNp]
  simp only [mul_comm]

theorem floor_mul_lt_of_unit_interval (N : ℕ) (hN : 0 < N)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ⌊(N : ℝ) * t⌋₊ < N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  apply (Nat.floor_lt (mul_nonneg hNp.le ht.1)).mpr
  nlinarith [ht.2]

/-- Outside a countable null set, a real point is not an endpoint of the
uniform grid of mesh 1/N. -/
theorem ae_ne_uniform_endpoint (N : ℕ) :
    ∀ᵐ t : ℝ, ∀ i : ℕ, t ≠ (i : ℝ) / (N : ℝ) := by
  filter_upwards [(Set.countable_range (fun i : ℕ => (i : ℝ) / (N : ℝ))).ae_notMem volume]
    with t ht i hi
  exact ht ⟨i, hi.symm⟩

/-- The grid point immediately to the left lies in the matrix's range of
rows and is strictly less than one mesh width away. -/
theorem exists_uniform_left_endpoint (N : ℕ) (hN : 8 ≤ N) (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4))
    (hne : ∀ i : ℕ, t ≠ (i : ℝ) / (N : ℝ)) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧ 0 < t - (i : ℝ) / (N : ℝ) ∧
      t - (i : ℝ) / (N : ℝ) < 1 / (N : ℝ) := by
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  let i : ℕ := ⌊(N : ℝ) * t⌋₊
  have hi1 : 1 ≤ i := by
    apply Nat.le_floor
    norm_num only [Nat.cast_one]
    calc
      (1 : ℝ) ≤ (N : ℝ) * (1 / 4) := by linarith
      _ ≤ (N : ℝ) * t := mul_le_mul_of_nonneg_left ht.1 hNp.le
  have hiN : i ≤ N := Nat.floor_le_of_le (by nlinarith [ht.2])
  have hi_le : (i : ℝ) ≤ (N : ℝ) * t := Nat.floor_le (mul_nonneg hNp.le ht0)
  have hi_lt : (i : ℝ) < (N : ℝ) * t := by
    apply lt_of_le_of_ne hi_le
    intro heq
    apply hne i
    apply (eq_div_iff hNp.ne').mpr
    nlinarith
  have hi_upper : (N : ℝ) * t < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨i, hi1, hiN, sub_pos.mpr ((div_lt_iff₀ hNp).mpr (by nlinarith)), ?_⟩
  apply (lt_div_iff₀ hNp).mpr
  rw [sub_mul, div_mul_cancel₀ _ hNp.ne']
  nlinarith

theorem log_ratio_ge_log_quarter {N t d : ℝ} (hN : 0 < N)
    (ht : 1 / 4 ≤ t) (hd : 0 < d) (hdN : d < 1 / N) :
    Real.log (N / 4) ≤ Real.log (t / d) := by
  apply Real.log_le_log (by positivity)
  apply (le_div_iff₀ hd).mpr
  have hNd : d * N ≤ 1 := (le_div_iff₀ hN).mp hdN.le
  nlinarith

/-- The pointwise logarithmic estimate used on the middle half of [0,1]. -/
theorem exists_logarithmic_row (N : ℕ) (hN : 8 ≤ N) (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4))
    (hne : ∀ i : ℕ, t ≠ (i : ℝ) / (N : ℝ)) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧
      Real.log ((N : ℝ) / 4) ≤ Real.log (t / (t - (i : ℝ) / (N : ℝ))) := by
  obtain ⟨i, hi1, hiN, hd, hdN⟩ := exists_uniform_left_endpoint N hN t ht hne
  refine ⟨i, hi1, hiN, log_ratio_ge_log_quarter ?_ ht.1 hd hdN⟩
  have : 0 < N := by omega
  exact_mod_cast this

theorem log_dyadic_quarter (n : ℕ) :
    Real.log ((2 : ℝ) ^ n / 4) = ((n : ℝ) - 2) * Real.log 2 := by
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [h4]
  ring

theorem log_dyadic_quarter_linear_lower (n : ℕ) (hn : 3 ≤ n) :
    (((n : ℝ) + 1) / 4) * Real.log 2 ≤ Real.log ((2 : ℝ) ^ n / 4) := by
  rw [log_dyadic_quarter]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end HilbertUMD
