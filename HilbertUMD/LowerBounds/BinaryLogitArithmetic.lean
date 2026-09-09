import HilbertUMD.LowerBounds.BinaryLogitDefs

/-! Finite alternating-coefficient inequalities, independent of integration. -/

noncomputable section
open Finset

namespace HilbertUMD.BinaryLogit

def first : ℝ := 2 * Real.log 2 / Real.pi
def second : ℝ := 3 * Real.log (4 / 3) / Real.pi

theorem log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  exact h

theorem log_sixteen : Real.log 16 = 4 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 4
  norm_num at h
  exact h

theorem log_twentyseven : Real.log 27 = 3 * Real.log 3 := by
  have h := Real.log_pow (3 : ℝ) 3
  norm_num at h
  exact h

theorem log_thirtytwo : Real.log 32 = 5 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 5
  norm_num at h
  exact h

theorem delta_eq_twice_gap : delta = 2 * (first - second) := by
  simp only [delta, first, second, Real.log_div (by norm_num : (27 : ℝ) ≠ 0)
      (by norm_num : (16 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
    log_twentyseven, log_sixteen, log_four_eq]
  ring

theorem delta_le_first : delta ≤ first := by
  have h : 0 ≤ 2 / Real.pi * Real.log (32 / 27) :=
    mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le)
      (Real.log_nonneg (by norm_num))
  have he : first - delta = 2 / Real.pi * Real.log (32 / 27) := by
    rw [delta_eq_twice_gap]
    simp only [first, second,
      Real.log_div (by norm_num : (32 : ℝ) ≠ 0) (by norm_num : (27 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
      log_thirtytwo, log_twentyseven, log_four_eq]
    ring
  linarith

/-- The magnitude of the jth coefficient (using zero-based j). -/
def alternatingCoefficient (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  2 * (∑ k ∈ range j, (-1 : ℝ) ^ k * a k) + (-1 : ℝ) ^ j * a j

@[simp] theorem alternatingCoefficient_zero (a : ℕ → ℝ) :
    alternatingCoefficient a 0 = a 0 := by simp [alternatingCoefficient]

@[simp] theorem alternatingCoefficient_one (a : ℕ → ℝ) :
    alternatingCoefficient a 1 = 2 * a 0 - a 1 := by simp [alternatingCoefficient]; ring

theorem alternatingCoefficient_succ (a : ℕ → ℝ) (j : ℕ) :
    alternatingCoefficient a (j + 1) =
      alternatingCoefficient a j + (-1 : ℝ) ^ j * (a j - a (j + 1)) := by
  simp only [alternatingCoefficient, sum_range_succ, pow_succ]
  ring

theorem alternatingCoefficient_add_two (a : ℕ → ℝ) (j : ℕ) :
    alternatingCoefficient a (j + 2) =
      2 * (a 0 - a 1) + alternatingCoefficient (fun k => a (k + 2)) j := by
  rw [alternatingCoefficient, show j + 2 = 2 + j by omega, sum_range_add]
  simp only [sum_range_succ, sum_range_zero, pow_zero, one_mul, zero_add, pow_one,
    neg_one_mul, pow_add, neg_one_sq, one_mul, alternatingCoefficient]
  simp_rw [show ∀ k : ℕ, 2 + k = k + 2 by omega]
  ring

theorem alternatingCoefficient_nonneg (a : ℕ → ℝ) (ha : Antitone a)
    (h0 : ∀ k, 0 ≤ a k) (j : ℕ) : 0 ≤ alternatingCoefficient a j := by
  induction j using Nat.twoStepInduction generalizing a with
  | zero => simpa using h0 0
  | one =>
    rw [alternatingCoefficient_one]
    have h := ha (show 0 ≤ 1 by omega)
    linarith [h0 0]
  | more j ih₀ ih₁ =>
    rw [alternatingCoefficient_add_two]
    have h := ih₀ (fun k => a (k + 2))
      (fun i j hij => ha (Nat.add_le_add_right hij 2)) (fun k => h0 (k + 2))
    have h' := ha (show 0 ≤ 1 by omega)
    linarith

theorem delta_le_alternatingCoefficient (a : ℕ → ℝ) (ha : Antitone a)
    (h0 : ∀ k, 0 ≤ a k) (ha0 : a 0 = first) (ha1 : a 1 = second) (j : ℕ) :
    delta ≤ alternatingCoefficient a j := by
  cases j with
  | zero => simpa [ha0] using delta_le_first
  | succ j =>
    cases j with
    | zero =>
      rw [alternatingCoefficient_one, delta_eq_twice_gap, ← ha0, ← ha1]
      linarith [h0 1]
    | succ j =>
      rw [show j + 1 + 1 = j + 2 by omega, alternatingCoefficient_add_two,
        delta_eq_twice_gap, ← ha0, ← ha1]
      exact le_add_of_nonneg_right
        (alternatingCoefficient_nonneg (fun k => a (k + 2))
          (fun i j hij => ha (Nat.add_le_add_right hij 2)) (fun k => h0 (k + 2)) j)

/-- The exact coefficient identity forced by the binary recursion. -/
theorem binary_coefficient_recursion (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ)
    (hfirst : ∀ n, b (n + 1) 0 = (-1 : ℝ) ^ (n + 1) * a 0)
    (hstep : ∀ n j, b (n + 1) (j + 1) =
      b n j + (-1 : ℝ) ^ (n + 1) * (a (j + 1) - a j))
    (n j : ℕ) (hj : j < n) :
    b n j = (-1 : ℝ) ^ (n - j) * alternatingCoefficient a j := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simpa using hfirst n
    | succ j =>
      rw [hstep, ih j (by omega), Nat.add_sub_add_right, alternatingCoefficient_succ]
      have hp : (-1 : ℝ) ^ (n - j) * (-1 : ℝ) ^ j = (-1 : ℝ) ^ n := by
        rw [← pow_add, Nat.sub_add_cancel (show j ≤ n by omega)]
      rw [mul_add, ← mul_assoc, hp, pow_succ]
      ring

end HilbertUMD.BinaryLogit
