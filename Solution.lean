module

public import HilbertUMD.MainTheorem

/-! The proved counterpart of Challenge.lean. This module imports the complete
proof development and never imports the independent statement module. -/

@[expose] public section

namespace HilbertUMD
universe uΩ

/-- Theorem 1.1, simultaneously over the real and complex fields, with the
full UMD constant over sample spaces in any chosen universe. -/
theorem Comparison.theorem_1_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Paper.Theorem11Bounds.{uΩ} ℝ n c C ∧ Paper.Theorem11Bounds.{uΩ} ℂ n c C :=
  HilbertUMD.theorem_1_1

end HilbertUMD
