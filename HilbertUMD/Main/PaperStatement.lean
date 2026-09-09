import HilbertUMD.Main.Statement
import HilbertUMD.UMD.UniverseIndependence

/-! The notation and literal depth dependence of Theorem 1.1 in the fixed
9 September 2026 paper. The abbreviations below use the existing spaces and
operator constants; they introduce no new mathematical definitions. -/

noncomputable section
open scoped ENNReal
namespace HilbertUMD.Paper

universe uΩ vΩ

/-- The paper's first family, indexed by the same depth n. -/
abbrev X (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := XSpace 𝕜 n

/-- The paper's second family, indexed by the same depth n. -/
abbrev Y (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := YSpace 𝕜 n

/-- The paper's Hilbert constant hbar_{p,E}, over the displayed scalar field. -/
abbrev hbar (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] : ℝ≥0∞ :=
  hilbertConstant p (ContinuousLinearMap.id 𝕜 E)

/-- The paper's UMD constant beta_{p,E}, with sample spaces in universe uΩ.
At p=2, its value is independent of that universe. -/
abbrev beta (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] : ℝ≥0∞ :=
  umdConstant.{uΩ} p (ContinuousLinearMap.id 𝕜 E)

theorem finrank_X (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    Module.finrank 𝕜 (X 𝕜 n) = 2 ^ n := by
  change Module.finrank 𝕜 (Leaf n → 𝕜) = _
  rw [Module.finrank_pi, card_leaf]

theorem finrank_Y (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    Module.finrank 𝕜 (Y 𝕜 n) = 2 ^ n := by
  change Module.finrank 𝕜 (Leaf n → 𝕜) = _
  rw [Module.finrank_pi, card_leaf]

/-- The dimensions and all eight inequalities of Theorem 1.1, using n and
sqrt(n) exactly as in the paper. The spaces are Banach spaces by their existing
normed-space and completeness instances. Constants c and C are universal in
the public theorem; this statement does not prescribe Remark 1.2's numbers. -/
structure Theorem11Bounds (𝕜 : Type*) [RCLike 𝕜] (n : ℕ)
    [NormedSpace ℝ (X 𝕜 n)] [NormedSpace ℝ (Y 𝕜 n)] (c C : ℝ) : Prop where
  x_dimension : Module.finrank 𝕜 (X 𝕜 n) = 2 ^ n
  y_dimension : Module.finrank 𝕜 (Y 𝕜 n) = 2 ^ n
  x_hilbert_lower : ENNReal.ofReal (c * (n : ℝ)) ≤ hbar 𝕜 2 (X 𝕜 n)
  x_hilbert_upper : hbar 𝕜 2 (X 𝕜 n) ≤ ENNReal.ofReal (C * (n : ℝ))
  x_umd_lower : ENNReal.ofReal (c * Real.sqrt (n : ℝ)) ≤ beta.{uΩ} 𝕜 2 (X 𝕜 n)
  x_umd_upper : beta.{uΩ} 𝕜 2 (X 𝕜 n) ≤ ENNReal.ofReal (C * Real.sqrt (n : ℝ))
  y_umd_lower : ENNReal.ofReal (c * (n : ℝ)) ≤ beta.{uΩ} 𝕜 2 (Y 𝕜 n)
  y_umd_upper : beta.{uΩ} 𝕜 2 (Y 𝕜 n) ≤ ENNReal.ofReal (C * (n : ℝ))
  y_hilbert_lower : ENNReal.ofReal (c * Real.sqrt (n : ℝ)) ≤ hbar 𝕜 2 (Y 𝕜 n)
  y_hilbert_upper : hbar 𝕜 2 (Y 𝕜 n) ≤ ENNReal.ofReal (C * Real.sqrt (n : ℝ))

/-- All paper bounds hold with the identical comparison constants in any
sample-space universe. -/
theorem Theorem11Bounds.changeUniverse {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    [NormedSpace ℝ (X 𝕜 n)] [NormedSpace ℝ (Y 𝕜 n)]
    [IsScalarTower ℝ 𝕜 (X 𝕜 n)] [IsScalarTower ℝ 𝕜 (Y 𝕜 n)]
    {c C : ℝ} (h : Theorem11Bounds.{uΩ} 𝕜 n c C) :
    Theorem11Bounds.{vΩ} 𝕜 n c C := by
  have hx : beta.{vΩ} 𝕜 2 (X 𝕜 n) = beta.{uΩ} 𝕜 2 (X 𝕜 n) :=
    umdConstant_two_universe_eq _
  have hy : beta.{vΩ} 𝕜 2 (Y 𝕜 n) = beta.{uΩ} 𝕜 2 (Y 𝕜 n) :=
    umdConstant_two_universe_eq _
  exact {
    x_dimension := h.x_dimension
    y_dimension := h.y_dimension
    x_hilbert_lower := h.x_hilbert_lower
    x_hilbert_upper := h.x_hilbert_upper
    x_umd_lower := by rw [hx]; exact h.x_umd_lower
    x_umd_upper := by rw [hx]; exact h.x_umd_upper
    y_umd_lower := by rw [hy]; exact h.y_umd_lower
    y_umd_upper := by rw [hy]; exact h.y_umd_upper
    y_hilbert_lower := h.y_hilbert_lower
    y_hilbert_upper := h.y_hilbert_upper }

/-- Convert the internal n+1 bounds to the paper's n bounds without changing
the depth or the spaces. A common upper coefficient 2C works for all fields. -/
theorem theorem11Bounds_of_p2 {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    [NormedSpace ℝ (X 𝕜 n)] [NormedSpace ℝ (Y 𝕜 n)]
    {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hn : 1 ≤ n)
    (h : P2MainBounds 𝕜 n c C) : Theorem11Bounds.{0} 𝕜 n c (2 * C) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlinear : C * ((n : ℝ) + 1) ≤ (2 * C) * (n : ℝ) := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hn')]
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)]
  have hupper := mul_le_mul_of_nonneg_left hsqrt hC
  have hlower := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)) hc
  have hlinlower : c * (n : ℝ) ≤ c * ((n : ℝ) + 1) := by nlinarith
  exact {
    x_dimension := finrank_X 𝕜 n
    y_dimension := finrank_Y 𝕜 n
    x_hilbert_lower := (ENNReal.ofReal_le_ofReal hlinlower).trans h.x_hilbert_lower
    x_hilbert_upper := h.x_hilbert_upper.trans (ENNReal.ofReal_le_ofReal hlinear)
    x_umd_lower := (ENNReal.ofReal_le_ofReal hlower).trans h.x_umd_lower
    x_umd_upper := h.x_umd_upper.trans (ENNReal.ofReal_le_ofReal (by nlinarith [hupper]))
    y_umd_lower := (ENNReal.ofReal_le_ofReal hlinlower).trans h.y_umd_lower
    y_umd_upper := h.y_umd_upper.trans (ENNReal.ofReal_le_ofReal hlinear)
    y_hilbert_lower := (ENNReal.ofReal_le_ofReal hlower).trans h.y_hilbert_lower
    y_hilbert_upper := h.y_hilbert_upper.trans (ENNReal.ofReal_le_ofReal (by nlinarith [hupper])) }

end HilbertUMD.Paper
