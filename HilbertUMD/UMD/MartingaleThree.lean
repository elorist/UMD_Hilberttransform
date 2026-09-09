import HilbertUMD.Analysis.MixedNorm
import HilbertUMD.UMD.MartingaleProducts
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The cubic Hilbert-valued dyadic martingale inequality

Burkholder's function at exponent three gives the constant two. The proof
uses a supporting-plane inequality and finite sums over the dyadic tree.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace
namespace HilbertUMD

private theorem cubic_support_algebra (a b A B p q r s : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hA : 0 ≤ A)
    (hx : A ^ 2 = a ^ 2 + 2 * p + r)
    (hy : B ^ 2 = b ^ 2 + 2 * q + s)
    (hrs : s ≤ r) (hs : (B - b) ^ 2 ≤ s) (hB : B - b ≤ A + a) :
    B ^ 3 - 3 * A ^ 2 * B - 2 * A ^ 3 ≤
      b ^ 3 - 3 * a ^ 2 * b - 2 * a ^ 3 - 6 * (a + b) * p +
        (3 * (b ^ 2 - a ^ 2) / b) * q := by
  have h₁ : (B - b - 2 * A - a) * (A - a + B - b) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have h₂ : 0 ≤ 3 * (a + b) * (r - s) := by positivity
  have h₃ : 0 ≤ (3 * (a + b) ^ 2 / (2 * b)) * (s - (B - b) ^ 2) := by
    positivity
  have hid :
      B ^ 3 - 3 * A ^ 2 * B - 2 * A ^ 3 -
        (b ^ 3 - 3 * a ^ 2 * b - 2 * a ^ 3 - 6 * (a + b) * p +
          (3 * (b ^ 2 - a ^ 2) / b) * q) =
      (B - b - 2 * A - a) * (A - a + B - b) ^ 2 -
        3 * (a + b) * (r - s) -
        (3 * (a + b) ^ 2 / (2 * b)) * (s - (B - b) ^ 2) := by
    field_simp
    linear_combination -6 * b * (a + b) * hx + 3 * (b ^ 2 - a ^ 2) * hy
  linarith

private theorem cubic_support_zero_algebra (a A B p r : ℝ)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : A ^ 2 = a ^ 2 + 2 * p + r)
    (hr : B ^ 2 ≤ r) (hBA : B ≤ A + a) :
    B ^ 3 - 3 * A ^ 2 * B - 2 * A ^ 3 ≤ -2 * a ^ 3 - 6 * a * p := by
  have h₁ : (B - 2 * A - a) * (A - a + B) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have h₂ : 0 ≤ 3 * a * (r - B ^ 2) := by positivity
  have h₃ : 0 ≤ 3 * a ^ 2 * B := by positivity
  nlinarith [show
    B ^ 3 - 3 * A ^ 2 * B - 2 * A ^ 3 + 2 * a ^ 3 + 6 * a * p =
      (B - 2 * A - a) * (A - a + B) ^ 2 - 3 * a * (r - B ^ 2) -
        3 * a ^ 2 * B by linear_combination -3 * a * hx]

section Hilbert
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The unnormalized cubic Burkholder function. -/
def cubicBurkholder (x : E) (y : F) : ℝ :=
  ‖y‖ ^ 3 - 3 * ‖x‖ ^ 2 * ‖y‖ - 2 * ‖x‖ ^ 3

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
theorem cubicBurkholder_majorizes (x : E) (y : F) :
    3 / 4 * (‖y‖ ^ 3 - 8 * ‖x‖ ^ 3) ≤ cubicBurkholder x y := by
  have h : 0 ≤ (‖y‖ - 2 * ‖x‖) ^ 2 * (‖y‖ + 4 * ‖x‖) := by positivity
  dsimp [cubicBurkholder]
  nlinarith

/-- A supporting plane in every direction with subordinate increments.
This includes the nonsmooth case `y = 0`, with the zero supporting vector. -/
theorem cubicBurkholder_support (x h : E) (y k : F) (hk : ‖k‖ ≤ ‖h‖) :
    cubicBurkholder (x + h) (y + k) ≤ cubicBurkholder x y -
      6 * (‖x‖ + ‖y‖) * ⟪x, h⟫_ℝ +
        (3 * (‖y‖ ^ 2 - ‖x‖ ^ 2) / ‖y‖) * ⟪y, k⟫_ℝ := by
  have hB : ‖y + k‖ - ‖y‖ ≤ ‖x + h‖ + ‖x‖ := by
    have hh : ‖h‖ ≤ ‖x + h‖ + ‖x‖ := by
      simpa using norm_sub_le (x + h) x
    linarith [norm_add_le y k]
  by_cases hy : y = 0
  · subst y
    simp only [cubicBurkholder, zero_add, norm_zero, inner_zero_left,
      zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 2 ≠ 0), mul_zero,
      sub_zero, zero_sub, add_zero, div_zero]
    simpa only [neg_mul] using cubic_support_zero_algebra _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_add_sq_real x h)
      (pow_le_pow_left₀ (norm_nonneg _) hk 2) (by simpa using hB)
  · apply cubic_support_algebra _ _ _ _ _ _ _ _ (norm_nonneg _)
      (norm_pos_iff.mpr hy) (norm_nonneg _) (norm_add_sq_real x h)
      (norm_add_sq_real y k) (pow_le_pow_left₀ (norm_nonneg _) hk 2) _ hB
    exact sq_le_sq.mpr
      (by simpa using abs_norm_sub_norm_le (y + k) y)

private theorem sum_inner_eq_zero_of_leafAverage_eq_zero (n t : ℕ)
    (u v : Leaf n → E)
    (hu : ∀ i j, j ∈ dyadicBlock n t i → u j = u i)
    (hv : ∀ i, leafAverage (𝕜 := ℝ) n t v i = 0) :
    ∑ i, ⟪u i, v i⟫_ℝ = 0 := by
  classical
  rw [← sum_leafAverage (𝕜 := ℝ) n t (fun i => ⟪u i, v i⟫_ℝ)]
  apply Finset.sum_eq_zero
  intro i _
  calc
    leafAverage (𝕜 := ℝ) n t (fun j => ⟪u j, v j⟫_ℝ) i =
        ⟪u i, leafAverage (𝕜 := ℝ) n t v i⟫_ℝ := by
      simp only [leafAverage, real_inner_smul_right, inner_sum, smul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [hu i j hj]
    _ = 0 := by rw [hv, inner_zero_right]

private theorem leafAverage_increment_zero (n t : ℕ) (f : Leaf n → E) (i : Leaf n) :
    leafAverage (𝕜 := ℝ) n t
      (fun j => leafAverage (𝕜 := ℝ) n (t + 1) f j - leafAverage (𝕜 := ℝ) n t f j) i = 0 := by
  have hsub (u v : Leaf n → E) :
      leafAverage (𝕜 := ℝ) n t (fun j => u j - v j) i =
        leafAverage (𝕜 := ℝ) n t u i - leafAverage (𝕜 := ℝ) n t v i := by
    simp only [leafAverage, Finset.sum_sub_distrib, smul_sub]
  rw [hsub, leafAverage_tower n t (t + 1) (by omega),
    leafAverage_tower n t t le_rfl, sub_self]

/-- One conditional averaging step decreases the expected Burkholder function. -/
theorem sum_cubicBurkholder_average_succ_le (n t : ℕ) (f : Leaf n → E) (g : Leaf n → F)
    (hsub : ∀ i,
      ‖leafAverage (𝕜 := ℝ) n (t + 1) g i - leafAverage (𝕜 := ℝ) n t g i‖ ≤
        ‖leafAverage (𝕜 := ℝ) n (t + 1) f i - leafAverage (𝕜 := ℝ) n t f i‖) :
    (∑ i, cubicBurkholder (leafAverage (𝕜 := ℝ) n (t + 1) f i)
      (leafAverage (𝕜 := ℝ) n (t + 1) g i)) ≤
        ∑ i, cubicBurkholder (leafAverage (𝕜 := ℝ) n t f i)
          (leafAverage (𝕜 := ℝ) n t g i) := by
  let X := leafAverage (𝕜 := ℝ) n t f
  let Y := leafAverage (𝕜 := ℝ) n t g
  let dX := fun i => leafAverage (𝕜 := ℝ) n (t + 1) f i - X i
  let dY := fun i => leafAverage (𝕜 := ℝ) n (t + 1) g i - Y i
  have hX : ∑ i, 6 * (‖X i‖ + ‖Y i‖) * ⟪X i, dX i⟫_ℝ = 0 := by
    simp_rw [← real_inner_smul_left]
    apply sum_inner_eq_zero_of_leafAverage_eq_zero n t
    · intro i j hj
      dsimp [X, Y]
      rw [leafAverage_eq_of_mem n t f i j hj, leafAverage_eq_of_mem n t g i j hj]
    · exact leafAverage_increment_zero n t f
  have hY : ∑ i, (3 * (‖Y i‖ ^ 2 - ‖X i‖ ^ 2) / ‖Y i‖) * ⟪Y i, dY i⟫_ℝ = 0 := by
    simp_rw [← real_inner_smul_left]
    apply sum_inner_eq_zero_of_leafAverage_eq_zero n t
    · intro i j hj
      dsimp [X, Y]
      rw [leafAverage_eq_of_mem n t f i j hj, leafAverage_eq_of_mem n t g i j hj]
    · exact leafAverage_increment_zero n t g
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    cubicBurkholder_support (X i) (dX i) (Y i) (dY i) (hsub i))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hX, hY,
    sub_zero, add_zero] at h
  simpa only [dX, dY, X, Y, add_sub_cancel] using h

/-- Finite Hilbert-valued differential subordination at exponent three. -/
theorem sum_norm_cubed_le_of_dyadic_subordination (n : ℕ)
    (f : Leaf n → E) (g : Leaf n → F)
    (hg : ∀ i, leafAverage (𝕜 := ℝ) n 0 g i = 0)
    (hsub : ∀ (t : Fin n) i,
      ‖leafAverage (𝕜 := ℝ) n (t.val + 1) g i - leafAverage (𝕜 := ℝ) n t.val g i‖ ≤
        ‖leafAverage (𝕜 := ℝ) n (t.val + 1) f i - leafAverage (𝕜 := ℝ) n t.val f i‖) :
    (∑ i, ‖g i‖ ^ 3) ≤ 8 * ∑ i, ‖f i‖ ^ 3 := by
  have h (t : ℕ) (ht : t ≤ n) :
      (∑ i, cubicBurkholder (leafAverage (𝕜 := ℝ) n t f i)
        (leafAverage (𝕜 := ℝ) n t g i)) ≤ 0 := by
    induction t with
    | zero =>
      apply Finset.sum_nonpos
      intro i _
      rw [hg]
      simp only [cubicBurkholder, norm_zero, zero_pow (by decide : 3 ≠ 0), mul_zero,
        sub_zero, zero_sub]
      exact neg_nonpos.mpr (by positivity)
    | succ t ih =>
      exact (sum_cubicBurkholder_average_succ_le n t f g (hsub ⟨t, by omega⟩)).trans
        (ih (by omega))
  have hterminal := h n le_rfl
  simp only [leafAverage_terminal] at hterminal
  have hmajor := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    cubicBurkholder_majorizes (f i) (g i))
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at hmajor
  linarith

end Hilbert

section Norms
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem lpNorm_leafUniform_three_cubed (n : ℕ) (f : Leaf n → E) :
    lpNorm f 3 (leafUniform n) ^ 3 = ((2 : ℝ) ^ n)⁻¹ * ∑ i, ‖f i‖ ^ 3 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (leaf_memLp n 3 f).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_natCast]
  have hpos : 0 ≤ ∫ x, ‖f x‖ ^ 3 ∂leafUniform n := integral_nonneg (fun _ => by positivity)
  calc
    _ = ∫ x, ‖f x‖ ^ 3 ∂leafUniform n := by
      convert Real.rpow_inv_natCast_pow hpos (by decide : (3 : ℕ) ≠ 0) using 1; norm_num
    _ = _ := integral_leafUniform n _

theorem eLpNorm_three_le_of_sum_norm_cubed_le (n : ℕ) (f : Leaf n → E) (g : Leaf n → F)
    (h : (∑ i, ‖g i‖ ^ 3) ≤ 8 * ∑ i, ‖f i‖ ^ 3) :
    eLpNorm g 3 (leafUniform n) ≤ 2 * eLpNorm f 3 (leafUniform n) := by
  have hcube : lpNorm g 3 (leafUniform n) ^ 3 ≤ (2 * lpNorm f 3 (leafUniform n)) ^ 3 := by
    rw [mul_pow, lpNorm_leafUniform_three_cubed, lpNorm_leafUniform_three_cubed]
    have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ ((2 : ℝ) ^ n)⁻¹)
    nlinarith
  have hnorm : lpNorm g 3 (leafUniform n) ≤ 2 * lpNorm f 3 (leafUniform n) :=
    (pow_le_pow_iff_left₀ lpNorm_nonneg (mul_nonneg (by norm_num) lpNorm_nonneg)
      (by decide : 3 ≠ 0)).mp hcube
  rw [← ofReal_lpNorm (leaf_memLp n 3 g), ← ofReal_lpNorm (leaf_memLp n 3 f)]
  calc
    _ ≤ ENNReal.ofReal (2 * lpNorm f 3 (leafUniform n)) := ENNReal.ofReal_le_ofReal hnorm
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

end Norms

/-- The dimension-free Hilbert-valued dyadic L3 inequality, for two possibly
different real Hilbert spaces and pointwise subordinate martingale increments. -/
theorem eLpNorm_three_le_of_dyadic_subordination {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (n : ℕ) (f : Leaf n → E) (g : Leaf n → F)
    (hg : ∀ i, leafAverage (𝕜 := ℝ) n 0 g i = 0)
    (hsub : ∀ (t : Fin n) i,
      ‖leafAverage (𝕜 := ℝ) n (t.val + 1) g i - leafAverage (𝕜 := ℝ) n t.val g i‖ ≤
        ‖leafAverage (𝕜 := ℝ) n (t.val + 1) f i - leafAverage (𝕜 := ℝ) n t.val f i‖) :
    eLpNorm g 3 (leafUniform n) ≤ 2 * eLpNorm f 3 (leafUniform n) :=
  eLpNorm_three_le_of_sum_norm_cubed_le n f g
    (sum_norm_cubed_le_of_dyadic_subordination n f g hg hsub)

section Coordinates
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem leafAverage_toLp_two (n t : ℕ) (f : Leaf n → ι → ℝ) (i : Leaf n) :
    leafAverage (𝕜 := ℝ) n t (fun j => (WithLp.toLp 2 (f j) : EuclideanSpace ℝ ι)) i =
      WithLp.toLp 2 (fun a => leafAverage (𝕜 := ℝ) n t (fun j => f j a) i) := by
  apply WithLp.ofLp_injective
  ext a
  simp [leafAverage, WithLp.ofLp_sum, Finset.sum_apply]

/-- Deterministic real scalar contractions acting on finite Hilbert coordinates. -/
theorem dyadic_hilbert_transform_three
    (n : ℕ) (ε : Fin n → ℝ) (hε : ∀ k, |ε k| ≤ 1) (f : Leaf n → ι → ℝ) :
    mixedNorm 3 2 (leafUniform n) (fun x j => dyadicScalar n ε (fun y => f y j) x) ≤
      2 * mixedNorm 3 2 (leafUniform n) f := by
  apply eLpNorm_three_le_of_dyadic_subordination
  · intro i
    rw [leafAverage_toLp_two]
    simp only [leafAverage_dyadicScalar_zero]
    exact WithLp.toLp_zero 2
  · intro t i
    simp only [leafAverage_toLp_two, ← WithLp.toLp_sub]
    have heq :
        (fun a => leafAverage (𝕜 := ℝ) n (t.val + 1)
          (fun j => dyadicScalar n ε (fun y => f y a) j) i) -
            (fun a => leafAverage (𝕜 := ℝ) n t.val
              (fun j => dyadicScalar n ε (fun y => f y a) j) i) =
        ε t • ((fun a => leafAverage (𝕜 := ℝ) n (t.val + 1) (fun j => f j a) i) -
          (fun a => leafAverage (𝕜 := ℝ) n t.val (fun j => f j a) i)) := by
      ext a
      exact dyadicDifference_dyadicScalar n ε (fun y => f y a) t i
    rw [heq, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hε t) (norm_nonneg _)).trans_eq (one_mul _)

end Coordinates
end HilbertUMD
