import HilbertUMD.UMD.MartingaleThree

/-! Finite square-function estimates obtained from the cubic Hilbert inequality. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace HilbertUMD

theorem dyadic_hilbert_square_three {ι : Type*} [Fintype ι]
    (n : ℕ) (f : Leaf n → ι → ℝ) :
    mixedNorm 3 2 (leafUniform n) (fun x j => dyadicSquareFunction n (fun y => f y j) x) ≤
      2 * mixedNorm 3 2 (leafUniform n) f := by
  classical
  let F (x : Leaf n) : EuclideanSpace ℝ ι := WithLp.toLp 2 (f x)
  let G (x : Leaf n) : EuclideanSpace ℝ (Fin n × ι) :=
    WithLp.toLp 2 (fun a => dyadicDifference n a.1 (fun y => f y a.2) x)
  have hG (t : ℕ) (x : Leaf n) :
      leafAverage (𝕜 := ℝ) n t G x = WithLp.toLp 2
        (fun a => if a.1.val < t then dyadicDifference n a.1 (fun y => f y a.2) x else 0) := by
    rw [leafAverage_toLp_two]
    simp only [leafAverage_dyadicDifference]
  have h := eLpNorm_three_le_of_dyadic_subordination n F G (by
    intro x
    rw [hG]
    simp only [Nat.not_lt_zero, ↓reduceIte]
    exact WithLp.toLp_zero 2) (by
    intro t x
    rw [hG, hG]
    simp only [F, leafAverage_toLp_two, ← WithLp.toLp_sub]
    have heq :
        ((fun a : Fin n × ι => if a.1.val < t.val + 1 then
          dyadicDifference n a.1 (fun y => f y a.2) x else 0) -
        (fun a : Fin n × ι => if a.1.val < t.val then
          dyadicDifference n a.1 (fun y => f y a.2) x else 0)) =
        (fun a => if a.1 = t then dyadicDifference n t (fun y => f y a.2) x else 0) := by
      funext a
      simp only [Pi.sub_apply]
      by_cases ha : a.1 = t
      · simp [ha]
      · have hv : a.1.val ≠ t.val := fun h => ha (Fin.ext h)
        by_cases hl : a.1.val < t.val <;> simp [ha, hl, show
          (a.1.val < t.val + 1) ↔ (a.1.val < t.val) by omega]
    rw [heq]
    simp only [PiLp.norm_eq_of_L2, Fintype.sum_prod_type]
    simp [dyadicDifference, Pi.sub_apply])
  have heq : mixedNorm 3 2 (leafUniform n)
      (fun x j => dyadicSquareFunction n (fun y => f y j) x) =
      eLpNorm G 3 (leafUniform n) := by
    rw [mixedNorm_two, ← eLpNorm_norm G]
    congr 1
    funext x
    simp only [G, PiLp.norm_eq_of_L2, Real.norm_of_nonneg (dyadicSquareFunction_nonneg _ _ _),
      dyadicSquareFunction_sq, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_comm]
  rw [heq]
  exact h

theorem eLpNorm_dyadicSquareFunction_three (n : ℕ) (f : Leaf n → ℝ) :
    eLpNorm (dyadicSquareFunction n f) 3 (leafUniform n) ≤
      2 * eLpNorm f 3 (leafUniform n) := by
  have h := dyadic_hilbert_square_three (ι := Fin 1) n (fun x _ => f x)
  simpa only [mixedNorm_two, Fin.sum_univ_one, Real.sqrt_sq_eq_abs, abs_norm,
    eLpNorm_norm] using h

theorem dyadicDifference_self (n : ℕ) (k : Fin n) (f : Leaf n → ℝ) :
    dyadicDifference n k (dyadicDifference n k f) = dyadicDifference n k f := by
  funext x
  change leafAverage (𝕜 := ℝ) n (k.val + 1) (dyadicDifference n k f) x -
    leafAverage (𝕜 := ℝ) n k.val (dyadicDifference n k f) x = _
  simp [leafAverage_dyadicDifference]

theorem sum_dyadicDifference (n : ℕ) (f : Leaf n → ℝ) (x : Leaf n) :
    ∑ k : Fin n, dyadicDifference n k f x = f x - leafAverage (𝕜 := ℝ) n 0 f x := by
  simp only [dyadicDifference, Pi.sub_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => leafAverage (𝕜 := ℝ) n (k + 1) f x -
    leafAverage (𝕜 := ℝ) n k f x),
    Finset.sum_range_sub (fun k => leafAverage (𝕜 := ℝ) n k f x)]
  simp

theorem sum_mul_eq_sum_dyadicDifference (n : ℕ) (f g : Leaf n → ℝ)
    (hf : ∀ x, leafAverage (𝕜 := ℝ) n 0 f x = 0) :
    ∑ x, f x * g x = ∑ x, ∑ k : Fin n,
      dyadicDifference n k f x * dyadicDifference n k g x := by
  have h (k : Fin n) : (∑ x, dyadicDifference n k f x * dyadicDifference n k g x) =
      ∑ x, dyadicDifference n k f x * g x := by
    rw [sum_mul_dyadicDifference, dyadicDifference_self]
  rw [Finset.sum_comm]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_mul, sum_dyadicDifference, hf, sub_zero]

theorem integral_mul_le_square (n : ℕ) (f g : Leaf n → ℝ)
    (hf : ∀ x, leafAverage (𝕜 := ℝ) n 0 f x = 0) :
    (∫ x, f x * g x ∂leafUniform n) ≤
      ∫ x, dyadicSquareFunction n f x * dyadicSquareFunction n g x ∂leafUniform n := by
  rw [integral_leafUniform, integral_leafUniform, sum_mul_eq_sum_dyadicDifference n f g hf]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro x _
  simp only [dyadicSquareFunction_eq_sqrt]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem leaf_holder_threeHalves_three (n : ℕ) (f g : Leaf n → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    (∫ x, f x * g x ∂leafUniform n) ≤
      lpNorm f (3 / 2) (leafUniform n) * lpNorm g 3 (leafUniform n) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := leafUniform n) (p := 3 / 2) (q := 3)
    (by constructor <;> norm_num) (Filter.Eventually.of_forall hf)
    (Filter.Eventually.of_forall hg) (leaf_memLp n _ f) (leaf_memLp n _ g)
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by finiteness)
      (leaf_memLp n (3 / 2) f).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (leaf_memLp n 3 g).aestronglyMeasurable]
  simpa [Real.norm_of_nonneg (hf _), Real.norm_of_nonneg (hg _)] using h

/-- The scalar reverse square-function estimate at the dual exponent.
The square-root norming test makes the duality argument entirely finite. -/
theorem eLpNorm_le_two_square_threeHalves (n : ℕ) (f : Leaf n → ℝ)
    (hf : ∀ x, leafAverage (𝕜 := ℝ) n 0 f x = 0) :
    eLpNorm f (3 / 2) (leafUniform n) ≤
      2 * eLpNorm (dyadicSquareFunction n f) (3 / 2) (leafUniform n) := by
  let g (x : Leaf n) := (if 0 ≤ f x then (1 : ℝ) else -1) * Real.sqrt |f x|
  have hg (x : Leaf n) : ‖g x‖ = Real.sqrt |f x| := by
    dsimp [g]
    split_ifs <;> simp
  have hsq (x : Leaf n) : ‖g x‖ ^ (2 : ℝ) = ‖f x‖ := by
    rw [Real.rpow_two, hg, Real.sq_sqrt (abs_nonneg _), Real.norm_eq_abs]
  have hnorm : lpNorm f (3 / 2) (leafUniform n) = lpNorm g 3 (leafUniform n) ^ 2 := by
    have h := eLpNorm_norm_rpow (μ := leafUniform n) (p := 3 / 2) g (by norm_num : (0 : ℝ) < 2)
    simp only [hsq, eLpNorm_norm] at h
    norm_num only [ENNReal.ofReal_ofNat, ENNReal.div_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by simp : (2 : ℝ≥0∞) ≠ ∞), ENNReal.rpow_two] at h
    have hr := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_pow, toReal_eLpNorm (leaf_memLp n (3 / 2) f).aestronglyMeasurable,
      toReal_eLpNorm (leaf_memLp n 3 g).aestronglyMeasurable] using hr
  have hpair : (∫ x, f x * g x ∂leafUniform n) = lpNorm g 3 (leafUniform n) ^ 3 := by
    rw [lpNorm_leafUniform_three_cubed, integral_leafUniform]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [hg]
    have hs := Real.sq_sqrt (abs_nonneg (f x))
    dsimp [g]
    split_ifs with hx
    · rw [abs_of_nonneg hx] at hs ⊢
      nlinarith [congrArg (fun a => a * Real.sqrt (f x)) hs]
    · rw [abs_of_neg (lt_of_not_ge hx)] at hs ⊢
      nlinarith [congrArg (fun a => a * Real.sqrt (-f x)) hs]
  have hsquare : lpNorm (dyadicSquareFunction n g) 3 (leafUniform n) ≤
      2 * lpNorm g 3 (leafUniform n) := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (leaf_memLp n 3 g).2.ne)
      (eLpNorm_dyadicSquareFunction_three n g)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      toReal_eLpNorm (leaf_memLp n 3 g).aestronglyMeasurable,
      toReal_eLpNorm (leaf_memLp n 3 (dyadicSquareFunction n g)).aestronglyMeasurable] using h
  have hp := (integral_mul_le_square n f g hf).trans
    (leaf_holder_threeHalves_three n _ _ (dyadicSquareFunction_nonneg n f)
      (dyadicSquareFunction_nonneg n g))
  rw [hpair] at hp
  have hp' := hp.trans (mul_le_mul_of_nonneg_left hsquare lpNorm_nonneg)
  have hn : lpNorm f (3 / 2) (leafUniform n) ≤
      2 * lpNorm (dyadicSquareFunction n f) (3 / 2) (leafUniform n) := by
    rw [hnorm]
    by_cases hz : lpNorm g 3 (leafUniform n) = 0
    · rw [hz, zero_pow (by decide : 2 ≠ 0)]; exact mul_nonneg (by norm_num) lpNorm_nonneg
    · have hpos : 0 < lpNorm g 3 (leafUniform n) := lt_of_le_of_ne lpNorm_nonneg (Ne.symm hz)
      nlinarith
  rw [← ofReal_lpNorm (leaf_memLp n _ f), ← ofReal_lpNorm (leaf_memLp n _ _)]
  simpa [ENNReal.ofReal_mul] using ENNReal.ofReal_le_ofReal hn

end HilbertUMD
