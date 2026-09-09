import HilbertUMD.UMD.LowerSquareL1

/-!
# A finite vector-valued Doob inequality

The quadratic pathwise maximal inequality gives a scalar martingale whose
square function is bounded by the product of the coordinate maximal and
square functions. The scalar reverse square estimate at exponent 3/2,
Hölder, and the Hilbert square estimate at exponent 3 then give a constant
independent of both the depth and the number of coordinates.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace HilbertUMD

/-- The running absolute maximum of a real sequence, including time zero. -/
def pathMax (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => |a 0|
  | t + 1 => max (pathMax a t) |a (t + 1)|

theorem pathMax_nonneg (a : ℕ → ℝ) (t : ℕ) : 0 ≤ pathMax a t := by
  cases t with
  | zero => exact abs_nonneg _
  | succ t => exact (abs_nonneg _).trans (le_max_right _ _)

theorem abs_le_pathMax (a : ℕ → ℝ) (t : ℕ) : |a t| ≤ pathMax a t := by
  cases t with
  | zero => exact le_rfl
  | succ t => exact le_max_right _ _

theorem pathMax_mono (a : ℕ → ℝ) : Monotone (pathMax a) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

theorem pathMax_le (a : ℕ → ℝ) (t : ℕ) (b : ℝ)
    (h : ∀ k, k ≤ t → |a k| ≤ b) : pathMax a t ≤ b := by
  induction t with
  | zero => exact h 0 le_rfl
  | succ t ih => exact max_le (ih (fun k hk => h k (by omega))) (h _ le_rfl)

/-- A predictable coefficient for the quadratic maximal inequality. -/
def pathMaxCoefficient (a : ℕ → ℝ) (t : ℕ) : ℝ :=
  pathMax a t * (if 0 ≤ a t then 1 else -1)

theorem abs_pathMaxCoefficient (a : ℕ → ℝ) (t : ℕ) :
    |pathMaxCoefficient a t| = pathMax a t := by
  simp only [pathMaxCoefficient, abs_mul, abs_of_nonneg (pathMax_nonneg a t)]
  split_ifs <;> simp

private theorem quadratic_max_step (x y m : ℝ) (hm : 0 ≤ m) :
    2 * (m * (if 0 ≤ x then 1 else -1)) * (y - x) ≤
      (2 * max m |y| * |y| - (max m |y|) ^ 2) - (2 * m * |x| - m ^ 2) := by
  have hs : (if 0 ≤ x then (1 : ℝ) else -1) * (y - x) ≤ |y| - |x| := by
    split_ifs with hx
    · rw [abs_of_nonneg hx]
      linarith [le_abs_self y]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith [neg_le_abs y]
  have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * m by positivity)
  rcases le_total |y| m with hy | hy
  · rw [max_eq_left hy]
    nlinarith
  · rw [max_eq_right hy]
    nlinarith [sq_nonneg (|y| - m)]

/-- A pathwise quadratic Doob inequality, valid for arbitrary real sequences. -/
theorem pathMax_sq_le (a : ℕ → ℝ) (t : ℕ) :
    pathMax a t ^ 2 ≤ 4 * a t ^ 2 - 4 * ∑ k ∈ Finset.range t,
      pathMaxCoefficient a k * (a (k + 1) - a k) := by
  have h (t : ℕ) :
      2 * (∑ k ∈ Finset.range t, pathMaxCoefficient a k * (a (k + 1) - a k)) ≤
        2 * pathMax a t * |a t| - pathMax a t ^ 2 := by
    induction t with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, pathMax]
      nlinarith [sq_nonneg (a 0), sq_abs (a 0)]
    | succ t ih =>
      have hs := quadratic_max_step (a t) (a (t + 1)) (pathMax a t)
        (pathMax_nonneg a t)
      rw [Finset.sum_range_succ]
      simp only [pathMax, pathMaxCoefficient] at *
      linarith
  have ht := h t
  nlinarith [sq_nonneg (pathMax a t - 2 * |a t|), sq_abs (a t)]

/-- The running maximum of the actual dyadic conditional averages. -/
def dyadicRunningMax (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) (x : Leaf n) : ℝ :=
  pathMax (fun k => leafAverage (𝕜 := ℝ) n k f x) t

theorem dyadicRunningMax_terminal (n : ℕ) (f : Leaf n → ℝ) (x : Leaf n) :
    dyadicRunningMax n f n x = dyadicMaximal n f x := by
  apply le_antisymm
  · exact pathMax_le _ n _ (fun k hk => abs_leafAverage_le_dyadicMaximal n k hk f x)
  · apply (pi_norm_le_iff_of_nonneg (pathMax_nonneg _ n)).mpr
    intro k
    exact (abs_le_pathMax (fun l => leafAverage (𝕜 := ℝ) n l f x) k.val).trans
      (pathMax_mono _ (show k.val ≤ n by omega))

theorem dyadicBlockConstant_runningMax (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) :
    DyadicBlockConstant n t (dyadicRunningMax n f t) := by
  induction t with
  | zero =>
    intro x y hxy
    simp only [dyadicRunningMax, pathMax, leafAverage_eq_of_mem n 0 f x y hxy]
  | succ t ih =>
    intro x y hxy
    change max (dyadicRunningMax n f t y) |leafAverage (𝕜 := ℝ) n (t + 1) f y| =
      max (dyadicRunningMax n f t x) |leafAverage (𝕜 := ℝ) n (t + 1) f x|
    rw [ih.mono (Nat.le_succ t) x y hxy, leafAverage_eq_of_mem n (t + 1) f x y hxy]

def dyadicMaxCoefficient (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) (x : Leaf n) : ℝ :=
  pathMaxCoefficient (fun k => leafAverage (𝕜 := ℝ) n k f x) t

theorem dyadicBlockConstant_maxCoefficient (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) :
    DyadicBlockConstant n t (dyadicMaxCoefficient n f t) := by
  intro x y hxy
  change dyadicRunningMax n f t y * (if 0 ≤ leafAverage (𝕜 := ℝ) n t f y then 1 else -1) =
    dyadicRunningMax n f t x * (if 0 ≤ leafAverage (𝕜 := ℝ) n t f x then 1 else -1)
  rw [dyadicBlockConstant_runningMax n f t x y hxy, leafAverage_eq_of_mem n t f x y hxy]

theorem abs_dyadicMaxCoefficient_le (n : ℕ) (f : Leaf n → ℝ) (t : ℕ)
    (ht : t ≤ n) (x : Leaf n) :
    |dyadicMaxCoefficient n f t x| ≤ dyadicMaximal n f x := by
  rw [dyadicMaxCoefficient, abs_pathMaxCoefficient, ← dyadicRunningMax_terminal]
  exact pathMax_mono _ ht

theorem dyadicMaximal_sq_le (n : ℕ) (f : Leaf n → ℝ) (x : Leaf n) :
    dyadicMaximal n f x ^ 2 ≤ 4 * f x ^ 2 - 4 * ∑ k : Fin n,
      dyadicMaxCoefficient n f k.val x * dyadicDifference n k f x := by
  have h := pathMax_sq_le (fun k => leafAverage (𝕜 := ℝ) n k f x) n
  change dyadicRunningMax n f n x ^ 2 ≤ _ at h
  rw [dyadicRunningMax_terminal, leafAverage_terminal] at h
  rw [← Fin.sum_univ_eq_sum_range (fun k =>
    pathMaxCoefficient (fun l => leafAverage (𝕜 := ℝ) n l f x) k *
      (leafAverage (𝕜 := ℝ) n (k + 1) f x - leafAverage (𝕜 := ℝ) n k f x)) n] at h
  exact h

section Coordinates
variable {ι : Type*} [Fintype ι]

/-- The scalar predictable increment obtained by summing over coordinates. -/
def dyadicMaxIncrement (n : ℕ) (f : Leaf n → ι → ℝ) (k : Fin n) (x : Leaf n) : ℝ :=
  ∑ j, dyadicMaxCoefficient n (fun y => f y j) k.val x *
    dyadicDifference n k (fun y => f y j) x

theorem dyadicBlockConstant_maxIncrement (n : ℕ) (f : Leaf n → ι → ℝ) (k : Fin n) :
    DyadicBlockConstant n (k.val + 1) (dyadicMaxIncrement n f k) := by
  intro x y hxy
  apply Finset.sum_congr rfl
  intro j _
  have hc := (dyadicBlockConstant_maxCoefficient n (fun y => f y j) k.val).mono
    (Nat.le_succ k.val) x y hxy
  have hd := ((dyadicBlockConstant_average n (k.val + 1) (fun y => f y j)).sub
    ((dyadicBlockConstant_average n k.val (fun y => f y j)).mono (Nat.le_succ k.val))) x y hxy
  change dyadicDifference n k (fun y => f y j) y = dyadicDifference n k (fun y => f y j) x at hd
  rw [hc, hd]

theorem leafAverage_maxIncrement_zero (n : ℕ) (f : Leaf n → ι → ℝ)
    (k : Fin n) (x : Leaf n) :
    leafAverage (𝕜 := ℝ) n k.val (dyadicMaxIncrement n f k) x = 0 := by
  have heq : dyadicMaxIncrement n f k = ∑ j, fun x =>
      dyadicMaxCoefficient n (fun y => f y j) k.val x *
        dyadicDifference n k (fun y => f y j) x := by funext x; simp [dyadicMaxIncrement]
  rw [heq]
  change (leafAverageLinear n k.val) (∑ j, _) x = 0
  rw [map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  change leafAverage (𝕜 := ℝ) n k.val
    (fun x => dyadicMaxCoefficient n (fun y => f y j) k.val x *
      dyadicDifference n k (fun y => f y j) x) x = 0
  rw [leafAverage_mul_of_blockConstant n k.val _ _
    (dyadicBlockConstant_maxCoefficient n (fun y => f y j) k.val)]
  simp [leafAverage_dyadicDifference]

/-- The scalar martingale terminal value in the vector maximal argument. -/
def dyadicMaxSum (n : ℕ) (f : Leaf n → ι → ℝ) : Leaf n → ℝ :=
  ∑ k, dyadicMaxIncrement n f k

theorem leafAverage_maxSum_zero (n : ℕ) (f : Leaf n → ι → ℝ) (x : Leaf n) :
    leafAverage (𝕜 := ℝ) n 0 (dyadicMaxSum n f) x = 0 := by
  simp [dyadicMaxSum, leafAverage_sum_increments n 0 _
    (dyadicBlockConstant_maxIncrement n f) (leafAverage_maxIncrement_zero n f)]

theorem dyadicDifference_maxSum (n : ℕ) (f : Leaf n → ι → ℝ) (k : Fin n) (x : Leaf n) :
    dyadicDifference n k (dyadicMaxSum n f) x = dyadicMaxIncrement n f k x :=
  dyadicDifference_sum_increments n _ (dyadicBlockConstant_maxIncrement n f)
    (leafAverage_maxIncrement_zero n f) k x

theorem sampleL2_maximal_sq_le (n : ℕ) (f : Leaf n → ι → ℝ) (x : Leaf n) :
    sampleL2 (fun j => dyadicMaximal n (fun y => f y j) x) ^ 2 ≤
      4 * sampleL2 (f x) ^ 2 - 4 * dyadicMaxSum n f x := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    dyadicMaximal_sq_le n (fun y => f y j) x)
  simpa only [sampleL2_sq, Finset.sum_sub_distrib, ← Finset.mul_sum,
    dyadicMaxSum, dyadicMaxIncrement, Finset.sum_apply,
    Finset.sum_comm (s := Finset.univ (α := ι))] using h

/-- Cauchy-Schwarz bounds the scalar square function by the product of the
coordinatewise maximal and square-function Euclidean norms. -/
theorem dyadicSquareFunction_maxSum_le (n : ℕ) (f : Leaf n → ι → ℝ) (x : Leaf n) :
    dyadicSquareFunction n (dyadicMaxSum n f) x ≤
      sampleL2 (fun j => dyadicMaximal n (fun y => f y j) x) *
        sampleL2 (fun j => dyadicSquareFunction n (fun y => f y j) x) := by
  apply (sq_le_sq₀ (dyadicSquareFunction_nonneg _ _ _)
    (mul_nonneg (sampleL2_nonneg _) (sampleL2_nonneg _))).mp
  simp only [dyadicSquareFunction_sq, dyadicDifference_maxSum, mul_pow, sampleL2_sq]
  rw [Finset.sum_comm (s := Finset.univ (α := ι)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  apply (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => dyadicMaxCoefficient n (fun y => f y j) k.val x)
    (fun j => dyadicDifference n k (fun y => f y j) x)).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  apply Finset.sum_le_sum
  intro j _
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (dyadicMaximal_nonneg _ _ _)).2
    (abs_dyadicMaxCoefficient_le n (fun y => f y j) k.val (by omega) x)

end Coordinates

private theorem leaf_toReal_eLpNorm (n : ℕ) (p : ℝ≥0∞) (f : Leaf n → ℝ) :
    (eLpNorm f p (leafUniform n)).toReal = lpNorm f p (leafUniform n) :=
  toReal_eLpNorm (leaf_memLp n p f).aestronglyMeasurable

theorem lpNorm_sq_threeHalves (n : ℕ) (f : Leaf n → ℝ) :
    lpNorm (fun x => f x ^ 2) (3 / 2) (leafUniform n) =
      lpNorm f 3 (leafUniform n) ^ 2 := by
  have h := eLpNorm_norm_rpow (μ := leafUniform n) (p := 3 / 2) f
    (by norm_num : (0 : ℝ) < 2)
  norm_num only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_ofNat,
    ENNReal.div_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ∞),
    ENNReal.rpow_two] at h
  have hr := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_pow, leaf_toReal_eLpNorm] using hr

theorem leaf_lpNorm_mul_three (n : ℕ) (f g : Leaf n → ℝ) :
    lpNorm (fun x => f x * g x) (3 / 2) (leafUniform n) ≤
      lpNorm f 3 (leafUniform n) * lpNorm g 3 (leafUniform n) := by
  let : ENNReal.HolderTriple 3 3 (3 / 2) := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by simp)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 3) (q := 3) (r := 3 / 2)
    (leaf_memLp n 3 f).aestronglyMeasurable (leaf_memLp n 3 g).aestronglyMeasurable
    (fun a b : ℝ => a * b) 1 (Filter.Eventually.of_forall (fun x => by simp [norm_mul]))
  simp only [ENNReal.coe_one, one_mul] at h
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (leaf_memLp n 3 f).2.ne (leaf_memLp n 3 g).2.ne) h
  simpa only [ENNReal.toReal_mul, leaf_toReal_eLpNorm] using hr

theorem lpNorm_sampleL2_square_three {ι : Type*} [Fintype ι]
    (n : ℕ) (f : Leaf n → ι → ℝ) :
    lpNorm (fun x => sampleL2 (fun j => dyadicSquareFunction n (fun y => f y j) x))
        3 (leafUniform n) ≤ 2 * lpNorm (fun x => sampleL2 (f x)) 3 (leafUniform n) := by
  have h := dyadic_hilbert_square_three n f
  rw [mixedNorm_eq_eLpNorm_norm, mixedNorm_eq_eLpNorm_norm] at h
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (leaf_memLp n 3 _).2.ne) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    leaf_toReal_eLpNorm, sampleL2, PiLp.norm_eq_of_L2] using hr

/-- The vector-valued dyadic Doob inequality at exponents 3 and 2, with an
explicit dimension- and depth-independent constant. -/
theorem dyadic_vector_doob_three_two {ι : Type*} [Fintype ι]
    (n : ℕ) (f : Leaf n → ι → ℝ) :
    mixedNorm 3 2 (leafUniform n) (fun x j => dyadicMaximal n (fun y => f y j) x) ≤
      (65 / 4) * mixedNorm 3 2 (leafUniform n) f := by
  let M (x : Leaf n) := sampleL2 (fun j => dyadicMaximal n (fun y => f y j) x)
  let F (x : Leaf n) := sampleL2 (f x)
  let S (x : Leaf n) := sampleL2 (fun j => dyadicSquareFunction n (fun y => f y j) x)
  let G := dyadicMaxSum n f
  have hp : (1 : ℝ≥0∞) ≤ 3 / 2 := by
    rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num
  have hS : lpNorm S 3 (leafUniform n) ≤ 2 * lpNorm F 3 (leafUniform n) :=
    lpNorm_sampleL2_square_three n f
  have hG : lpNorm G (3 / 2) (leafUniform n) ≤
      4 * lpNorm M 3 (leafUniform n) * lpNorm F 3 (leafUniform n) := by
    have h := eLpNorm_le_two_square_threeHalves n G (leafAverage_maxSum_zero n f)
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (leaf_memLp n _ _).2.ne) h
    have hrev : lpNorm G (3 / 2) (leafUniform n) ≤
        2 * lpNorm (dyadicSquareFunction n G) (3 / 2) (leafUniform n) := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
        leaf_toReal_eLpNorm] using hr
    have hpoint : lpNorm (dyadicSquareFunction n G) (3 / 2) (leafUniform n) ≤
        lpNorm (fun x => M x * S x) (3 / 2) (leafUniform n) :=
      lpNorm_mono_real (leaf_memLp n _ _) (fun x => by
        rw [Real.norm_of_nonneg (dyadicSquareFunction_nonneg _ _ _)]
        exact dyadicSquareFunction_maxSum_le n f x)
    have hh := leaf_lpNorm_mul_three n M S
    have hmul := mul_le_mul_of_nonneg_left hS
      (lpNorm_nonneg (f := M) (p := 3) (μ := leafUniform n))
    nlinarith
  have hquad : lpNorm M 3 (leafUniform n) ^ 2 ≤
      4 * lpNorm F 3 (leafUniform n) ^ 2 + 4 * lpNorm G (3 / 2) (leafUniform n) := by
    rw [← lpNorm_sq_threeHalves, ← lpNorm_sq_threeHalves]
    calc
      _ ≤ lpNorm ((4 : ℝ) • (fun x => F x ^ 2) - (4 : ℝ) • G) (3 / 2) (leafUniform n) :=
        lpNorm_mono_real (leaf_memLp n _ _) (fun x => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact sampleL2_maximal_sq_le n f x)
      _ ≤ lpNorm ((4 : ℝ) • (fun x => F x ^ 2)) (3 / 2) (leafUniform n) +
          lpNorm ((4 : ℝ) • G) (3 / 2) (leafUniform n) := lpNorm_sub_le (leaf_memLp n _ _) hp
      _ = _ := by norm_num [lpNorm_const_smul]
  have hnorm : lpNorm M 3 (leafUniform n) ≤ (65 / 4) * lpNorm F 3 (leafUniform n) := by
    have hM : 0 ≤ lpNorm M 3 (leafUniform n) := lpNorm_nonneg
    have hF : 0 ≤ lpNorm F 3 (leafUniform n) := lpNorm_nonneg
    by_contra h
    have hlt : (65 / 4) * lpNorm F 3 (leafUniform n) < lpNorm M 3 (leafUniform n) := lt_of_not_ge h
    have hprod : 0 < (lpNorm M 3 (leafUniform n) - (65 / 4) * lpNorm F 3 (leafUniform n)) *
        (lpNorm M 3 (leafUniform n) + lpNorm F 3 (leafUniform n) / 4) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg (lpNorm F 3 (leafUniform n))]
  rw [mixedNorm_eq_eLpNorm_norm, mixedNorm_eq_eLpNorm_norm]
  change eLpNorm M 3 (leafUniform n) ≤ (65 / 4) * eLpNorm F 3 (leafUniform n)
  rw [← ofReal_lpNorm (leaf_memLp n 3 M), ← ofReal_lpNorm (leaf_memLp n 3 F)]
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (65 / 4)),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_ofNat]
    using ENNReal.ofReal_le_ofReal hnorm

end HilbertUMD
