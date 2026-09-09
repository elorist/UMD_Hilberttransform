import HilbertUMD.UMD.MartingaleSquare
import HilbertUMD.UMD.PathwiseDavis

/-! A dimension-independent lower square-function estimate for finite real l1. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace HilbertUMD

def dyadicPartialSquare (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) (x : Leaf n) : ℝ :=
  Real.sqrt (∑ k ∈ Finset.range t,
    (leafAverage (𝕜 := ℝ) n (k + 1) f x - leafAverage (𝕜 := ℝ) n k f x) ^ 2)

theorem dyadicPartialSquare_nonneg (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) (x : Leaf n) :
    0 ≤ dyadicPartialSquare n f t x := Real.sqrt_nonneg _

@[simp] theorem dyadicPartialSquare_zero (n : ℕ) (f : Leaf n → ℝ) (x : Leaf n) :
    dyadicPartialSquare n f 0 x = 0 := by simp [dyadicPartialSquare]

theorem dyadicPartialSquare_succ (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) (x : Leaf n) :
    dyadicPartialSquare n f (t + 1) x = Real.sqrt (dyadicPartialSquare n f t x ^ 2 +
      (leafAverage (𝕜 := ℝ) n (t + 1) f x - leafAverage (𝕜 := ℝ) n t f x) ^ 2) := by
  unfold dyadicPartialSquare
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), Finset.sum_range_succ]

theorem dyadicPartialSquare_terminal (n : ℕ) (f : Leaf n → ℝ) (x : Leaf n) :
    dyadicPartialSquare n f n x = dyadicSquareFunction n f x := by
  rw [dyadicSquareFunction_eq_sqrt, dyadicPartialSquare]
  congr 1
  exact (Fin.sum_univ_eq_sum_range
    (fun k => (leafAverage (𝕜 := ℝ) n (k + 1) f x - leafAverage (𝕜 := ℝ) n k f x) ^ 2) n).symm

theorem dyadicBlockConstant_partialSquare (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) :
    DyadicBlockConstant n t (dyadicPartialSquare n f t) := by
  intro x y hxy
  unfold dyadicPartialSquare
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkt := Finset.mem_range.mp hk
  rw [leafAverage_eq_of_mem n (k + 1) f x y
      (dyadicBlock_subset n (k + 1) t (by omega) x hxy),
    leafAverage_eq_of_mem n k f x y (dyadicBlock_subset n k t (by omega) x hxy)]

def dyadicDavisCoefficient (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) (x : Leaf n) : ℝ :=
  davisCoefficient (leafAverage (𝕜 := ℝ) n t f x) (dyadicPartialSquare n f t x)

theorem dyadicBlockConstant_davisCoefficient (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) :
    DyadicBlockConstant n t (dyadicDavisCoefficient n f t) := by
  intro x y hxy
  unfold dyadicDavisCoefficient
  rw [leafAverage_eq_of_mem n t f x y hxy, dyadicBlockConstant_partialSquare n f t x y hxy]

theorem abs_dyadicDavisCoefficient_le (n : ℕ) (f : Leaf n → ℝ) (t : ℕ) (x : Leaf n) :
    |dyadicDavisCoefficient n f t x| ≤ 1 := abs_davisCoefficient_le _ _

theorem dyadic_davis_pathwise (n : ℕ) (f : Leaf n → ℝ)
    (hf : ∀ x, leafAverage (𝕜 := ℝ) n 0 f x = 0) (x : Leaf n) :
    |f x| ≤ (29 / 8) * dyadicSquareFunction n f x +
      ∑ k : Fin n, dyadicDavisCoefficient n f k.val x * dyadicDifference n k f x := by
  have h (t : ℕ) :
      Real.sqrt (leafAverage (𝕜 := ℝ) n t f x ^ 2 + dyadicPartialSquare n f t x ^ 2) ≤
        (29 / 8) * dyadicPartialSquare n f t x + ∑ k ∈ Finset.range t,
          dyadicDavisCoefficient n f k x *
            (leafAverage (𝕜 := ℝ) n (k + 1) f x - leafAverage (𝕜 := ℝ) n k f x) := by
    induction t with
    | zero => simp [hf]
    | succ t ih =>
      have hs := davis_step (leafAverage (𝕜 := ℝ) n t f x) (dyadicPartialSquare n f t x)
        (leafAverage (𝕜 := ℝ) n (t + 1) f x - leafAverage (𝕜 := ℝ) n t f x)
        (dyadicPartialSquare_nonneg n f t x)
      rw [add_sub_cancel, ← dyadicPartialSquare_succ] at hs
      have heq := Real.sq_sqrt (show 0 ≤ dyadicPartialSquare n f t x ^ 2 +
        (leafAverage (𝕜 := ℝ) n (t + 1) f x - leafAverage (𝕜 := ℝ) n t f x) ^ 2 by positivity)
      rw [← dyadicPartialSquare_succ] at heq
      rw [← heq] at hs
      rw [Finset.sum_range_succ]
      change _ ≤ _ at hs
      dsimp only [dyadicDavisCoefficient] at *
      linarith
  have hnorm : |f x| ≤ Real.sqrt (f x ^ 2 + dyadicPartialSquare n f n x ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (dyadicPartialSquare n f n x)]
  have hn := h n
  rw [leafAverage_terminal] at hn
  have hfin := hnorm.trans hn
  rw [dyadicPartialSquare_terminal] at hfin
  have heq := Fin.sum_univ_eq_sum_range
    (fun k => dyadicDavisCoefficient n f k x *
      (leafAverage (𝕜 := ℝ) n (k + 1) f x - leafAverage (𝕜 := ℝ) n k f x)) n
  simpa only [← heq, dyadicDifference, Pi.sub_apply] using hfin

/-- Averaging a finite martingale difference retains it precisely after its time. -/
theorem leafAverage_increment (n t : ℕ) (k : Fin n) (a : Leaf n → ℝ)
    (ha : DyadicBlockConstant n (k.val + 1) a)
    (hz : ∀ x, leafAverage (𝕜 := ℝ) n k.val a x = 0) (x : Leaf n) :
    leafAverage (𝕜 := ℝ) n t a x = if k.val < t then a x else 0 := by
  split_ifs with h
  · exact leafAverage_of_blockConstant n t a (ha.mono (by omega)) x
  · rw [← leafAverage_tower n t k.val (by omega) a x]
    have heq : leafAverage (𝕜 := ℝ) n k.val a = 0 := funext hz
    rw [heq]
    simp [leafAverage]

theorem leafAverage_sum_increments (n t : ℕ) (a : Fin n → Leaf n → ℝ)
    (ha : ∀ k, DyadicBlockConstant n (k.val + 1) (a k))
    (hz : ∀ k x, leafAverage (𝕜 := ℝ) n k.val (a k) x = 0) (x : Leaf n) :
    leafAverage (𝕜 := ℝ) n t (∑ k, a k) x = ∑ k, if k.val < t then a k x else 0 := by
  change (leafAverageLinear n t) (∑ k, a k) x = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => leafAverage_increment n t k (a k) (ha k) (hz k) x)

theorem dyadicDifference_sum_increments (n : ℕ) (a : Fin n → Leaf n → ℝ)
    (ha : ∀ k, DyadicBlockConstant n (k.val + 1) (a k))
    (hz : ∀ k x, leafAverage (𝕜 := ℝ) n k.val (a k) x = 0) (t : Fin n) (x : Leaf n) :
    dyadicDifference n t (∑ k, a k) x = a t x := by
  simp only [dyadicDifference, Pi.sub_apply, leafAverage_sum_increments n _ a ha hz]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ k : Fin n, if k = t then a k x else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hkt : k = t
      · simp [hkt]
      · have hv : k.val ≠ t.val := fun h => hkt (Fin.ext h)
        by_cases hlt : k.val < t.val
        · simp [hkt, hlt, show k.val < t.val + 1 by omega]
        · simp [hkt, hlt, show ¬k.val < t.val + 1 by omega]
    _ = _ := by simp

theorem sampleL2_sum_le {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → κ → ℝ) :
    sampleL2 (fun k => ∑ j, a j k) ≤ ∑ j, sampleL2 (a j) := by
  have heq : (fun k => ∑ j, a j k) = ∑ j, a j := by funext k; simp
  simp only [sampleL2, heq, WithLp.toLp_sum]
  exact norm_sum_le _ _

/-- A finite l1 lower square estimate with constant (45 / 8), uniform in both indices. -/
theorem mixedNorm_lower_square_l1 {ι : Type*} [Fintype ι]
    (n : ℕ) (f : Leaf n → ι → ℝ)
    (hf : ∀ x j, leafAverage (𝕜 := ℝ) n 0 (fun y => f y j) x = 0) :
    mixedNorm (3 / 2) 1 (leafUniform n) f ≤
      (45 / 8) * mixedNorm (3 / 2) 1 (leafUniform n)
        (fun x j => dyadicSquareFunction n (fun y => f y j) x) := by
  classical
  let a (k : Fin n) (x : Leaf n) := ∑ j,
    dyadicDavisCoefficient n (fun y => f y j) k.val x *
      dyadicDifference n k (fun y => f y j) x
  let G : Leaf n → ℝ := ∑ k, a k
  let S (x : Leaf n) := ∑ j, dyadicSquareFunction n (fun y => f y j) x
  have hS (x : Leaf n) : 0 ≤ S x := Finset.sum_nonneg
    (fun j _ => dyadicSquareFunction_nonneg n (fun y => f y j) x)
  have ha (k : Fin n) : DyadicBlockConstant n (k.val + 1) (a k) := by
    intro x y hxy
    apply Finset.sum_congr rfl
    intro j _
    have hc := (dyadicBlockConstant_davisCoefficient n (fun y => f y j) k.val).mono
      (Nat.le_succ k.val) x y hxy
    have hd := ((dyadicBlockConstant_average n (k.val + 1) (fun y => f y j)).sub
      ((dyadicBlockConstant_average n k.val (fun y => f y j)).mono (Nat.le_succ k.val))) x y hxy
    change dyadicDifference n k (fun y => f y j) y = dyadicDifference n k (fun y => f y j) x at hd
    rw [hc, hd]
  have hz (k : Fin n) (x : Leaf n) : leafAverage (𝕜 := ℝ) n k.val (a k) x = 0 := by
    have heq : a k = ∑ j, fun x => dyadicDavisCoefficient n (fun y => f y j) k.val x *
        dyadicDifference n k (fun y => f y j) x := by funext x; simp [a]
    rw [heq]
    change (leafAverageLinear n k.val) (∑ j, _) x = 0
    rw [map_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    change leafAverage (𝕜 := ℝ) n k.val
      (fun x => dyadicDavisCoefficient n (fun y => f y j) k.val x *
        dyadicDifference n k (fun y => f y j) x) x = 0
    rw [leafAverage_mul_of_blockConstant n k.val _ _
      (dyadicBlockConstant_davisCoefficient n (fun y => f y j) k.val)]
    simp [leafAverage_dyadicDifference]
  have hGzero (x : Leaf n) : leafAverage (𝕜 := ℝ) n 0 G x = 0 := by
    simp [G, leafAverage_sum_increments n 0 a ha hz]
  have hGdiff (k : Fin n) (x : Leaf n) : dyadicDifference n k G x = a k x :=
    dyadicDifference_sum_increments n a ha hz k x
  have hpoint (x : Leaf n) : (∑ j, |f x j|) ≤ (29 / 8) * S x + G x := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      dyadic_davis_pathwise n (fun y => f y j) (fun x => hf x j) x)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, S, G, a, Finset.sum_apply,
      Finset.sum_comm (s := Finset.univ (α := ι))] using h
  have hSquare (x : Leaf n) : dyadicSquareFunction n G x ≤ S x := by
    have habs : ∀ k, |a k x| ≤ ∑ j, |dyadicDifference n k (fun y => f y j) x| := by
      intro k
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (abs_dyadicDavisCoefficient_le _ _ _ _) (abs_nonneg _)).trans_eq
        (one_mul _)
    calc
      _ = sampleL2 (fun k => |a k x|) := by simp only [dyadicSquareFunction, hGdiff]
      _ ≤ sampleL2 (fun k : Fin n => ∑ j, |dyadicDifference n k (fun y => f y j) x|) :=
        sampleL2_mono (fun _ => abs_nonneg _) habs
      _ ≤ S x := sampleL2_sum_le (fun j k => |dyadicDifference n k (fun y => f y j) x|)
  have hGn : eLpNorm G (3 / 2) (leafUniform n) ≤ 2 * eLpNorm S (3 / 2) (leafUniform n) :=
    (eLpNorm_le_two_square_threeHalves n G hGzero).trans (mul_le_mul' le_rfl
      (eLpNorm_mono_real (fun x => by
        rw [Real.norm_of_nonneg (dyadicSquareFunction_nonneg _ _ _)]; exact hSquare x)))
  rw [mixedNorm_one, mixedNorm_one]
  simp only [Real.norm_of_nonneg (dyadicSquareFunction_nonneg _ _ _)]
  change eLpNorm (fun x => ∑ j, ‖f x j‖) (3 / 2) (leafUniform n) ≤
    (45 / 8) * eLpNorm S (3 / 2) (leafUniform n)
  calc
    _ ≤ eLpNorm (((29 / 8) : ℝ) • S + G) (3 / 2) (leafUniform n) := eLpNorm_mono_real (fun x => by
      rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg _))]
      simpa only [Real.norm_eq_abs, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hpoint x)
    _ ≤ eLpNorm (((29 / 8) : ℝ) • S) (3 / 2) (leafUniform n) + eLpNorm G (3 / 2) (leafUniform n) :=
      eLpNorm_add_le (leaf_memLp n 1 _).aestronglyMeasurable
        (leaf_memLp n 1 G).aestronglyMeasurable (by
          rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num)
    _ ≤ (29 / 8) * eLpNorm S (3 / 2) (leafUniform n) + 2 * eLpNorm S (3 / 2) (leafUniform n) := by
      rw [eLpNorm_const_smul]
      norm_num only [Real.enorm_eq_ofReal, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8), ENNReal.ofReal_ofNat]
      exact add_le_add_right hGn _
    _ = _ := by
      rw [← add_mul]
      congr 1
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_div]

end HilbertUMD
