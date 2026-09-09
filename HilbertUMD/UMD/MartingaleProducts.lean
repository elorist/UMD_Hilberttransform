import HilbertUMD.UMD.DyadicTransfer

/-!
# Finite dyadic martingale products

The cancellation argument in Lemma 3.1 uses the actual conditional averages
on `Leaf n`. No external analytic estimates or admitted statements occur here.
The algebraic cancellation holds for arbitrary real coefficients; their
absolute-value bound is needed only for the square-function estimates.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace HilbertUMD

/-- Functions constant on every block of the given dyadic partition. -/
def DyadicBlockConstant (n k : ℕ) (f : Leaf n → ℝ) : Prop :=
  ∀ i j, j ∈ dyadicBlock n k i → f j = f i

theorem dyadicBlockConstant_average (n k : ℕ) (f : Leaf n → ℝ) :
    DyadicBlockConstant n k (leafAverage (𝕜 := ℝ) n k f) :=
  fun i j h => leafAverage_eq_of_mem n k f i j h

theorem DyadicBlockConstant.mono {n k l : ℕ} {f : Leaf n → ℝ}
    (hf : DyadicBlockConstant n k f) (hkl : k ≤ l) : DyadicBlockConstant n l f :=
  fun i j h => hf i j (dyadicBlock_subset n k l hkl i h)

theorem DyadicBlockConstant.add {n k : ℕ} {f g : Leaf n → ℝ}
    (hf : DyadicBlockConstant n k f) (hg : DyadicBlockConstant n k g) :
    DyadicBlockConstant n k (f + g) := by
  intro i j h
  simp only [Pi.add_apply, hf i j h, hg i j h]

theorem DyadicBlockConstant.sub {n k : ℕ} {f g : Leaf n → ℝ}
    (hf : DyadicBlockConstant n k f) (hg : DyadicBlockConstant n k g) :
    DyadicBlockConstant n k (f - g) := by
  intro i j h
  simp only [Pi.sub_apply, hf i j h, hg i j h]

theorem DyadicBlockConstant.mul {n k : ℕ} {f g : Leaf n → ℝ}
    (hf : DyadicBlockConstant n k f) (hg : DyadicBlockConstant n k g) :
    DyadicBlockConstant n k (f * g) := by
  intro i j h
  simp only [Pi.mul_apply, hf i j h, hg i j h]

theorem dyadicBlockConstant_const (n k : ℕ) (c : ℝ) :
    DyadicBlockConstant n k (fun _ => c) := fun _ _ _ => rfl

theorem leafAverage_of_blockConstant (n k : ℕ) (f : Leaf n → ℝ)
    (hf : DyadicBlockConstant n k f) (i : Leaf n) :
    leafAverage (𝕜 := ℝ) n k f i = f i := by
  have hc : ((dyadicBlock n k i).card : ℝ) ≠ 0 := by
    rw [card_dyadicBlock]
    positivity
  unfold leafAverage
  rw [Finset.sum_congr rfl (fun j hj => hf i j hj)]
  simp only [Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
  field_simp

theorem leafAverage_reverse_tower (n k l : ℕ) (hkl : k ≤ l)
    (f : Leaf n → ℝ) (i : Leaf n) :
    leafAverage (𝕜 := ℝ) n l (leafAverage (𝕜 := ℝ) n k f) i =
      leafAverage (𝕜 := ℝ) n k f i :=
  leafAverage_of_blockConstant n l _ ((dyadicBlockConstant_average n k f).mono hkl) i

theorem leafAverage_mul_of_blockConstant (n k : ℕ) (a f : Leaf n → ℝ)
    (ha : DyadicBlockConstant n k a) (i : Leaf n) :
    leafAverage (𝕜 := ℝ) n k (fun j => a j * f j) i =
      a i * leafAverage (𝕜 := ℝ) n k f i := by
  unfold leafAverage
  rw [Finset.sum_congr rfl (fun j hj => congrArg (fun x => x * f j) (ha i j hj))]
  simp only [← Finset.mul_sum, smul_eq_mul]
  ring

/-- Difference at chronological step `k + 1`, with zero-based finite index. -/
def dyadicDifference (n : ℕ) (k : Fin n) (f : Leaf n → ℝ) : Leaf n → ℝ :=
  leafAverage (𝕜 := ℝ) n (k.val + 1) f - leafAverage (𝕜 := ℝ) n k.val f

theorem sum_mul_leafAverage (n k : ℕ) (f g : Leaf n → ℝ) :
    ∑ x, f x * leafAverage (𝕜 := ℝ) n k g x =
      ∑ x, leafAverage (𝕜 := ℝ) n k f x * g x := by
  induction n generalizing k with
  | zero => simp only [leafAverage_zero_depth]
  | succ n ih =>
    cases k with
    | zero =>
      simp only [leafAverage, dyadicBlock, smul_eq_mul,
        ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    | succ k =>
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [leafAverage_succ_inl, leafAverage_succ_inr]
      rw [ih k, ih k]

theorem sum_mul_dyadicDifference (n : ℕ) (k : Fin n) (f g : Leaf n → ℝ) :
    ∑ x, f x * dyadicDifference n k g x = ∑ x, dyadicDifference n k f x * g x := by
  simp only [dyadicDifference, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [sum_mul_leafAverage, sum_mul_leafAverage]

theorem leafAverage_dyadicDifference (n t : ℕ) (k : Fin n)
    (f : Leaf n → ℝ) (i : Leaf n) :
    leafAverage (𝕜 := ℝ) n t (dyadicDifference n k f) i =
      if k.val < t then dyadicDifference n k f i else 0 := by
  change (leafAverageLinear n t) ((leafAverageLinear n (k.val + 1)) f -
    (leafAverageLinear n k.val) f) i = _
  rw [map_sub]
  change leafAverage (𝕜 := ℝ) n t (leafAverage (𝕜 := ℝ) n (k.val + 1) f) i -
    leafAverage (𝕜 := ℝ) n t (leafAverage (𝕜 := ℝ) n k.val f) i = _
  split_ifs with h
  · rw [leafAverage_reverse_tower n (k.val + 1) t (by omega),
      leafAverage_reverse_tower n k.val t (by omega)]
    rfl
  · rw [leafAverage_tower n t (k.val + 1) (by omega),
      leafAverage_tower n t k.val (by omega)]
    simp

theorem dyadicScalar_eq_sum (n : ℕ) (ε : Fin n → ℝ) (f : Leaf n → ℝ) :
    dyadicScalar n ε f = ∑ k : Fin n, ε k • dyadicDifference n k f := by
  rw [dyadicScalar_apply]
  ext i
  simp [martingaleTransform, dyadicDifference, Finset.sum_apply]

theorem leafAverage_dyadicScalar (n t : ℕ) (ε : Fin n → ℝ)
    (f : Leaf n → ℝ) (i : Leaf n) :
    leafAverage (𝕜 := ℝ) n t (dyadicScalar n ε f) i =
      ∑ k : Fin n, if k.val < t then ε k * dyadicDifference n k f i else 0 := by
  rw [dyadicScalar_eq_sum]
  change (leafAverageLinear n t) (∑ k : Fin n, ε k • dyadicDifference n k f) i = _
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  change ε k * leafAverage (𝕜 := ℝ) n t (dyadicDifference n k f) i = _
  rw [leafAverage_dyadicDifference]
  split_ifs <;> simp

@[simp] theorem leafAverage_dyadicScalar_zero (n : ℕ) (ε : Fin n → ℝ)
    (f : Leaf n → ℝ) (i : Leaf n) :
    leafAverage (𝕜 := ℝ) n 0 (dyadicScalar n ε f) i = 0 := by
  simp [leafAverage_dyadicScalar]

/-- Conditional averaging preserves precisely the already revealed transform
increments. This is the transform difference identity used in Lemma 3.1. -/
theorem dyadicDifference_dyadicScalar (n : ℕ) (ε : Fin n → ℝ)
    (f : Leaf n → ℝ) (k : Fin n) (i : Leaf n) :
    dyadicDifference n k (dyadicScalar n ε f) i = ε k * dyadicDifference n k f i := by
  simp only [dyadicDifference, Pi.sub_apply, leafAverage_dyadicScalar]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin n, if j = k then ε j * dyadicDifference n j f i else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = k
      · subst j
        simp [dyadicDifference]
      · have hv : j.val ≠ k.val := fun h => hj (Fin.ext h)
        by_cases hlt : j.val < k.val
        · simp [hlt, show j.val < k.val + 1 by omega, hj]
        · simp [hlt, show ¬ j.val < k.val + 1 by omega, hj]
    _ = _ := by simp [dyadicDifference]

/-- The product process with the two transformed terminal functions. -/
def dyadicProductProcess (n : ℕ) (ε : Fin n → ℝ) (u v : Leaf n → ℝ)
    (k : ℕ) (i : Leaf n) : ℝ :=
  leafAverage (𝕜 := ℝ) n k u i * leafAverage (𝕜 := ℝ) n k (dyadicScalar n ε v) i -
    leafAverage (𝕜 := ℝ) n k v i * leafAverage (𝕜 := ℝ) n k (dyadicScalar n ε u) i

theorem dyadicBlockConstant_productProcess (n k : ℕ) (ε : Fin n → ℝ)
    (u v : Leaf n → ℝ) : DyadicBlockConstant n k (dyadicProductProcess n ε u v k) :=
  ((dyadicBlockConstant_average n k u).mul (dyadicBlockConstant_average n k _)).sub
    ((dyadicBlockConstant_average n k v).mul (dyadicBlockConstant_average n k _))

@[simp] theorem dyadicProductProcess_zero (n : ℕ) (ε : Fin n → ℝ)
    (u v : Leaf n → ℝ) (i : Leaf n) : dyadicProductProcess n ε u v 0 i = 0 := by
  simp [dyadicProductProcess]

@[simp] theorem dyadicProductProcess_terminal (n : ℕ) (ε : Fin n → ℝ)
    (u v : Leaf n → ℝ) (i : Leaf n) :
    dyadicProductProcess n ε u v n i = u i * dyadicScalar n ε v i -
      v i * dyadicScalar n ε u i := by
  simp [dyadicProductProcess]

/-- The quadratic increment terms cancel exactly, for arbitrary real ε. -/
theorem dyadicProductProcess_increment (n : ℕ) (ε : Fin n → ℝ)
    (u v : Leaf n → ℝ) (k : Fin n) (i : Leaf n) :
    dyadicProductProcess n ε u v (k.val + 1) i - dyadicProductProcess n ε u v k.val i =
      (ε k * leafAverage (𝕜 := ℝ) n k.val u i -
        leafAverage (𝕜 := ℝ) n k.val (dyadicScalar n ε u) i) * dyadicDifference n k v i +
      (leafAverage (𝕜 := ℝ) n k.val (dyadicScalar n ε v) i -
        ε k * leafAverage (𝕜 := ℝ) n k.val v i) * dyadicDifference n k u i := by
  have hu := dyadicDifference_dyadicScalar n ε u k i
  have hv := dyadicDifference_dyadicScalar n ε v k i
  simp only [dyadicDifference, Pi.sub_apply] at hu hv
  have hu' : leafAverage (𝕜 := ℝ) n (k.val + 1) (dyadicScalar n ε u) i =
      leafAverage (𝕜 := ℝ) n k.val (dyadicScalar n ε u) i + ε k *
        (leafAverage (𝕜 := ℝ) n (k.val + 1) u i - leafAverage (𝕜 := ℝ) n k.val u i) := by
    linarith
  have hv' : leafAverage (𝕜 := ℝ) n (k.val + 1) (dyadicScalar n ε v) i =
      leafAverage (𝕜 := ℝ) n k.val (dyadicScalar n ε v) i + ε k *
        (leafAverage (𝕜 := ℝ) n (k.val + 1) v i - leafAverage (𝕜 := ℝ) n k.val v i) := by
    linarith
  simp only [dyadicProductProcess, dyadicDifference, Pi.sub_apply, hu', hv']
  ring

/-- Averaging a product increment at the previous time gives zero. -/
theorem leafAverage_productProcess_succ (n : ℕ) (ε : Fin n → ℝ)
    (u v : Leaf n → ℝ) (k : Fin n) (i : Leaf n) :
    leafAverage (𝕜 := ℝ) n k.val (dyadicProductProcess n ε u v (k.val + 1)) i =
      dyadicProductProcess n ε u v k.val i := by
  let a : Leaf n → ℝ := fun j => ε k * leafAverage (𝕜 := ℝ) n k.val u j -
    leafAverage (𝕜 := ℝ) n k.val (dyadicScalar n ε u) j
  let b : Leaf n → ℝ := fun j => leafAverage (𝕜 := ℝ) n k.val (dyadicScalar n ε v) j -
    ε k * leafAverage (𝕜 := ℝ) n k.val v j
  have ha : DyadicBlockConstant n k.val a :=
    ((dyadicBlockConstant_const n k.val (ε k)).mul
      (dyadicBlockConstant_average n k.val u)).sub (dyadicBlockConstant_average n k.val _)
  have hb : DyadicBlockConstant n k.val b :=
    (dyadicBlockConstant_average n k.val _).sub
      ((dyadicBlockConstant_const n k.val (ε k)).mul (dyadicBlockConstant_average n k.val v))
  have hinc : dyadicProductProcess n ε u v (k.val + 1) =
      dyadicProductProcess n ε u v k.val + a * dyadicDifference n k v +
        b * dyadicDifference n k u := by
    funext j
    have h := dyadicProductProcess_increment n ε u v k j
    change _ = _ + a j * dyadicDifference n k v j + b j * dyadicDifference n k u j
    dsimp [a, b]
    linarith
  rw [hinc]
  change (leafAverageLinear n k.val) (_ + _ + _) i = _
  rw [map_add, map_add]
  change leafAverage (𝕜 := ℝ) n k.val (dyadicProductProcess n ε u v k.val) i +
    leafAverage (𝕜 := ℝ) n k.val (fun j => a j * dyadicDifference n k v j) i +
    leafAverage (𝕜 := ℝ) n k.val (fun j => b j * dyadicDifference n k u j) i = _
  rw [leafAverage_of_blockConstant n k.val _ (dyadicBlockConstant_productProcess n k.val ε u v),
    leafAverage_mul_of_blockConstant n k.val a _ ha,
    leafAverage_mul_of_blockConstant n k.val b _ hb]
  simp [leafAverage_dyadicDifference]

theorem leafAverage_productProcess (n : ℕ) (ε : Fin n → ℝ)
    (u v : Leaf n → ℝ) (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ n) (i : Leaf n) :
    leafAverage (𝕜 := ℝ) n k (dyadicProductProcess n ε u v l) i =
      dyadicProductProcess n ε u v k i := by
  induction l generalizing k with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    exact leafAverage_of_blockConstant n 0 _ (dyadicBlockConstant_productProcess n 0 ε u v) i
  | succ l ih =>
    by_cases hk : k = l + 1
    · subst k
      exact leafAverage_of_blockConstant n (l + 1) _
        (dyadicBlockConstant_productProcess n (l + 1) ε u v) i
    · have hle : k ≤ l := by omega
      calc
        _ = leafAverage (𝕜 := ℝ) n k
            (leafAverage (𝕜 := ℝ) n l (dyadicProductProcess n ε u v (l + 1))) i :=
          (leafAverage_tower n k l hle _ i).symm
        _ = leafAverage (𝕜 := ℝ) n k (dyadicProductProcess n ε u v l) i := by
          congr 1
          funext j
          exact leafAverage_productProcess_succ n ε u v ⟨l, by omega⟩ j
        _ = _ := ih k hle (by omega)

/-- The maximal function, including the initial conditional average. -/
def dyadicMaximal (n : ℕ) (f : Leaf n → ℝ) (i : Leaf n) : ℝ :=
  ‖fun k : Fin (n + 1) => leafAverage (𝕜 := ℝ) n k.val f i‖

theorem dyadicMaximal_nonneg (n : ℕ) (f : Leaf n → ℝ) (i : Leaf n) :
    0 ≤ dyadicMaximal n f i := norm_nonneg _

theorem abs_leafAverage_le_dyadicMaximal (n k : ℕ) (hk : k ≤ n)
    (f : Leaf n → ℝ) (i : Leaf n) :
    |leafAverage (𝕜 := ℝ) n k f i| ≤ dyadicMaximal n f i := by
  exact norm_le_pi_norm (fun l : Fin (n + 1) => leafAverage (𝕜 := ℝ) n l.val f i)
    ⟨k, by omega⟩

/-- The square function is the Euclidean norm of the actual martingale
differences, with no initial-value term. -/
def dyadicSquareFunction (n : ℕ) (f : Leaf n → ℝ) (i : Leaf n) : ℝ :=
  sampleL2 (fun k : Fin n => |dyadicDifference n k f i|)

theorem dyadicSquareFunction_nonneg (n : ℕ) (f : Leaf n → ℝ) (i : Leaf n) :
    0 ≤ dyadicSquareFunction n f i := sampleL2_nonneg _

theorem dyadicSquareFunction_sq (n : ℕ) (f : Leaf n → ℝ) (i : Leaf n) :
    dyadicSquareFunction n f i ^ 2 = ∑ k : Fin n, dyadicDifference n k f i ^ 2 := by
  simp [dyadicSquareFunction, sampleL2_sq, sq_abs]

theorem dyadicSquareFunction_eq_sqrt (n : ℕ) (f : Leaf n → ℝ) (i : Leaf n) :
    dyadicSquareFunction n f i = Real.sqrt (∑ k : Fin n, dyadicDifference n k f i ^ 2) := by
  rw [← dyadicSquareFunction_sq, Real.sqrt_sq (dyadicSquareFunction_nonneg n f i)]

/-- Multipliers in [-1,1] decrease the pointwise square function. -/
theorem dyadicSquareFunction_transform_le (n : ℕ) (ε : Fin n → ℝ)
    (hε : ∀ k, |ε k| ≤ 1) (f : Leaf n → ℝ) (i : Leaf n) :
    dyadicSquareFunction n (dyadicScalar n ε f) i ≤ dyadicSquareFunction n f i := by
  apply sampleL2_mono (fun _ => abs_nonneg _)
  intro k
  rw [dyadicDifference_dyadicScalar, abs_mul]
  simpa using mul_le_mul_of_nonneg_right (hε k) (abs_nonneg (dyadicDifference n k f i))

theorem dyadicDifference_productProcess_terminal (n : ℕ) (ε : Fin n → ℝ)
    (u v : Leaf n → ℝ) (k : Fin n) (i : Leaf n) :
    dyadicDifference n k (dyadicProductProcess n ε u v n) i =
      (ε k * leafAverage (𝕜 := ℝ) n k.val u i -
        leafAverage (𝕜 := ℝ) n k.val (dyadicScalar n ε u) i) * dyadicDifference n k v i +
      (leafAverage (𝕜 := ℝ) n k.val (dyadicScalar n ε v) i -
        ε k * leafAverage (𝕜 := ℝ) n k.val v i) * dyadicDifference n k u i := by
  simp only [dyadicDifference, Pi.sub_apply]
  rw [leafAverage_productProcess n ε u v (k.val + 1) n (by omega) le_rfl,
    leafAverage_productProcess n ε u v k.val n (by omega) le_rfl]
  exact dyadicProductProcess_increment n ε u v k i

private theorem abs_mul_sub_bound (c x y A B : ℝ) (hc : |c| ≤ 1)
    (hx : |x| ≤ A) (hy : |y| ≤ B) : |c * x - y| ≤ A + B := by
  calc
    |c * x - y| ≤ |c * x| + |y| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (c * x) y
    _ = |c| * |x| + |y| := by rw [abs_mul]
    _ ≤ 1 * |x| + |y| := by gcongr
    _ ≤ A + B := by linarith

/-- The pointwise increment estimate in the product argument. -/
theorem abs_dyadicDifference_product_le (n : ℕ) (ε : Fin n → ℝ)
    (hε : ∀ k, |ε k| ≤ 1) (u v : Leaf n → ℝ) (k : Fin n) (i : Leaf n) :
    |dyadicDifference n k (dyadicProductProcess n ε u v n) i| ≤
      (dyadicMaximal n u i + dyadicMaximal n (dyadicScalar n ε u) i) *
        |dyadicDifference n k v i| +
      (dyadicMaximal n v i + dyadicMaximal n (dyadicScalar n ε v) i) *
        |dyadicDifference n k u i| := by
  have ha := abs_mul_sub_bound (ε k) (leafAverage (𝕜 := ℝ) n k.val u i)
    (leafAverage (𝕜 := ℝ) n k.val (dyadicScalar n ε u) i)
    (dyadicMaximal n u i) (dyadicMaximal n (dyadicScalar n ε u) i) (hε k)
    (abs_leafAverage_le_dyadicMaximal n k.val (by omega) u i)
    (abs_leafAverage_le_dyadicMaximal n k.val (by omega) (dyadicScalar n ε u) i)
  have hb := abs_mul_sub_bound (ε k) (leafAverage (𝕜 := ℝ) n k.val v i)
    (leafAverage (𝕜 := ℝ) n k.val (dyadicScalar n ε v) i)
    (dyadicMaximal n v i) (dyadicMaximal n (dyadicScalar n ε v) i) (hε k)
    (abs_leafAverage_le_dyadicMaximal n k.val (by omega) v i)
    (abs_leafAverage_le_dyadicMaximal n k.val (by omega) (dyadicScalar n ε v) i)
  rw [abs_sub_comm] at hb
  rw [dyadicDifference_productProcess_terminal]
  exact (abs_add_le _ _).trans (by
    simp only [abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hb (abs_nonneg _)))

/-- The square-function estimate from Lemma 3.1, proved by finite Euclidean
Minkowski after the checked martingale cancellation. -/
theorem dyadicSquareFunction_product_le (n : ℕ) (ε : Fin n → ℝ)
    (hε : ∀ k, |ε k| ≤ 1) (u v : Leaf n → ℝ) (i : Leaf n) :
    dyadicSquareFunction n (dyadicProductProcess n ε u v n) i ≤
      (dyadicMaximal n u i + dyadicMaximal n (dyadicScalar n ε u) i) *
        dyadicSquareFunction n v i +
      (dyadicMaximal n v i + dyadicMaximal n (dyadicScalar n ε v) i) *
        dyadicSquareFunction n u i := by
  let A := dyadicMaximal n u i + dyadicMaximal n (dyadicScalar n ε u) i
  let B := dyadicMaximal n v i + dyadicMaximal n (dyadicScalar n ε v) i
  have hA : 0 ≤ A := add_nonneg (dyadicMaximal_nonneg n u i) (dyadicMaximal_nonneg n _ i)
  have hB : 0 ≤ B := add_nonneg (dyadicMaximal_nonneg n v i) (dyadicMaximal_nonneg n _ i)
  calc
    _ ≤ sampleL2 (fun k : Fin n => A * |dyadicDifference n k v i| +
        B * |dyadicDifference n k u i|) :=
      sampleL2_mono (fun _ => abs_nonneg _)
        (fun k => abs_dyadicDifference_product_le n ε hε u v k i)
    _ ≤ sampleL2 (fun k : Fin n => A * |dyadicDifference n k v i|) +
        sampleL2 (fun k : Fin n => B * |dyadicDifference n k u i|) := sampleL2_add_le _ _
    _ = _ := by rw [sampleL2_mul A hA, sampleL2_mul B hB]; rfl

/-- Both inequalities in the manuscript's pointwise square-function line. -/
theorem dyadicSquareFunction_transformed_product_le (n : ℕ) (ε : Fin n → ℝ)
    (hε : ∀ k, |ε k| ≤ 1) (u v : Leaf n → ℝ) (i : Leaf n) :
    dyadicSquareFunction n (dyadicScalar n ε (dyadicProductProcess n ε u v n)) i ≤
      (dyadicMaximal n u i + dyadicMaximal n (dyadicScalar n ε u) i) *
        dyadicSquareFunction n v i +
      (dyadicMaximal n v i + dyadicMaximal n (dyadicScalar n ε v) i) *
        dyadicSquareFunction n u i :=
  (dyadicSquareFunction_transform_le n ε hε _ i).trans
    (dyadicSquareFunction_product_le n ε hε u v i)

end HilbertUMD
