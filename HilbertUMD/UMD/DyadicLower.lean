import HilbertUMD.Foundations.Matrices
import HilbertUMD.Foundations.Geometry

/-! The finite dyadic witness for the signed matrix lower bound. -/

noncomputable section
open scoped BigOperators
namespace HilbertUMD

/-- The block containing `i` after revealing `k` binary digits. -/
def dyadicBlock : (n k : ℕ) → Leaf n → Finset (Leaf n)
  | _, 0, _ => Finset.univ
  | 0, _ + 1, _ => Finset.univ
  | n + 1, k + 1, Sum.inl i => (dyadicBlock n k i).map Function.Embedding.inl
  | n + 1, k + 1, Sum.inr i => (dyadicBlock n k i).map Function.Embedding.inr

theorem card_dyadicBlock (n k : ℕ) (i : Leaf n) :
    (dyadicBlock n k i).card = 2 ^ (n - k) := by
  induction n generalizing k with
  | zero => cases k <;> simp [dyadicBlock, Leaf]
  | succ n ih =>
    cases k with
    | zero => simp [dyadicBlock, card_leaf, pow_succ, Nat.mul_two]
    | succ k => cases i <;> simp [dyadicBlock, ih]

theorem mem_dyadicBlock_self (n k : ℕ) (i : Leaf n) : i ∈ dyadicBlock n k i := by
  induction n generalizing k with
  | zero => cases k <;> simp [dyadicBlock, Subsingleton.elim i (0 : Fin 1)]
  | succ n ih => cases k <;> cases i <;> simp [dyadicBlock, ih]

theorem dyadicBlock_terminal (n : ℕ) (i : Leaf n) : dyadicBlock n n i = {i} := by
  induction n with
  | zero => simp [dyadicBlock, Leaf, Subsingleton.elim i (0 : Fin 1)]
  | succ n ih => cases i <;> simp [dyadicBlock, ih]

theorem dyadicBlock_eq_of_mem (n k : ℕ) (i j : Leaf n) (h : j ∈ dyadicBlock n k i) :
    dyadicBlock n k j = dyadicBlock n k i := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      cases i <;> cases j <;> simp only [dyadicBlock, Finset.mem_map,
        Function.Embedding.inl_apply, Function.Embedding.inr_apply,
        Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, exists_false,
        and_false, exists_eq_right] at h ⊢
      all_goals first | contradiction | rw [ih k _ _ h]

theorem dyadicBlock_subset (n k l : ℕ) (hkl : k ≤ l) (i : Leaf n) :
    dyadicBlock n l i ⊆ dyadicBlock n k i := by
  induction n generalizing k l with
  | zero => cases k <;> cases l <;> exact Finset.Subset.refl _
  | succ n ih =>
    cases k with
    | zero => exact Finset.subset_univ _
    | succ k =>
      cases l with
      | zero => omega
      | succ l =>
        cases i <;> exact Finset.map_subset_map.mpr (ih k l (by omega) _)

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Finite conditional averaging on the partition into depth-`k` dyadic blocks. -/
def leafAverage {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    (n k : ℕ) (f : Leaf n → E) (i : Leaf n) : E :=
  ((dyadicBlock n k i).card : 𝕜)⁻¹ • ∑ j ∈ dyadicBlock n k i, f j

theorem leafAverage_eq_of_mem {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    (n k : ℕ) (f : Leaf n → E) (i j : Leaf n) (h : j ∈ dyadicBlock n k i) :
    leafAverage (𝕜 := 𝕜) n k f j = leafAverage (𝕜 := 𝕜) n k f i := by
  simp only [leafAverage, dyadicBlock_eq_of_mem n k i j h]

@[simp] theorem leafAverage_succ_inl {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    (n k : ℕ) (f : Leaf (n + 1) → E) (i : Leaf n) :
    leafAverage (𝕜 := 𝕜) (n + 1) (k + 1) f (Sum.inl i) =
      leafAverage (𝕜 := 𝕜) n k (fun j => f (Sum.inl j)) i := by
  simp [leafAverage, dyadicBlock, Finset.sum_map]

@[simp] theorem leafAverage_succ_inr {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    (n k : ℕ) (f : Leaf (n + 1) → E) (i : Leaf n) :
    leafAverage (𝕜 := 𝕜) (n + 1) (k + 1) f (Sum.inr i) =
      leafAverage (𝕜 := 𝕜) n k (fun j => f (Sum.inr j)) i := by
  simp [leafAverage, dyadicBlock, Finset.sum_map]

@[simp] theorem leafAverage_zero_depth {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    (k : ℕ) (f : Leaf 0 → E) (i : Leaf 0) :
    leafAverage (𝕜 := 𝕜) 0 k f i = f i := by
  cases k <;> simp [leafAverage, dyadicBlock, Leaf, Subsingleton.elim i (0 : Fin 1)]

theorem sum_leafAverage {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    (n k : ℕ) (f : Leaf n → E) :
    ∑ i, leafAverage (𝕜 := 𝕜) n k f i = ∑ i, f i := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero =>
      simp only [leafAverage, dyadicBlock, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul]
      rw [mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero :
        (Fintype.card (Leaf (n + 1)) : 𝕜) ≠ 0), one_smul]
    | succ k =>
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [leafAverage_succ_inl, leafAverage_succ_inr]
      rw [ih, ih]

/-- The finite tower identity: averaging a later conditional average at an earlier
dyadic level gives the earlier conditional average. -/
theorem leafAverage_tower {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    (n k l : ℕ) (hkl : k ≤ l) (f : Leaf n → E) (i : Leaf n) :
    leafAverage (𝕜 := 𝕜) n k (leafAverage (𝕜 := 𝕜) n l f) i =
      leafAverage (𝕜 := 𝕜) n k f i := by
  induction n generalizing k l with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero =>
      change ((Fintype.card (Leaf (n + 1)) : 𝕜)⁻¹) •
        (∑ j, leafAverage (𝕜 := 𝕜) (n + 1) l f j) = _
      rw [sum_leafAverage]
      rfl
    | succ k =>
      cases l with
      | zero => omega
      | succ l =>
        cases i with
        | inl i =>
          simp only [leafAverage_succ_inl]
          exact ih k l (by omega) _ i
        | inr i =>
          simp only [leafAverage_succ_inr]
          exact ih k l (by omega) _ i

@[simp] theorem leafAverage_terminal {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    (n : ℕ) (f : Leaf n → E) (i : Leaf n) : leafAverage (𝕜 := 𝕜) n n f i = f i := by
  simp [leafAverage, dyadicBlock_terminal]

/-- The normalized average of the coordinate-vector witness over a dyadic block. -/
def basisAverage (n k : ℕ) (i : Leaf n) : Vec 𝕜 n :=
  fun j => if j ∈ dyadicBlock n k i then ((2 : 𝕜) ^ (n - k))⁻¹ else 0

theorem basisAverage_eq_sum (n k : ℕ) (i : Leaf n) :
    basisAverage (𝕜 := 𝕜) n k i =
      ((dyadicBlock n k i).card : 𝕜)⁻¹ • ∑ j ∈ dyadicBlock n k i, basisVec j := by
  ext j
  simp [basisAverage, card_dyadicBlock, basisVec, Finset.sum_apply,
    Finset.sum_ite_eq, Pi.smul_apply, smul_eq_mul]

@[simp] theorem basisAverage_terminal (n : ℕ) (i : Leaf n) :
    basisAverage (𝕜 := 𝕜) n n i = basisVec i := by
  ext j
  simp [basisAverage, dyadicBlock_terminal, basisVec]

@[simp] theorem left_basisAverage_inl (n k : ℕ) (i : Leaf n) :
    left (basisAverage (𝕜 := 𝕜) (n + 1) (k + 1) (Sum.inl i)) = basisAverage n k i := by
  ext j
  simp [left, basisAverage, dyadicBlock]

@[simp] theorem right_basisAverage_inl (n k : ℕ) (i : Leaf n) :
    right (basisAverage (𝕜 := 𝕜) (n + 1) (k + 1) (Sum.inl i)) = 0 := by
  ext j
  simp [right, basisAverage, dyadicBlock]

@[simp] theorem left_basisAverage_inr (n k : ℕ) (i : Leaf n) :
    left (basisAverage (𝕜 := 𝕜) (n + 1) (k + 1) (Sum.inr i)) = 0 := by
  ext j
  simp [left, basisAverage, dyadicBlock]

@[simp] theorem right_basisAverage_inr (n k : ℕ) (i : Leaf n) :
    right (basisAverage (𝕜 := 𝕜) (n + 1) (k + 1) (Sum.inr i)) = basisAverage n k i := by
  ext j
  simp [right, basisAverage, dyadicBlock]

/-- The common normalized row sum of the signed dyadic matrix. -/
def dyadicRowMean : ℕ → 𝕜
  | 0 => 1
  | n + 1 => (dyadicRowMean n + (-1 : 𝕜) ^ (n + 1)) / 2

theorem dyadicRowMean_explicit (n : ℕ) :
    dyadicRowMean (𝕜 := 𝕜) n = ((-1 : 𝕜) ^ n + 2 / 2 ^ n) / 3 := by
  induction n with
  | zero => norm_num [dyadicRowMean]
  | succ n ih =>
    rw [dyadicRowMean, ih]
    simp only [pow_succ]
    field_simp
    ring

theorem signedDyadic_constant (n : ℕ) (c : 𝕜) (i : Leaf n) :
    signedDyadic n (fun _ => c) i = 2 ^ n * c * dyadicRowMean n := by
  induction n with
  | zero => simp [signedDyadic, dyadicRowMean]
  | succ n ih =>
    cases i with
    | inl i =>
      change signedDyadic n (fun _ => c) i + (-1 : 𝕜) ^ (n + 1) * total (fun _ : Leaf n => c) = _
      rw [ih]
      simp [total, card_leaf, dyadicRowMean, pow_succ]
      ring
    | inr i =>
      change (-1 : 𝕜) ^ (n + 1) * total (fun _ : Leaf n => c) + signedDyadic n (fun _ => c) i = _
      rw [ih]
      simp [total, card_leaf, dyadicRowMean, pow_succ]
      ring

theorem signedDyadic_basisAverage_diagonal (n k : ℕ) (hk : k ≤ n) (i : Leaf n) :
    signedDyadic n (basisAverage (𝕜 := 𝕜) n k i) i = dyadicRowMean (n - k) := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp [basisAverage, dyadicBlock, signedDyadic, dyadicRowMean,
      Subsingleton.elim i (0 : Fin 1)]
  | succ n ih =>
    cases k with
    | zero =>
      have hav : basisAverage (𝕜 := 𝕜) (n + 1) 0 i = fun _ => (2 ^ (n + 1) : 𝕜)⁻¹ := by
        ext j
        simp [basisAverage, dyadicBlock]
      rw [hav]
      rw [signedDyadic_constant]
      simp
    | succ k =>
      have hk' : k ≤ n := by omega
      cases i with
      | inl i =>
        change signedDyadic n (left _) i + (-1 : 𝕜) ^ (n + 1) * total (right _) = _
        rw [left_basisAverage_inl, right_basisAverage_inl, total_zero, mul_zero, add_zero]
        simpa using ih k hk' i
      | inr i =>
        change (-1 : 𝕜) ^ (n + 1) * total (left _) + signedDyadic n (right _) i = _
        rw [left_basisAverage_inr, right_basisAverage_inr, total_zero, mul_zero, zero_add]
        simpa using ih k hk' i

theorem dyadicRowMean_signed_difference (h : ℕ) :
    (-1 : 𝕜) ^ h * (dyadicRowMean h - dyadicRowMean (h + 1)) =
      2 / 3 + (-1 / 2 : 𝕜) ^ h / 3 := by
  rw [dyadicRowMean_explicit, dyadicRowMean_explicit]
  have hs : ((-1 : 𝕜) ^ h) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    simp
  simp only [pow_succ, div_pow]
  field_simp
  linear_combination 2 * (2 : 𝕜) ^ h * hs

theorem dyadicRowMean_alternating_sum (n : ℕ) :
    (∑ h ∈ Finset.range n, (-1 : 𝕜) ^ h *
      (dyadicRowMean h - dyadicRowMean (h + 1))) =
      2 * (n : 𝕜) / 3 + 2 / 9 * (1 - (-1 / 2 : 𝕜) ^ n) := by
  simp_rw [dyadicRowMean_signed_difference]
  rw [Finset.sum_add_distrib]
  simp_rw [← Finset.sum_div]
  rw [geom_sum_eq (by norm_num : (-1 / 2 : 𝕜) ≠ 1)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The alternating martingale transform of the coordinate-vector witness.
The sum runs from fine to coarse; `alternatingWitness_forward` gives chronological order. -/
def alternatingWitness (n : ℕ) (i : Leaf n) : Vec 𝕜 n :=
  ∑ h ∈ Finset.range n, (-1 : 𝕜) ^ h •
    (basisAverage n (n - h) i - basisAverage n (n - (h + 1)) i)

theorem alternatingWitness_forward (n : ℕ) (i : Leaf n) :
    alternatingWitness (𝕜 := 𝕜) n i =
      ∑ k ∈ Finset.range n, (-1 : 𝕜) ^ (n - (k + 1)) •
        (basisAverage n (k + 1) i - basisAverage n k i) := by
  rw [alternatingWitness, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have he : n - 1 - k = n - (k + 1) := by omega
  have hl : n - (n - 1 - k) = k + 1 := by omega
  have hr : n - (n - 1 - k + 1) = k := by omega
  rw [hl, hr, he]

theorem signedDyadic_alternatingWitness_diagonal (n : ℕ) (i : Leaf n) :
    signedDyadic n (alternatingWitness (𝕜 := 𝕜) n i) i =
      2 * (n : 𝕜) / 3 + 2 / 9 * (1 - (-1 / 2 : 𝕜) ^ n) := by
  change (signedDyadicLinear n) (alternatingWitness n i) i = _
  rw [alternatingWitness, map_sum]
  simp only [Finset.sum_apply, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [← dyadicRowMean_alternating_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hh' := Finset.mem_range.mp hh
  change (-1 : 𝕜) ^ h * (signedDyadic n (basisAverage n (n - h) i) i -
    signedDyadic n (basisAverage n (n - (h + 1)) i) i) = _
  rw [signedDyadic_basisAverage_diagonal n (n-h) (by omega),
    signedDyadic_basisAverage_diagonal n (n-(h+1)) (by omega)]
  congr 3 <;> omega

/-- The L2 norm for the uniform probability measure on the binary leaves,
written as a finite normalized sum. -/
def leafL2Norm {E : Type*} [Norm E] (n : ℕ) (f : Leaf n → E) : ℝ :=
  Real.sqrt ((2 : ℝ)⁻¹ ^ n * ∑ i, ‖f i‖ ^ 2)

theorem leafL2Norm_ge_of_pointwise {E : Type*} [SeminormedAddCommGroup E]
    (n : ℕ) (f : Leaf n → E) (c : ℝ) (hc : 0 ≤ c) (hf : ∀ i, c ≤ ‖f i‖) :
    c ≤ leafL2Norm n f := by
  have hs : (Fintype.card (Leaf n) : ℝ) * c ^ 2 ≤ ∑ i, ‖f i‖ ^ 2 := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => pow_le_pow_left₀ hc (hf i) 2)
  rw [card_leaf, Nat.cast_pow, Nat.cast_ofNat] at hs
  have hp : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  have hm := mul_le_mul_of_nonneg_left hs hp
  have hcancel : (2 : ℝ)⁻¹ ^ n * ((2 : ℝ) ^ n * c ^ 2) = c ^ 2 := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [hcancel] at hm
  exact (Real.le_sqrt hc (by positivity)).mpr hm

/-- The terminal witness in counting-measure l1. -/
def l1BasisWitness (n : ℕ) (i : Leaf n) : L1Vec 𝕜 n := WithLp.toLp 1 (basisVec i)

theorem ofLp_leafAverage_l1BasisWitness (n k : ℕ) (i : Leaf n) :
    WithLp.ofLp (leafAverage (𝕜 := 𝕜) n k (l1BasisWitness n) i) =
      basisAverage (𝕜 := 𝕜) n k i := by
  rw [basisAverage_eq_sum]
  simp [leafAverage, WithLp.ofLp_sum, l1BasisWitness]

@[simp] theorem norm_l1BasisWitness (n : ℕ) (i : Leaf n) :
    ‖l1BasisWitness (𝕜 := 𝕜) n i‖ = 1 := by
  rw [PiLp.norm_eq_of_L1]
  exact l1Norm_basisVec i

theorem leafL2Norm_l1BasisWitness (n : ℕ) :
    leafL2Norm n (l1BasisWitness (𝕜 := 𝕜) n) = 1 := by
  simp only [leafL2Norm, norm_l1BasisWitness, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, card_leaf, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

end HilbertUMD
