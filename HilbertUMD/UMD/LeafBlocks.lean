import HilbertUMD.UMD.DyadicSampled

/-! Splitting a uniform binary tree into a prefix block and a remaining tree. -/

noncomputable section
open scoped BigOperators

namespace HilbertUMD

def leafSplit : (p q : ℕ) → Leaf (q + p) ≃ Leaf p × Leaf q
  | 0, q => (Equiv.uniqueProd (Leaf q) (Leaf 0)).symm
  | p + 1, q => (Equiv.sumCongr (leafSplit p q) (leafSplit p q)).trans
      (Equiv.sumProdDistrib (Leaf p) (Leaf p) (Leaf q)).symm

@[simp] theorem leafSplit_zero (q : ℕ) (x : Leaf q) :
    leafSplit 0 q x = (0, x) := rfl

@[simp] theorem leafSplit_inl (p q : ℕ) (x : Leaf (q + p)) :
    leafSplit (p + 1) q (Sum.inl x) = (Sum.inl (leafSplit p q x).1, (leafSplit p q x).2) := rfl

@[simp] theorem leafSplit_inr (p q : ℕ) (x : Leaf (q + p)) :
    leafSplit (p + 1) q (Sum.inr x) = (Sum.inr (leafSplit p q x).1, (leafSplit p q x).2) := rfl

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

def leafMean (n : ℕ) (f : Leaf n → E) : E :=
  ((2 : 𝕜) ^ n)⁻¹ • ∑ i, f i

theorem leafMean_const (n : ℕ) (x : E) : leafMean (𝕜 := 𝕜) n (fun _ => x) = x := by
  simp [leafMean, ← Nat.cast_smul_eq_nsmul 𝕜, card_leaf, smul_smul]

theorem leafMean_add (n : ℕ) (f g : Leaf n → E) :
    leafMean (𝕜 := 𝕜) n (fun i => f i + g i) = leafMean (𝕜 := 𝕜) n f + leafMean (𝕜 := 𝕜) n g := by
  simp [leafMean, Finset.sum_add_distrib, smul_add]

theorem leafMean_sub (n : ℕ) (f g : Leaf n → E) :
    leafMean (𝕜 := 𝕜) n (fun i => f i - g i) = leafMean (𝕜 := 𝕜) n f - leafMean (𝕜 := 𝕜) n g := by
  simp [leafMean, Finset.sum_sub_distrib, smul_sub]

theorem leafMean_smul_const (n : ℕ) (f : Leaf n → 𝕜) (x : E) :
    leafMean (𝕜 := 𝕜) n (fun i => f i • x) = leafMean (𝕜 := 𝕜) n f • x := by
  simp [leafMean, ← Finset.sum_smul, smul_smul, smul_eq_mul]

theorem leafAverage_real [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    (n k : ℕ) (f : Leaf n → E) (i : Leaf n) :
    leafAverage (𝕜 := 𝕜) n k f i = leafAverage (𝕜 := ℝ) n k f i := by
  simp only [leafAverage, RCLike.real_smul_eq_coe_smul (K := 𝕜),
    RCLike.ofReal_inv, RCLike.ofReal_natCast]

theorem leafAverage_zero_mean (n : ℕ) (f : Leaf n → E) (i : Leaf n) :
    leafAverage (𝕜 := 𝕜) n 0 f i = leafMean (𝕜 := 𝕜) n f := by
  simp [leafAverage, dyadicBlock, leafMean, card_leaf]

theorem leafMean_split (p q : ℕ) (f : Leaf p → Leaf q → E) :
    leafMean (𝕜 := 𝕜) (q + p) (fun x => f (leafSplit p q x).1 (leafSplit p q x).2) =
      leafMean (𝕜 := 𝕜) p (fun a => leafMean (𝕜 := 𝕜) q (f a)) := by
  unfold leafMean
  rw [(leafSplit p q).sum_comp (fun x => f x.1 x.2), Fintype.sum_prod_type]
  simp only [← Finset.smul_sum, smul_smul]
  congr 1
  rw [pow_add, mul_inv_rev]

theorem leafAverage_split (p q k : ℕ) (f : Leaf p → Leaf q → E)
    (x : Leaf (q + p)) :
    leafAverage (𝕜 := 𝕜) (q + p) (p + k)
      (fun y => f (leafSplit p q y).1 (leafSplit p q y).2) x =
    leafAverage (𝕜 := 𝕜) q k (f (leafSplit p q x).1) (leafSplit p q x).2 := by
  induction p with
  | zero => simp only [Nat.zero_add]; rfl
  | succ p ih =>
    cases x with
    | inl x =>
      rw [Nat.succ_add]
      change leafAverage (𝕜 := 𝕜) ((q + p) + 1) ((p + k) + 1) _ (Sum.inl x) = _
      rw [leafAverage_succ_inl]
      exact ih (fun a b => f (Sum.inl a) b) x
    | inr x =>
      rw [Nat.succ_add]
      change leafAverage (𝕜 := 𝕜) ((q + p) + 1) ((p + k) + 1) _ (Sum.inr x) = _
      rw [leafAverage_succ_inr]
      exact ih (fun a b => f (Sum.inr a) b) x

end HilbertUMD
