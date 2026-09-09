import HilbertUMD.UMD.WeightedBinaryTree

/-! Realization of dyadic branching probabilities by uniform binary blocks. -/

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace HilbertUMD.WeightedTree

def branchProbability (L : ℕ) (s : Leaf L → Bool) : ℝ :=
  leafMean (𝕜 := ℝ) L (fun x => if s x then 1 else 0)

theorem leafMean_select {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : ℕ) (s : Leaf L → Bool) (x y : E) :
    leafMean (𝕜 := ℝ) L (fun a => if s a then x else y) =
      branchProbability L s • x + (1 - branchProbability L s) • y := by
  let mark : Leaf L → ℝ := fun a => if s a then 1 else 0
  have he : (fun a => if s a then x else y) =
      (fun a => mark a • x + (1 - mark a) • y) := by
    funext a
    cases hs : s a <;> simp [mark, hs]
  rw [he, leafMean_add, leafMean_smul_const, leafMean_smul_const,
    leafMean_sub, leafMean_const]
  rfl

theorem leafMean_ite {E : Type*} [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (b : Bool) (f g : Leaf n → E) :
    leafMean (𝕜 := ℝ) n (fun x => if b then f x else g x) =
      if b then leafMean (𝕜 := ℝ) n f else leafMean (𝕜 := ℝ) n g := by
  cases b <;> rfl

abbrev Code (L n : ℕ) := Node n → Leaf L → Bool

def bias {L n : ℕ} (s : Code L n) : Bias n := fun a => branchProbability L (s a)

@[simp] theorem bias_left {L n : ℕ} (s : Code L (n + 1)) : left (bias s) = bias (left s) := rfl
@[simp] theorem bias_right {L n : ℕ} (s : Code L (n + 1)) : right (bias s) = bias (right s) := rfl

abbrev depth (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => depth L n + L

theorem depth_eq_mul (L n : ℕ) : depth L n = L * n := by
  induction n with
  | zero => simp [depth]
  | succ n ih => simp [depth, ih, Nat.mul_succ]

theorem depth_mono (L : ℕ) : Monotone (depth L) := by
  intro a b hab
  simpa only [depth_eq_mul] using Nat.mul_le_mul_left L hab

def decode (L : ℕ) : (n : ℕ) → Code L n → Leaf (depth L n) → Leaf n
  | 0, _, i => i
  | n + 1, s, i =>
      let a := leafSplit L (depth L n) i
      if root s a.1 then Sum.inl (decode L n (left s) a.2)
      else Sum.inr (decode L n (right s) a.2)

theorem leafMean_decode {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L n : ℕ) (s : Code L n) (f : Leaf n → E) :
    leafMean (𝕜 := ℝ) (depth L n) (fun i => f (decode L n s i)) = mean n (bias s) f := by
  induction n with
  | zero =>
    simp only [depth, decode, leafMean, mean, pow_zero, inv_one, one_smul]
    exact Fin.sum_univ_one f
  | succ n ih =>
    change leafMean (𝕜 := ℝ) (depth L n + L)
      (fun i => f (if root s (leafSplit L (depth L n) i).1 then
        Sum.inl (decode L n (left s) (leafSplit L (depth L n) i).2) else
        Sum.inr (decode L n (right s) (leafSplit L (depth L n) i).2))) = _
    simp only [apply_ite]
    rw [leafMean_split L (depth L n) (fun a b => if root s a then
      f (Sum.inl (decode L n (left s) b)) else f (Sum.inr (decode L n (right s) b)))]
    simp_rw [leafMean_ite,
      ih (left s) (fun j => f (Sum.inl j)), ih (right s) (fun j => f (Sum.inr j))]
    rw [leafMean_select]
    rfl

theorem leafAverage_decode {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L n k : ℕ) (hk : k ≤ n) (s : Code L n) (f : Leaf n → E) (i : Leaf (depth L n)) :
    leafAverage (𝕜 := ℝ) (depth L n) (depth L k) (fun j => f (decode L n s j)) i =
      average n (bias s) k f (decode L n s i) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    change leafAverage (𝕜 := ℝ) 0 0 f i = f 0
    rw [leafAverage_zero_depth]
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    cases k with
    | zero =>
      rw [show depth L 0 = 0 from rfl, leafAverage_zero_mean, leafMean_decode]
      rfl
    | succ k =>
      change leafAverage (𝕜 := ℝ) (depth L n + L) (depth L k + L)
        (fun j => f (if root s (leafSplit L (depth L n) j).1 then
          Sum.inl (decode L n (left s) (leafSplit L (depth L n) j).2) else
          Sum.inr (decode L n (right s) (leafSplit L (depth L n) j).2))) i = _
      simp only [apply_ite]
      rw [Nat.add_comm (depth L k) L,
        leafAverage_split L (depth L n) (depth L k) (fun a b => if root s a then
          f (Sum.inl (decode L n (left s) b)) else f (Sum.inr (decode L n (right s) b)))]
      cases hs : root s (leafSplit L (depth L n) i).1 with
      | false =>
        simpa only [hs, Bool.false_eq_true, if_false, decode, average, bias_right] using
          ih k (by omega) (right s) (fun j => f (Sum.inr j)) (leafSplit L (depth L n) i).2
      | true =>
        simpa only [hs, if_true, decode, average, bias_left] using
          ih k (by omega) (left s) (fun j => f (Sum.inl j)) (leafSplit L (depth L n) i).2

end HilbertUMD.WeightedTree
