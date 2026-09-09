import HilbertUMD.UMD.LeafBlocks

/-! Finite binary trees with arbitrary branching probabilities. -/

noncomputable section
open scoped BigOperators

namespace HilbertUMD.WeightedTree

abbrev Node : ℕ → Type
  | 0 => PEmpty
  | n + 1 => Unit ⊕ (Node n ⊕ Node n)

instance nodeFintype : (n : ℕ) → Fintype (Node n)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | n + 1 => by
    letI := nodeFintype n
    exact inferInstanceAs (Fintype (Unit ⊕ (Node n ⊕ Node n)))

abbrev Bias (n : ℕ) := Node n → ℝ

def left {n : ℕ} {A : Type*} (b : Node (n + 1) → A) : Node n → A :=
  fun i => b (Sum.inr (Sum.inl i))

def right {n : ℕ} {A : Type*} (b : Node (n + 1) → A) : Node n → A :=
  fun i => b (Sum.inr (Sum.inr i))

def root {n : ℕ} {A : Type*} (b : Node (n + 1) → A) : A := b (Sum.inl ())

def Valid {n : ℕ} (b : Bias n) : Prop := ∀ i, 0 ≤ b i ∧ b i ≤ 1

theorem Valid.left {n : ℕ} {b : Bias (n + 1)} (h : Valid b) : Valid (left b) :=
  fun i => h (Sum.inr (Sum.inl i))

theorem Valid.right {n : ℕ} {b : Bias (n + 1)} (h : Valid b) : Valid (right b) :=
  fun i => h (Sum.inr (Sum.inr i))

theorem Valid.root {n : ℕ} {b : Bias (n + 1)} (h : Valid b) : 0 ≤ root b ∧ root b ≤ 1 :=
  h _

def mass : (n : ℕ) → Bias n → Leaf n → ℝ
  | 0, _, _ => 1
  | n + 1, b, Sum.inl i => root b * mass n (left b) i
  | n + 1, b, Sum.inr i => (1 - root b) * mass n (right b) i

theorem sum_mass (n : ℕ) (b : Bias n) : ∑ i, mass n b i = 1 := by
  induction n with
  | zero => simp [mass, Leaf]
  | succ n ih =>
    rw [Fintype.sum_sum_type]
    simp only [mass, ← Finset.mul_sum, ih, mul_one]
    ring

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def mean : (n : ℕ) → Bias n → (Leaf n → E) → E
  | 0, _, f => f 0
  | n + 1, b, f => root b • mean n (left b) (fun i => f (Sum.inl i)) +
      (1 - root b) • mean n (right b) (fun i => f (Sum.inr i))

theorem mean_eq_sum (n : ℕ) (b : Bias n) (f : Leaf n → E) :
    mean n b f = ∑ i, mass n b i • f i := by
  induction n with
  | zero => simp [mean, mass, Leaf]
  | succ n ih =>
    simp only [mean, Fintype.sum_sum_type, mass, mul_smul, ih, Finset.smul_sum]

theorem mean_const (n : ℕ) (b : Bias n) (x : E) : mean n b (fun _ => x) = x := by
  rw [mean_eq_sum, ← Finset.sum_smul, sum_mass, one_smul]

def average : (n : ℕ) → Bias n → ℕ → (Leaf n → E) → Leaf n → E
  | n, b, 0, f, _ => mean n b f
  | 0, _, _ + 1, f, i => f i
  | n + 1, b, k + 1, f, Sum.inl i => average n (left b) k (fun j => f (Sum.inl j)) i
  | n + 1, b, k + 1, f, Sum.inr i => average n (right b) k (fun j => f (Sum.inr j)) i

theorem mean_average (n : ℕ) (b : Bias n) (k : ℕ) (f : Leaf n → E) :
    mean n b (average n b k f) = mean n b f := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => exact mean_const _ _ _
    | succ k => simp only [mean, average, ih]

theorem average_eq_of_mem (n k : ℕ) (b : Bias n) (f : Leaf n → E)
    (i j : Leaf n) (h : j ∈ dyadicBlock n k i) :
    average n b k f i = average n b k f j := by
  induction n generalizing k with
  | zero => exact congrArg (average 0 b k f) (Subsingleton.elim _ _)
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      cases i <;> cases j <;>
        simp only [dyadicBlock, Finset.mem_map, Function.Embedding.inl_apply,
          Function.Embedding.inr_apply, Sum.inl.injEq, Sum.inr.injEq,
          Sum.inl_ne_inr, Sum.inr_ne_inl, exists_false, and_false] at h
      · obtain ⟨a, ha, rfl⟩ := h
        exact ih k _ _ _ _ ha
      · obtain ⟨a, ha, rfl⟩ := h
        exact ih k _ _ _ _ ha

section Continuity

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem continuous_left (n : ℕ) : Continuous (left : Bias (n + 1) → Bias n) :=
  continuous_pi (fun _ => continuous_apply _)

theorem continuous_right (n : ℕ) : Continuous (right : Bias (n + 1) → Bias n) :=
  continuous_pi (fun _ => continuous_apply _)

theorem continuous_root (n : ℕ) : Continuous (root : Bias (n + 1) → ℝ) :=
  continuous_apply _

theorem continuous_mass (n : ℕ) (i : Leaf n) : Continuous (fun b : Bias n => mass n b i) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    cases i with
    | inl i => exact (continuous_root n).mul ((ih i).comp (continuous_left n))
    | inr i => exact (continuous_const.sub (continuous_root n)).mul ((ih i).comp (continuous_right n))

theorem continuous_mean (n : ℕ) (f : Leaf n → E) : Continuous (fun b : Bias n => mean n b f) := by
  simp only [mean_eq_sum]
  exact continuous_finsetSum _ (fun i _ => (continuous_mass n i).smul continuous_const)

theorem continuous_average (n k : ℕ) (f : Leaf n → E) (i : Leaf n) :
    Continuous (fun b : Bias n => average n b k f i) := by
  induction n generalizing k with
  | zero => cases k <;> exact continuous_const
  | succ n ih =>
    cases k with
    | zero => exact continuous_mean _ _
    | succ k =>
      cases i with
      | inl i => exact (ih k _ i).comp (continuous_left n)
      | inr i => exact (ih k _ i).comp (continuous_right n)

end Continuity

end HilbertUMD.WeightedTree
