import HilbertUMD.UMD.DyadicTerminal
import HilbertUMD.Analysis.MixedNorm

/-! Actual independent signs on the uniform binary leaf space and the
finite Rademacher estimates used in the martingale-product proof. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace HilbertUMD

/-- The kth binary digit of the leaf, encoded as a real sign. -/
def leafSign : (n : ℕ) → Fin n → Leaf n → ℝ
  | 0, k, _ => Fin.elim0 k
  | n + 1, k, Sum.inl x => Fin.cases 1 (fun j => leafSign n j x) k
  | n + 1, k, Sum.inr x => Fin.cases (-1) (fun j => leafSign n j x) k

/-- An actual finite Rademacher sum, not a norm introduced by definition. -/
def leafRademacherSum (n : ℕ) (c : Fin n → ℝ) (x : Leaf n) : ℝ :=
  ∑ k : Fin n, leafSign n k x * c k

@[simp] theorem leafRademacherSum_inl (n : ℕ) (c : Fin (n + 1) → ℝ) (x : Leaf n) :
    leafRademacherSum (n + 1) c (Sum.inl x) = c 0 + leafRademacherSum n (fun k => c k.succ) x := by
  rw [leafRademacherSum, Fin.sum_univ_succ]
  simp [leafSign, leafRademacherSum]

@[simp] theorem leafRademacherSum_inr (n : ℕ) (c : Fin (n + 1) → ℝ) (x : Leaf n) :
    leafRademacherSum (n + 1) c (Sum.inr x) = -c 0 + leafRademacherSum n (fun k => c k.succ) x := by
  rw [leafRademacherSum, Fin.sum_univ_succ]
  simp [leafSign, leafRademacherSum]

end HilbertUMD
