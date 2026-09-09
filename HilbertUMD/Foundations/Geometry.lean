import HilbertUMD.Foundations.Dyadic

noncomputable section
open scoped BigOperators
namespace HilbertUMD

/-- Number leaves from 0 to 2^n-1, with every left leaf before every right leaf.
The manuscript uses the same numbering shifted by one. -/
def leafEquivFin : (n : ℕ) → Leaf n ≃ Fin (2 ^ n)
  | 0 => Equiv.refl (Fin 1)
  | n + 1 => ((Equiv.sumCongr (leafEquivFin n) (leafEquivFin n)).trans
      finSumFinEquiv).trans (finCongr (by simp [pow_succ, Nat.mul_two] :
        2 ^ n + 2 ^ n = 2 ^ (n + 1)))

/-- The leaf subset belonging to each dyadic node. -/
def nodeLeaves : (n : ℕ) → Node n → Finset (Leaf n)
  | 0, _ => Finset.univ
  | _n + 1, Sum.inl _ => Finset.univ
  | n + 1, Sum.inr (Sum.inl a) => (nodeLeaves n a).map Function.Embedding.inl
  | n + 1, Sum.inr (Sum.inr a) => (nodeLeaves n a).map Function.Embedding.inr

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The recursive sum map really is the sum over each node's dyadic leaf block. -/
theorem blockSum_eq_sum_nodeLeaves (n : ℕ) (x : Vec 𝕜 n) (a : Node n) :
    blockSum n x a = ∑ j ∈ nodeLeaves n a, x j := by
  induction n with
  | zero =>
    have ha : a = (0 : Fin 1) := Subsingleton.elim _ _
    simp [blockSum, nodeLeaves, ha]
  | succ n ih =>
    rcases a with u | (a | a)
    · rfl
    · simpa [nodeLeaves, Finset.sum_map, blockSum, left] using ih (left x) a
    · simpa [nodeLeaves, Finset.sum_map, blockSum, right] using ih (right x) a

end HilbertUMD
