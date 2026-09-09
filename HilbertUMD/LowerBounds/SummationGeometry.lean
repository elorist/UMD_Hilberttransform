import HilbertUMD.Foundations.Matrices
import HilbertUMD.Foundations.Geometry

/-! The recursive summation matrix in the manuscript's ordered coordinates. -/

noncomputable section
open scoped BigOperators

namespace HilbertUMD

variable {𝕜 : Type*} [RCLike 𝕜]

theorem summation_eq_initial_sum (n : ℕ) (x : Vec 𝕜 n) (i : Leaf n) :
    summation n x i =
      ∑ j : Leaf n, if (leafEquivFin n j).val ≤ (leafEquivFin n i).val then x j else 0 := by
  induction n with
  | zero =>
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp [summation, leafEquivFin]
  | succ n ih =>
    rcases i with i | i
    · change summation n (left x) i = _
      rw [Fintype.sum_sum_type, ih]
      change (∑ j : Leaf n, if (leafEquivFin n j).val ≤ (leafEquivFin n i).val
        then x (Sum.inl j) else 0) =
        (∑ j : Leaf n, if (leafEquivFin n j).val ≤ (leafEquivFin n i).val
          then x (Sum.inl j) else 0) +
        ∑ j : Leaf n, if 2 ^ n + (leafEquivFin n j).val ≤ (leafEquivFin n i).val
          then x (Sum.inr j) else 0
      have hr : ∀ j : Leaf n, ¬(2 ^ n + (leafEquivFin n j).val ≤ (leafEquivFin n i).val) := by
        intro j
        have hi := (leafEquivFin n i).isLt
        omega
      simp only [hr, if_false, Finset.sum_const_zero, add_zero]
    · change total (left x) + summation n (right x) i = _
      rw [Fintype.sum_sum_type, ih]
      change (∑ j : Leaf n, x (Sum.inl j)) +
        (∑ j : Leaf n, if (leafEquivFin n j).val ≤ (leafEquivFin n i).val
          then x (Sum.inr j) else 0) =
        (∑ j : Leaf n, if (leafEquivFin n j).val ≤ 2 ^ n + (leafEquivFin n i).val
          then x (Sum.inl j) else 0) +
        ∑ j : Leaf n, if 2 ^ n + (leafEquivFin n j).val ≤ 2 ^ n + (leafEquivFin n i).val
          then x (Sum.inr j) else 0
      have hl : ∀ j : Leaf n, (leafEquivFin n j).val ≤ 2 ^ n + (leafEquivFin n i).val := by
        intro j
        have hj := (leafEquivFin n j).isLt
        omega
      simp only [hl, if_true, Nat.add_le_add_iff_left]

theorem summation_basisVec_entry (n : ℕ) (i j : Leaf n) :
    summation n (basisVec j : Vec 𝕜 n) i =
      if (leafEquivFin n j).val ≤ (leafEquivFin n i).val then 1 else 0 := by
  classical
  rw [summation_eq_initial_sum]
  rw [Finset.sum_eq_single j]
  · simp [basisVec]
  · intro k _ hkj
    simp [basisVec, hkj]
  · simp

end HilbertUMD
