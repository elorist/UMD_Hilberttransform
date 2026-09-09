import HilbertUMD.UMD.LeafBlocks

/-! Binary coordinates and the sigma algebras of tree prefixes. -/

noncomputable section
open MeasureTheory

namespace HilbertUMD

def leafBits : (n : ℕ) → Leaf n → Fin n → Bool
  | 0, _ => Fin.elim0
  | n + 1, Sum.inl i => Fin.cases true (leafBits n i)
  | n + 1, Sum.inr i => Fin.cases false (leafBits n i)

def leafOfBits : (n : ℕ) → (Fin n → Bool) → Leaf n
  | 0, _ => 0
  | n + 1, b => if b 0 then Sum.inl (leafOfBits n (fun k => b k.succ))
      else Sum.inr (leafOfBits n (fun k => b k.succ))

theorem leafBits_ofBits (n : ℕ) (b : Fin n → Bool) : leafBits n (leafOfBits n b) = b := by
  induction n with
  | zero => funext k; exact Fin.elim0 k
  | succ n ih =>
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · cases h : b 0 <;> simp [leafOfBits, h, leafBits]
    · cases h : b 0 <;> simp [leafOfBits, h, leafBits, ih]

theorem mem_dyadicBlock_iff_bits (n k : ℕ) (i j : Leaf n) :
    j ∈ dyadicBlock n k i ↔ ∀ a : Fin n, a.val < k → leafBits n i a = leafBits n j a := by
  induction n generalizing k with
  | zero =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    cases k <;> simp [dyadicBlock]
  | succ n ih =>
    cases k with
    | zero => simp [dyadicBlock]
    | succ k =>
      cases i <;> cases j <;>
        simp [dyadicBlock, Fin.forall_fin_succ, leafBits, ih]

theorem measurable_leafBits (n k : ℕ) (a : Fin n) (ha : a.val < k) :
    Measurable[dyadicMeasurableSpace n k] (fun i => leafBits n i a) := by
  intro s _ i j hij
  change leafBits n i a ∈ s ↔ leafBits n j a ∈ s
  rw [(mem_dyadicBlock_iff_bits n k i j).mp hij a ha]

theorem measurable_leafOfBits_prefix {Ω : Type*} [MeasurableSpace Ω]
    (n k : ℕ) (b : Ω → Fin n → Bool)
    (hb : ∀ a : Fin n, a.val < k → Measurable (fun x => b x a)) :
    Measurable[_, dyadicMeasurableSpace n k] (fun x => leafOfBits n (b x)) := by
  have hblock (i : Leaf n) : MeasurableSet {x | leafOfBits n (b x) ∈ dyadicBlock n k i} := by
    have h : MeasurableSet (⋂ a : Fin n, ⋂ (_ : a.val < k), {x | b x a = leafBits n i a}) := by
      apply MeasurableSet.iInter
      intro a
      apply MeasurableSet.iInter
      intro ha
      exact (hb a ha) (measurableSet_singleton _)
    have he : {x | leafOfBits n (b x) ∈ dyadicBlock n k i} =
        ⋂ a : Fin n, ⋂ (_ : a.val < k), {x | b x a = leafBits n i a} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, mem_dyadicBlock_iff_bits,
        leafBits_ofBits, eq_comm]
    rw [he]
    exact h
  intro s hs
  have he : (fun x => leafOfBits n (b x)) ⁻¹' s =
      ⋃ i ∈ s, {x | leafOfBits n (b x) ∈ dyadicBlock n k i} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨leafOfBits n (b x), hx, mem_dyadicBlock_self _ _ _⟩
    · rintro ⟨i, hi, hx⟩
      exact (hs i (leafOfBits n (b x)) hx).mp hi
  rw [he]
  exact MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hblock i))

theorem dyadicMeasurableSpace_terminal (n : ℕ) :
    dyadicMeasurableSpace n n = leafMeasurableSpace n := by
  apply le_antisymm le_top
  intro s _ i j hij
  rw [dyadicBlock_terminal, Finset.mem_singleton] at hij
  subst j
  rfl

theorem measurable_leafOfBits {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (b : Ω → Fin n → Bool) (hb : ∀ a, Measurable (fun x => b x a)) :
    Measurable (fun x => leafOfBits n (b x)) := by
  rw [← dyadicMeasurableSpace_terminal n]
  exact measurable_leafOfBits_prefix n n b (fun a _ => hb a)

end HilbertUMD
