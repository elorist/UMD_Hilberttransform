import HilbertUMD.UMD.LeafBits
import HilbertUMD.UMD.FiniteFiltrationApproximation
import Mathlib.Logic.Equiv.Fin.Basic

/-! A finite filtration and a simple terminal function have an exact model on
a finite binary tree. The probability law is allowed to be arbitrary. -/

noncomputable section
open MeasureTheory

namespace HilbertUMD

theorem exists_leaf_filtration_model {Ω E : Type*} [mΩ : MeasurableSpace Ω] [Nonempty E]
    {m : ℕ} (ℱ : Filtration (Fin (m + 1)) mΩ)
    (hfinite : ∀ k, FinitelyGeneratedSigma (ℱ k)) (g : SimpleFunc Ω E) :
    ∃ (n : ℕ) (r : Fin (m + 1) → ℕ) (φ : Ω → Leaf n) (f : Leaf n → E),
      Monotone r ∧ (∀ k, r k ≤ n) ∧ Measurable φ ∧
      (∀ k, ℱ k = (dyadicMeasurableSpace n (r k)).comap φ) ∧
      (∀ x, g x = f (φ x)) := by
  classical
  choose a ha hgen using hfinite
  let A : Set (Set Ω) := (⋃ k, a k) ∪ FiniteFiltrationApproximation.fibers g
  have hA : A.Finite := (Set.finite_iUnion ha).union
    (FiniteFiltrationApproximation.fibers_finite g.finite_range)
  let : Fintype A := hA.fintype
  let B := Fintype.card A
  let e : Fin B → Set Ω := fun i => ((Fintype.equivFin A).symm i).val
  have he (s : Set Ω) (hs : s ∈ A) : ∃ i, e i = s :=
    ⟨Fintype.equivFin A ⟨s, hs⟩, by simp [e]⟩
  have hme (i : Fin B) : MeasurableSet (e i) := by
    have hi := ((Fintype.equivFin A).symm i).property
    rcases hi with hi | hi
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hi
      apply ℱ.le k
      rw [hgen k]
      exact MeasurableSpace.measurableSet_generateFrom hk
    · obtain ⟨v, _, hv⟩ := hi
      change g ⁻¹' {v} = e i at hv
      rw [← hv]
      exact g.measurableSet_fiber v
  let event (j : Fin (m + 2)) (i : Fin B) : Set Ω :=
    if hj : j.val < m + 1 then
      if MeasurableSet[ℱ ⟨j.val, hj⟩] (e i) then e i else ∅
    else e i
  have h_event (j : Fin (m + 2)) (i : Fin B) : MeasurableSet (event j i) := by
    dsimp [event]
    split_ifs <;> first | exact hme i | exact MeasurableSet.empty
  have h_stage (k : Fin (m + 1)) (j : Fin (m + 2)) (i : Fin B)
      (hjk : j.val ≤ k.val) : MeasurableSet[ℱ k] (event j i) := by
    have hj : j.val < m + 1 := lt_of_le_of_lt hjk k.isLt
    dsimp [event]
    rw [dif_pos hj]
    split_ifs with h
    · exact ℱ.mono hjk _ h
    · exact @MeasurableSet.empty Ω (ℱ k)
  let n := (m + 2) * B
  let r (k : Fin (m + 1)) := (k.val + 1) * B
  let bits (x : Ω) (i : Fin n) : Bool :=
    decide (x ∈ event (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
  let φ (x : Ω) := leafOfBits n (bits x)
  have hbits (x : Ω) : leafBits n (φ x) = bits x := leafBits_ofBits n (bits x)
  have hφ : Measurable φ := by
    apply measurable_leafOfBits
    intro i
    apply measurable_to_bool
    convert h_event (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 using 1
    ext x
    simp [bits]
  have hr : Monotone r := fun k l h => Nat.mul_le_mul_right B (Nat.add_le_add_right h 1)
  have hrn (k : Fin (m + 1)) : r k ≤ n :=
    Nat.mul_le_mul_right B (by have := k.isLt; omega)
  have hσ (k : Fin (m + 1)) : ℱ k = (dyadicMeasurableSpace n (r k)).comap φ := by
    apply le_antisymm
    · rw [hgen k]
      apply MeasurableSpace.generateFrom_le
      intro s hs
      obtain ⟨i, hi⟩ := he s (Or.inl (Set.mem_iUnion.mpr ⟨k, hs⟩))
      let idx : Fin n := finProdFinEquiv (k.castSucc, i)
      have hidx : idx.val < r k := by
        change i.val + B * k.val < (k.val + 1) * B
        have := i.isLt
        nlinarith
      have hsm : MeasurableSet[ℱ k] s := by
        rw [hgen k]
        exact MeasurableSpace.measurableSet_generateFrom hs
      refine ⟨{l | leafBits n l idx = true}, measurable_leafBits n (r k) idx hidx
        (measurableSet_singleton true), ?_⟩
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, φ, leafBits_ofBits, bits, idx,
        Equiv.symm_apply_apply, decide_eq_true_eq]
      simp only [event, Fin.val_castSucc, dif_pos k.isLt, hi, if_pos hsm]
    · apply (@measurable_leafOfBits_prefix Ω (ℱ k) n (r k) bits ?_).comap_le
      intro idx hidx
      obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective idx
      have hjk : j.val ≤ k.val := by
        change i.val + B * j.val < (k.val + 1) * B at hidx
        have hB : 0 < B := Nat.zero_lt_of_lt i.isLt
        by_contra h
        have hj : k.val + 1 ≤ j.val := by omega
        have := Nat.mul_le_mul_left B hj
        nlinarith
      have ht := h_stage k j i hjk
      apply measurable_to_bool
      convert ht using 1
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, bits,
        Equiv.symm_apply_apply, decide_eq_true_eq]
  have hfactor : (fun x => g x).FactorsThrough φ := by
    intro x y hxy
    obtain ⟨i, hi⟩ := he (g ⁻¹' {g x}) (Or.inr ⟨g x, ⟨x, rfl⟩, rfl⟩)
    let idx : Fin n := finProdFinEquiv (Fin.last (m + 1), i)
    have h := congrArg (fun l => leafBits n l idx) hxy
    rw [hbits, hbits] at h
    simp only [bits, idx, Equiv.symm_apply_apply] at h
    have hmem : y ∈ g ⁻¹' {g x} := by
      simpa [event, hi] using h.symm
    exact hmem.symm
  obtain ⟨f, hf⟩ := (Function.factorsThrough_iff (fun x => g x)).mp hfactor
  exact ⟨n, r, φ, f, hr, hrn, hφ, hσ, fun x => congrFun hf x⟩

end HilbertUMD
