import HilbertUMD.Matrices.MatrixCubic
import HilbertUMD.Analysis.CubicLp

/-! Actual Bochner Lp realizations of the tree block data. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace HilbertUMD

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)
variable {p : ℝ≥0∞}

theorem coeFn_affine_sum {ι : Type*} [Fintype ι] (x : ι → Lp ℝ p μ)
    (b : Lp ℝ p μ) (c : ℝ) :
    ⇑(b + c • ∑ i, x i) =ᵐ[μ] (fun s => b s + c * ∑ i, x i s) := by
  filter_upwards [Lp.coeFn_add b (c • ∑ i, x i), Lp.coeFn_smul c (∑ i, x i),
    Lp.coeFn_fun_finsetSum Finset.univ x] with s ha hc hs
  rw [ha]
  change b s + (c • ∑ i, x i) s = _
  rw [hc]
  change b s + c * (∑ i, x i) s = _
  rw [hs]

/-- The bundled block sums have exactly the desired representatives a.e.,
including all accumulated external row terms. -/
theorem treeBlockVector_coeFn (η : ℝ) (c : ℕ → ℝ) (n k : ℕ)
    (x : Leaf n → Lp ℝ p μ) (b : Lp ℝ p μ) (i : TreeParents n k) :
    (⇑(treeBlockVector η c n k x b i).u =ᵐ[μ]
      fun s => (treeBlockValues η c n k (fun j => x j s) (b s) i).u) ∧
    (⇑(treeBlockVector η c n k x b i).v =ᵐ[μ]
      fun s => (treeBlockValues η c n k (fun j => x j s) (b s) i).v) ∧
    (⇑(treeBlockVector η c n k x b i).b =ᵐ[μ]
      fun s => (treeBlockValues η c n k (fun j => x j s) (b s) i).b) := by
  induction n generalizing k b with
  | zero => exact PEmpty.elim i
  | succ n ih =>
    cases k with
    | zero =>
      exact ⟨Lp.coeFn_fun_finsetSum Finset.univ (fun j => x (Sum.inl j)),
        Lp.coeFn_fun_finsetSum Finset.univ (fun j => x (Sum.inr j)), Filter.EventuallyEq.rfl⟩
    | succ k =>
      rcases i with i | i
      · have hh := ih k (fun j => x (Sum.inl j))
          (b + c (n+1) • ∑ j, x (Sum.inr j)) i
        have hb := coeFn_affine_sum μ (fun j => x (Sum.inr j)) b (c (n+1))
        refine ⟨?_, ?_, ?_⟩
        · filter_upwards [hh.1, hb] with s hs hb
          change _ = (treeBlockValues η c n k (fun j => x (Sum.inl j) s)
            (b s + c (n+1) * ∑ j, x (Sum.inr j) s) i).u
          rw [← hb]
          exact hs
        · filter_upwards [hh.2.1, hb] with s hs hb
          change _ = (treeBlockValues η c n k (fun j => x (Sum.inl j) s)
            (b s + c (n+1) * ∑ j, x (Sum.inr j) s) i).v
          rw [← hb]
          exact hs
        · filter_upwards [hh.2.2, hb] with s hs hb
          change _ = (treeBlockValues η c n k (fun j => x (Sum.inl j) s)
            (b s + c (n+1) * ∑ j, x (Sum.inr j) s) i).b
          rw [← hb]
          exact hs
      · have hh := ih k (fun j => x (Sum.inr j))
          (b + (η * c (n+1)) • ∑ j, x (Sum.inl j)) i
        have hb := coeFn_affine_sum μ (fun j => x (Sum.inl j)) b (η * c (n+1))
        refine ⟨?_, ?_, ?_⟩
        · filter_upwards [hh.1, hb] with s hs hb
          change _ = (treeBlockValues η c n k (fun j => x (Sum.inr j) s)
            (b s + (η * c (n+1)) * ∑ j, x (Sum.inl j) s) i).u
          rw [← hb]
          exact hs
        · filter_upwards [hh.2.1, hb] with s hs hb
          change _ = (treeBlockValues η c n k (fun j => x (Sum.inr j) s)
            (b s + (η * c (n+1)) * ∑ j, x (Sum.inl j) s) i).v
          rw [← hb]
          exact hs
        · filter_upwards [hh.2.2, hb] with s hs hb
          change _ = (treeBlockValues η c n k (fun j => x (Sum.inr j) s)
            (b s + (η * c (n+1)) * ∑ j, x (Sum.inl j) s) i).b
          rw [← hb]
          exact hs

/-- Simultaneous a.e. representative formulas for every parent at a depth,
with the zero external row used at the root of the matrix argument. -/
theorem treeBlockVector_zero_coeFn (η : ℝ) (c : ℕ → ℝ) (n k : ℕ)
    (x : Leaf n → Lp ℝ p μ) :
    ∀ᵐ s ∂μ, ∀ i : TreeParents n k,
      (treeBlockVector η c n k x 0 i).u s = (treeBlockValues η c n k (fun j => x j s) 0 i).u ∧
      (treeBlockVector η c n k x 0 i).v s = (treeBlockValues η c n k (fun j => x j s) 0 i).v ∧
      (treeBlockVector η c n k x 0 i).b s = (treeBlockValues η c n k (fun j => x j s) 0 i).b := by
  have hu := ae_all_iff.mpr (fun i => (treeBlockVector_coeFn μ η c n k x 0 i).1)
  have hv := ae_all_iff.mpr (fun i => (treeBlockVector_coeFn μ η c n k x 0 i).2.1)
  have hb := ae_all_iff.mpr (fun i => (treeBlockVector_coeFn μ η c n k x 0 i).2.2)
  filter_upwards [hu, hv, hb, Lp.coeFn_zero ℝ p μ] with s hu hv hb hz
  intro i
  simpa only [hz, Pi.zero_apply] using And.intro (hu i) (And.intro (hv i) (hb i))

/-- Positive inputs give nonnegative child sums, a partition of the total
mass, and uniformly bounded external rows for actual Lp block elements. -/
theorem treeBlockVector_geometry (η : ℝ) (c : ℕ → ℝ)
    (hη : |η| ≤ 1) (hc : ∀ k, |c k| ≤ 1) (n k : ℕ) (hk : k < n)
    (x : Leaf n → Lp ℝ p μ) (hx : ∀ᵐ s ∂μ, ∀ j, 0 ≤ x j s) :
    ∀ᵐ s ∂μ,
      (∀ i : TreeParents n k,
        0 ≤ (treeBlockVector η c n k x 0 i).u s ∧
        0 ≤ (treeBlockVector η c n k x 0 i).v s ∧
        |(treeBlockVector η c n k x 0 i).u s| ≤ ∑ j, x j s ∧
        |(treeBlockVector η c n k x 0 i).v s| ≤ ∑ j, x j s ∧
        |(treeBlockVector η c n k x 0 i).b s| ≤ ∑ j, x j s) ∧
      (∑ i : TreeParents n k, ((treeBlockVector η c n k x 0 i).u s +
        (treeBlockVector η c n k x 0 i).v s)) = ∑ j, x j s := by
  filter_upwards [hx, treeBlockVector_zero_coeFn μ η c n k x] with s hs hval
  constructor
  · intro i
    rw [(hval i).1, (hval i).2.1, (hval i).2.2]
    have hp := treeBlockValues_nonneg η c n k (fun j => x j s) hs 0 i
    have hm := treeBlockValues_mass_bound η c hη hc n k (fun j => x j s) hs 0 i
    simp only [abs_zero, add_zero, total] at hm
    refine ⟨hp.1, hp.2, ?_, ?_, ?_⟩
    · rw [abs_of_nonneg hp.1]
      linarith [abs_nonneg (treeBlockValues η c n k (fun j => x j s) 0 i).b]
    · rw [abs_of_nonneg hp.2]
      linarith [abs_nonneg (treeBlockValues η c n k (fun j => x j s) 0 i).b]
    · linarith
  · calc
      _ = ∑ i, ((treeBlockValues η c n k (fun j => x j s) 0 i).u +
          (treeBlockValues η c n k (fun j => x j s) 0 i).v) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(hval i).1, (hval i).2.1]
      _ = _ := treeBlockValues_sum η c n k hk (fun j => x j s) 0

end HilbertUMD
