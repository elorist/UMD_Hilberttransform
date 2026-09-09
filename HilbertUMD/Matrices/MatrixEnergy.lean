import HilbertUMD.Matrices.MatrixScalarData

/-! The original cubic energy bound for both tree matrices, deduced from
scalar analytic inputs and the checked block decomposition. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace HilbertUMD

variable {S : Type*} [MeasurableSpace S] {μ : Measure S}

theorem abs_eq_one_of_sq_eq_one {a : ℝ} (h : a^2 = 1) : |a| = 1 := by
  rcases sq_eq_one_iff.mp h with h | h <;> rw [h] <;> norm_num

set_option maxHeartbeats 1000000 in
/-- One level of the actual matrix energy is integrable and has the required
uniform bound. All scalar products here are genuine Lp equivalence classes. -/
theorem ScalarMatrixData.level_energy_bound {η M P : ℝ}
    (R : ScalarMatrixData μ η M P) (hη : η^2 = 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (c : ℕ → ℝ) (hc : ∀ k, c k ^ 2 = 1) (n k : ℕ) (hk : k < n)
    (f : Leaf n → Lp ℝ 3 μ) (hf : ∀ᵐ s ∂μ, ∀ j, 0 ≤ f j s)
    (G : ℝ) (hG : 0 ≤ G) (hgNorm : eLpNorm (fun s => ∑ j, f j s) 3 μ ≤ ENNReal.ofReal G) :
    Integrable (fun s => treeLevelJump η c n k (fun j => f j s) (fun j => R.atThree (f j) s) 0) μ ∧
    (∫ s, treeLevelJump η c n k (fun j => f j s) (fun j => R.atThree (f j) s) 0 ∂μ) ≤
      (2 * M^2 + 2 * P) * G^3 := by
  let d := treeBlockVector η c n k f (0 : Lp ℝ 3 μ)
  let u : TreeParents n k → Lp ℝ 3 μ := fun i => (d i).u
  let v : TreeParents n k → Lp ℝ 3 μ := fun i => (d i).v
  let b : TreeParents n k → Lp ℝ 3 μ := fun i => (d i).b
  let w : TreeParents n k → Lp ℝ (3/2) μ := fun i => scalarProductLp μ R.atThree η (u i) (v i)
  let g : S → ℝ := fun s => ∑ j, f j s
  have hg : MemLp g 3 μ := memLp_finsetSum Finset.univ (fun j _ => Lp.memLp (f j))
  have hgeom := treeBlockVector_geometry μ η c (abs_eq_one_of_sq_eq_one hη).le
    (fun k => (abs_eq_one_of_sq_eq_one (hc k)).le) n k hk f hf
  have huPos : ∀ᵐ s ∂μ, ∀ i, 0 ≤ u i s := by
    filter_upwards [hgeom] with s hs
    exact fun i => (hs.1 i).1
  have hvPos : ∀ᵐ s ∂μ, ∀ i, 0 ≤ v i s := by
    filter_upwards [hgeom] with s hs
    exact fun i => (hs.1 i).2.1
  have huBound : ∀ᵐ s ∂μ, ∀ i, |u i s| ≤ g s := by
    filter_upwards [hgeom] with s hs
    exact fun i => (hs.1 i).2.2.1
  have hvBound : ∀ᵐ s ∂μ, ∀ i, |v i s| ≤ g s := by
    filter_upwards [hgeom] with s hs
    exact fun i => (hs.1 i).2.2.2.1
  have hbBound : ∀ᵐ s ∂μ, ∀ i, |b i s| ≤ g s := by
    filter_upwards [hgeom] with s hs
    exact fun i => (hs.1 i).2.2.2.2
  have hsum : ∀ᵐ s ∂μ, ∑ i, (u i s + v i s) = g s := by
    filter_upwards [hgeom] with s hs
    exact hs.2
  have hU : mixedNorm 3 2 μ (fun s i => u i s) ≤ ENNReal.ofReal G :=
    (mixedNorm_two_le_mass μ _ _ g huPos hvPos hsum).trans hgNorm
  have hV : mixedNorm 3 2 μ (fun s i => v i s) ≤ ENNReal.ofReal G := by
    apply (mixedNorm_two_le_mass μ _ _ g hvPos huPos ?_).trans hgNorm
    filter_upwards [hsum] with s hs
    simpa only [add_comm] using hs
  have hRU : mixedNorm 3 2 μ (fun s i => R.atThree (u i) s) ≤ ENNReal.ofReal (M * G) := by
    rw [ENNReal.ofReal_mul hM]
    exact (R.hilbertBound _ u).trans (mul_le_mul' le_rfl hU)
  have hRV : mixedNorm 3 2 μ (fun s i => R.atThree (v i) s) ≤ ENNReal.ofReal (M * G) := by
    rw [ENNReal.ofReal_mul hM]
    exact (R.hilbertBound _ v).trans (mul_le_mul' le_rfl hV)
  have hW : mixedNorm (3/2) 1 μ (fun s i => R.atThreeHalves (w i) s) ≤ ENNReal.ofReal (P * G^2) := by
    calc
      _ ≤ ENNReal.ofReal P * mixedNorm 3 2 μ (fun s i => u i s) *
          mixedNorm 3 2 μ (fun s i => v i s) := R.productBound _ u v
      _ ≤ ENNReal.ofReal P * ENNReal.ofReal G * ENNReal.ofReal G :=
        mul_le_mul' (mul_le_mul' le_rfl hU) hV
      _ = _ := by rw [ENNReal.ofReal_mul hP, ENNReal.ofReal_pow hG]; ring
  have hRUInt : MemLp (fun s => (WithLp.toLp 2 (fun i => R.atThree (u i) s) :
      PiLp 2 (fun _ : TreeParents n k => ℝ))) 3 μ := MemLp.of_eval_piLp (fun i => Lp.memLp _)
  have hRVInt : MemLp (fun s => (WithLp.toLp 2 (fun i => R.atThree (v i) s) :
      PiLp 2 (fun _ : TreeParents n k => ℝ))) 3 μ := MemLp.of_eval_piLp (fun i => Lp.memLp _)
  have hWInt : MemLp (fun s => (WithLp.toLp 1 (fun i => R.atThreeHalves (w i) s) :
      PiLp 1 (fun _ : TreeParents n k => ℝ))) (3/2) μ := MemLp.of_eval_piLp (fun i => Lp.memLp _)
  have hUI : Integrable (fun s => ∑ i, u i s * (R.atThree (v i) s)^2) μ :=
    integrable_weighted_square_of_memLp_three μ (fun i => Lp.memLp _) (fun i => Lp.memLp _)
  have hVI : Integrable (fun s => ∑ i, v i s * (R.atThree (u i) s)^2) μ :=
    integrable_weighted_square_of_memLp_three μ (fun i => Lp.memLp _) (fun i => Lp.memLp _)
  have hBI : Integrable (fun s => ∑ i, R.atThree (b i) s * w i s) μ :=
    integrable_finsetSum _ fun i _ => (Lp.memLp _).integrable_mul (Lp.memLp _)
  let e : S → ℝ := fun s => ∑ i, (u i s * (R.atThree (v i) s)^2 +
    v i s * (R.atThree (u i) s)^2 + 2 * c (n-k) * R.atThree (b i) s * w i s)
  have hei : Integrable e μ := by
    have he : e = (fun s => (∑ i, u i s * (R.atThree (v i) s)^2) +
        (∑ i, v i s * (R.atThree (u i) s)^2) +
        (2*c (n-k)) * (∑ i, R.atThree (b i) s * w i s)) := by
      funext s
      simp only [e, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    rw [he]
    exact (hUI.add hVI).add (hBI.const_mul (2*c (n-k)))
  have he : (fun s => treeLevelJump η c n k (fun j => f j s) (fun j => R.atThree (f j) s) 0) =ᵐ[μ] e := by
    have hw := ae_all_iff.mpr (fun i => scalarProductLp_coeFn μ R.atThree η (u i) (v i))
    have hm : ∀ i : TreeParents n k,
        (treeBlockVector η c n k (fun j => R.atThree (f j)) 0 i).u = R.atThree (u i) ∧
        (treeBlockVector η c n k (fun j => R.atThree (f j)) 0 i).v = R.atThree (v i) ∧
        (treeBlockVector η c n k (fun j => R.atThree (f j)) 0 i).b = R.atThree (b i) := by
      intro i
      simpa only [map_zero, ContinuousLinearMap.coe_coe, u, v, b, d] using
        treeBlockVector_map R.atThree.toLinearMap η c n k f 0 i
    filter_upwards [treeBlockVector_zero_coeFn μ η c n k f,
      treeBlockVector_zero_coeFn μ η c n k (fun j => R.atThree (f j)), hw] with s hdf hdr hw
    rw [treeLevelJump_eq_sum_blocks η c n k _ _ 0 0]
    apply Finset.sum_congr rfl
    intro i _
    rw [← (hdf i).1, ← (hdf i).2.1, ← (hdr i).1, ← (hdr i).2.1, ← (hdr i).2.2,
      (hm i).1, (hm i).2.1, (hm i).2.2]
    change treeRootJump η (c (n-k)) (u i s) (v i s) (R.atThree (u i) s)
      (R.atThree (v i) s) (R.atThree (b i) s) = _
    rw [show w i s = u i s * R.atThree (v i) s + η * (v i s * R.atThree (u i) s) from hw i]
    unfold treeRootJump
    ring
  refine ⟨hei.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact block_energy_integral_le μ g (fun s i => u i s) (fun s i => v i s)
    (fun s i => b i s) (fun s i => R.atThree (u i) s) (fun s i => R.atThree (v i) s)
    (fun s i => R.atThree (b i) s) (fun s i => w i s) (fun s i => R.atThreeHalves (w i) s)
    hg hRUInt hRVInt hWInt huBound hvBound hbBound hUI hVI hBI
    (R.family_dual_abs hη b w) (c (n-k)) G M P (abs_eq_one_of_sq_eq_one (hc (n-k))).le
    hG hM hP hgNorm hRU hRV hW

/-- The common original matrix cubic estimate, uniform in n and in the
scalar operator once its Hilbert and product constants M,P are fixed. -/
theorem ScalarMatrixData.cubic_energy_bound {η M P : ℝ}
    (R : ScalarMatrixData μ η M P) (hη : η^2 = 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (c : ℕ → ℝ) (hc : ∀ k, c k ^ 2 = 1) (n : ℕ)
    (f : Leaf n → Lp ℝ 3 μ) (hf : ∀ᵐ s ∂μ, ∀ j, 0 ≤ f j s)
    (G : ℝ) (hG : 0 ≤ G) (hgNorm : eLpNorm (fun s => ∑ j, f j s) 3 μ ≤ ENNReal.ofReal G) :
    (∫ s, ∑ i, f i s * (treeMatrix η c n (fun j => R.atThree (f j) s) i)^2 ∂μ) ≤
      ((n : ℝ) * (2 * M^2 + 2 * P)) * G^3 := by
  apply tree_cubic_integral_le_of_levels μ η c hη hc n _ _ (2 * M^2 + 2 * P) G
  · intro k hk
    exact (R.level_energy_bound hη hM hP c hc n k (Finset.mem_range.mp hk) f hf G hG hgNorm).1
  · intro k hk
    exact (R.level_energy_bound hη hM hP c hc n k (Finset.mem_range.mp hk) f hf G hG hgNorm).2

end HilbertUMD
