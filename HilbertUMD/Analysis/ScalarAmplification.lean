import HilbertUMD.Transfer.TransferL2

/-! Coordinatewise amplification of scalar operators on actual Bochner L2. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace HilbertUMD.L2Transfer

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

def coordinate (j : Leaf n) : Vec 𝕜 n →L[𝕜] 𝕜 := ContinuousLinearMap.proj j

def insertion (j : Leaf n) : 𝕜 →L[𝕜] Vec 𝕜 n :=
  ContinuousLinearMap.single 𝕜 (fun _ : Leaf n => 𝕜) j

@[simp] theorem coordinate_apply (j : Leaf n) (x : Vec 𝕜 n) : coordinate j x = x j := rfl

theorem coordinate_insertion_l2 (j k : Leaf n) (g : Lp 𝕜 2 μ) :
    (coordinate (𝕜 := 𝕜) k).compLpL 2 μ ((insertion (𝕜 := 𝕜) j).compLpL 2 μ g) =
      if k = j then g else 0 := by
  apply Lp.ext
  filter_upwards [(coordinate (𝕜 := 𝕜) k).coeFn_compLpL ((insertion (𝕜 := 𝕜) j).compLpL 2 μ g),
    (insertion (𝕜 := 𝕜) j).coeFn_compLpL g, Lp.coeFn_zero 𝕜 2 μ] with t hC hI hZ
  rw [hC, hI]
  by_cases h : k = j
  · subst k
    simp [insertion, coordinate]
  · rw [if_neg h]
    have hz : (coordinate (𝕜 := 𝕜) k) ((insertion j) (g t)) = 0 := by
      simp [insertion, coordinate, h]
    rw [hz]
    exact hZ.symm

/-- A scalar L2 operator amplified to the finite-dimensional coordinate space. -/
def amplification (U : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) :
    Lp (Vec 𝕜 n) 2 μ →L[𝕜] Lp (Vec 𝕜 n) 2 μ :=
  ∑ j : Leaf n, ((insertion j).compLpL 2 μ).comp (U.comp ((coordinate j).compLpL 2 μ))

/-- The constructed bounded operator has precisely the requested scalar action
on every coordinate. -/
theorem coordinate_amplification (U : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (f : Lp (Vec 𝕜 n) 2 μ) (k : Leaf n) :
    (coordinate (𝕜 := 𝕜) k).compLpL 2 μ (amplification μ U f) =
      U ((coordinate (𝕜 := 𝕜) k).compLpL 2 μ f) := by
  classical
  simp only [amplification, sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    coordinate_insertion_l2]
  simp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem zero_compLpL : (0 : E →L[𝕜] F).compLpL 2 μ = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [(0 : E →L[𝕜] F).coeFn_compLpL f, Lp.coeFn_zero F 2 μ] with t h0 hZ
  simpa using h0.trans hZ.symm

theorem sum_compLpL {ι : Type*} (s : Finset ι) (J : ι → E →L[𝕜] F) :
    (∑ j ∈ s, J j).compLpL 2 μ = ∑ j ∈ s, (J j).compLpL 2 μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_compLpL]
  | @insert j s hj ih => simp [Finset.sum_insert, hj, ContinuousLinearMap.add_compLpL, ih]

/-- The scalar functional summing the coordinates in a given dyadic block. -/
def blockFunctional (a : Node n) : Vec 𝕜 n →L[𝕜] 𝕜 :=
  ∑ j ∈ nodeLeaves n a, coordinate j

theorem blockFunctional_apply (a : Node n) (x : Vec 𝕜 n) :
    blockFunctional a x = blockSum n x a := by
  simp [blockFunctional, blockSum_eq_sum_nodeLeaves]

theorem block_amplification (U : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (f : Lp (Vec 𝕜 n) 2 μ) (a : Node n) :
    (blockFunctional (𝕜 := 𝕜) a).compLpL 2 μ (amplification μ U f) =
      U ((blockFunctional (𝕜 := 𝕜) a).compLpL 2 μ f) := by
  simp only [blockFunctional, sum_compLpL, sum_apply, map_sum,
    coordinate_amplification]

/-- The squared H-valued Bochner L2 norm is the sum of the squared scalar
L2 norms of the dyadic block sums. -/
theorem hilbert_fibreNorm_sq (f : Lp (Vec 𝕜 n) 2 μ) :
    fibreNorm μ toH f ^ 2 = ∑ a : Node n, fibreNorm μ (blockFunctional a) f ^ 2 := by
  rw [fibreNorm_sq]
  simp only [norm_toH, hilbertNorm_sq]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [fibreNorm_sq]
    simp only [blockFunctional_apply]
  · intro a _
    simpa only [blockFunctional_apply] using fibreNorm_integrable_sq μ (blockFunctional (𝕜 := 𝕜) a) f

/-- Every scalar L2 contraction amplifies contractively to the manuscript's
dyadic Hilbert norm. This proof uses finite sums of actual scalar L2 norms. -/
theorem amplification_hilbert_contraction (U : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (hU : ∀ g, ‖U g‖ ≤ ‖g‖) (f : Lp (Vec 𝕜 n) 2 μ) :
    fibreNorm μ toH (amplification μ U f) ≤ fibreNorm μ toH f := by
  apply (sq_le_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [hilbert_fibreNorm_sq, hilbert_fibreNorm_sq]
  apply Finset.sum_le_sum
  intro a _
  rw [fibreNorm_apply, fibreNorm_apply, block_amplification]
  exact pow_le_pow_left₀ (norm_nonneg _) (hU _) 2

/-- The full scalar-contraction transfer estimate of Proposition 2.2 on
arbitrary measure spaces, for real or complex scalars. No Hilbert-space
amplification fact or density step is assumed. -/
theorem scalar_transfer {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} (hT : TransferAssumptions T)
    (U : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) (hU : ∀ g, ‖U g‖ ≤ ‖g‖)
    (M : ℝ)
    (hM : ∀ f, fibreNorm μ (toImage T) (amplification μ U f) ≤ M * fibreNorm μ toL1 f)
    (f : Lp (Vec 𝕜 n) 2 μ) :
    fibreNorm μ (toGraph T) (amplification μ U f) ^ 2 ≤
      (M ^ 2 + 2 * ((n : ℝ) + 1)) * fibreNorm μ (toGraph T) f ^ 2 :=
  transfer μ hT (amplification μ U) (amplification_hilbert_contraction μ U hU) M hM f

end HilbertUMD.L2Transfer
