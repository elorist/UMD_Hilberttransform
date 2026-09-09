import HilbertUMD.Interfaces.MartingaleEstimates
import HilbertUMD.UMD.LowerSquareL1

/-! Checked mixed-norm assembly of the martingale product estimate.
The finite transform, square-function, maximal, and lower-square estimates
used here all have checked proofs. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace HilbertUMD

variable {ι : Type} [Fintype ι]

theorem leaf_mixed_aestronglyMeasurable (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : Leaf n → ι → ℝ) :
    AEStronglyMeasurable (fun x => (WithLp.toLp q (f x) : PiLp q (fun _ : ι => ℝ)))
      (leafUniform n) :=
  (leaf_memLp n 1 _).aestronglyMeasurable

/-- The family of scalar transforms. -/
def dyadicFamilyTransform (n : ℕ) (ε : Fin n → ℝ) (f : Leaf n → ι → ℝ) : Leaf n → ι → ℝ :=
  fun x j => dyadicScalar n ε (fun y => f y j) x

def dyadicFamilyMaximal (n : ℕ) (f : Leaf n → ι → ℝ) : Leaf n → ι → ℝ :=
  fun x j => dyadicMaximal n (fun y => f y j) x

def dyadicFamilySquare (n : ℕ) (f : Leaf n → ι → ℝ) : Leaf n → ι → ℝ :=
  fun x j => dyadicSquareFunction n (fun y => f y j) x

/-- The genuine terminal product u(Uv)-v(Uu), coordinate by coordinate. -/
def dyadicFamilyProduct (n : ℕ) (ε : Fin n → ℝ) (u v : Leaf n → ι → ℝ) : Leaf n → ι → ℝ :=
  fun x j => u x j * dyadicFamilyTransform n ε v x j -
    v x j * dyadicFamilyTransform n ε u x j

omit [Fintype ι] in
theorem dyadicFamilyProduct_eq_process (n : ℕ) (ε : Fin n → ℝ)
    (u v : Leaf n → ι → ℝ) (j : ι) :
    (fun x => dyadicFamilyProduct n ε u v x j) =
      dyadicProductProcess n ε (fun x => u x j) (fun x => v x j) n := by
  funext x
  simp [dyadicFamilyProduct, dyadicFamilyTransform]

/-- Integration of the checked pointwise estimate using mixed Hölder and
Minkowski. All hypotheses are explicit, so this theorem has no admitted
dependency even though its eventual applications use classical bounds. -/
theorem dyadicSquareProduct_estimate_of_bounds (n : ℕ) (ε : Fin n → ℝ)
    (hε : ∀ k, |ε k| ≤ 1) (u v : Leaf n → ι → ℝ) (D : ℝ≥0)
    (hD : ∀ f : Leaf n → ι → ℝ,
      mixedNorm 3 2 (leafUniform n) (dyadicFamilyMaximal n f) ≤
        (D : ℝ≥0∞) * mixedNorm 3 2 (leafUniform n) f)
    (hU : ∀ f : Leaf n → ι → ℝ,
      mixedNorm 3 2 (leafUniform n) (dyadicFamilyTransform n ε f) ≤
        2 * mixedNorm 3 2 (leafUniform n) f)
    (hS : ∀ f : Leaf n → ι → ℝ,
      mixedNorm 3 2 (leafUniform n) (dyadicFamilySquare n f) ≤
        2 * mixedNorm 3 2 (leafUniform n) f) :
    mixedNorm (3 / 2) 1 (leafUniform n)
      (dyadicFamilySquare n (dyadicFamilyTransform n ε (dyadicFamilyProduct n ε u v))) ≤
      12 * (D : ℝ≥0∞) * mixedNorm 3 2 (leafUniform n) u * mixedNorm 3 2 (leafUniform n) v := by
  let : ENNReal.HolderTriple 3 3 (3 / 2) := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by simp)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
  let A : (Leaf n → ι → ℝ) → Leaf n → ι → ℝ :=
    fun f => dyadicFamilyMaximal n f + dyadicFamilyMaximal n (dyadicFamilyTransform n ε f)
  have hA (f : Leaf n → ι → ℝ) : mixedNorm 3 2 (leafUniform n) (A f) ≤
      3 * (D : ℝ≥0∞) * mixedNorm 3 2 (leafUniform n) f := by
    calc
      _ ≤ mixedNorm 3 2 (leafUniform n) (dyadicFamilyMaximal n f) +
          mixedNorm 3 2 (leafUniform n) (dyadicFamilyMaximal n (dyadicFamilyTransform n ε f)) :=
        mixedNorm_add_le 3 2 (leafUniform n) (by norm_num) _ _
          (leaf_mixed_aestronglyMeasurable n 2 _) (leaf_mixed_aestronglyMeasurable n 2 _)
      _ ≤ (D : ℝ≥0∞) * mixedNorm 3 2 (leafUniform n) f +
          (D : ℝ≥0∞) * (2 * mixedNorm 3 2 (leafUniform n) f) :=
        add_le_add (hD f) ((hD _).trans (mul_le_mul' le_rfl (hU f)))
      _ = _ := by ring
  let P : Leaf n → ι → ℝ := fun x j => A u x j * dyadicFamilySquare n v x j
  let Q : Leaf n → ι → ℝ := fun x j => A v x j * dyadicFamilySquare n u x j
  have hpoint (x : Leaf n) (j : ι) :
      dyadicFamilySquare n (dyadicFamilyTransform n ε (dyadicFamilyProduct n ε u v)) x j ≤
        P x j + Q x j := by
    have h := dyadicSquareFunction_transformed_product_le n ε hε
      (fun x => u x j) (fun x => v x j) x
    simpa only [dyadicFamilySquare, dyadicFamilyTransform,
      dyadicFamilyProduct_eq_process, P, Q, A, Pi.add_apply, dyadicFamilyMaximal] using h
  have hdom : mixedNorm (3 / 2) 1 (leafUniform n)
      (dyadicFamilySquare n (dyadicFamilyTransform n ε (dyadicFamilyProduct n ε u v))) ≤
      mixedNorm (3 / 2) 1 (leafUniform n) (P + Q) := by
    apply mixedNorm_mono
    apply Filter.Eventually.of_forall
    intro x
    simp only [PiLp.norm_eq_of_L1, Real.norm_eq_abs]
    apply Finset.sum_le_sum
    intro j _
    change |dyadicFamilySquare n _ x j| ≤ |P x j + Q x j|
    rw [abs_of_nonneg (show 0 ≤ dyadicFamilySquare n _ x j from dyadicSquareFunction_nonneg n _ x)]
    exact (hpoint x j).trans (le_abs_self _)
  have hP : mixedNorm (3 / 2) 1 (leafUniform n) P ≤
      (3 * (D : ℝ≥0∞) * mixedNorm 3 2 (leafUniform n) u) *
        (2 * mixedNorm 3 2 (leafUniform n) v) :=
    (mixedNorm_mul_le 3 3 (3 / 2) (leafUniform n) (A u) (dyadicFamilySquare n v)
      (leaf_mixed_aestronglyMeasurable n 2 _) (leaf_mixed_aestronglyMeasurable n 2 _)).trans
      (mul_le_mul' (hA u) (hS v))
  have hQ : mixedNorm (3 / 2) 1 (leafUniform n) Q ≤
      (3 * (D : ℝ≥0∞) * mixedNorm 3 2 (leafUniform n) v) *
        (2 * mixedNorm 3 2 (leafUniform n) u) :=
    (mixedNorm_mul_le 3 3 (3 / 2) (leafUniform n) (A v) (dyadicFamilySquare n u)
      (leaf_mixed_aestronglyMeasurable n 2 _) (leaf_mixed_aestronglyMeasurable n 2 _)).trans
      (mul_le_mul' (hA v) (hS u))
  calc
    _ ≤ mixedNorm (3 / 2) 1 (leafUniform n) P + mixedNorm (3 / 2) 1 (leafUniform n) Q :=
      hdom.trans (mixedNorm_add_le (3 / 2) 1 (leafUniform n) (by
        apply (ENNReal.toReal_le_toReal (by norm_num) (by finiteness)).mp
        norm_num [ENNReal.toReal_div]) P Q
        (leaf_mixed_aestronglyMeasurable n 1 _) (leaf_mixed_aestronglyMeasurable n 1 _))
    _ ≤ _ := (add_le_add hP hQ).trans_eq (by ring)

/-- The existing maximal and transform estimates give the explicit
square-product coefficient 12 * (65 / 4) = 195. -/
theorem dyadicSquareProduct_estimate (n : ℕ) (ε : Fin n → ℝ)
    (hε : ∀ k, |ε k| ≤ 1) (u v : Leaf n → ι → ℝ) :
    mixedNorm (3 / 2) 1 (leafUniform n)
      (dyadicFamilySquare n (dyadicFamilyTransform n ε (dyadicFamilyProduct n ε u v))) ≤
      195 * mixedNorm 3 2 (leafUniform n) u * mixedNorm 3 2 (leafUniform n) v := by
  have hD (f : Leaf n → ι → ℝ) :
      mixedNorm 3 2 (leafUniform n) (dyadicFamilyMaximal n f) ≤
        (((65 / 4) : ℝ≥0) : ℝ≥0∞) * mixedNorm 3 2 (leafUniform n) f := by
    unfold dyadicFamilyMaximal
    rw [ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_ofNat]
    exact dyadic_vector_doob_three_two n f
  have hc : (12 : ℝ≥0∞) * (65 / 4) = 195 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  simpa only [ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, hc] using
    dyadicSquareProduct_estimate_of_bounds n ε hε u v (65 / 4) hD
      (fun f => Interfaces.dyadic_hilbert_transform_three n ε hε f)
      (fun f => Interfaces.dyadic_hilbert_square_three n f)

/-- A universal square-product coefficient, chosen before depth and dimension. -/
theorem exists_dyadicSquareProduct_estimate :
    ∃ C : ℝ≥0, ∀ (n : ℕ) (ι : Type) [Fintype ι] (ε : Fin n → ℝ),
      (∀ k, |ε k| ≤ 1) → ∀ u v : Leaf n → ι → ℝ,
      mixedNorm (3 / 2) 1 (leafUniform n)
        (dyadicFamilySquare n (dyadicFamilyTransform n ε (dyadicFamilyProduct n ε u v))) ≤
        (C : ℝ≥0∞) * mixedNorm 3 2 (leafUniform n) u * mixedNorm 3 2 (leafUniform n) v := by
  refine ⟨195, ?_⟩
  intro n ι _ ε hε u v
  simpa only [ENNReal.coe_ofNat] using dyadicSquareProduct_estimate n ε hε u v

/-- The direct finite l1 lower square estimate, with constant (45 / 8). -/
theorem exists_dyadic_lower_square_l1 :
    ∃ L : ℝ≥0, ∀ (n : ℕ) (ι : Type) [Fintype ι] (f : Leaf n → ι → ℝ),
      (∀ x j, leafAverage (𝕜 := ℝ) n 0 (fun y => f y j) x = 0) →
      mixedNorm (3 / 2) 1 (leafUniform n) f ≤
        (L : ℝ≥0∞) * mixedNorm (3 / 2) 1 (leafUniform n) (dyadicFamilySquare n f) := by
  refine ⟨(45 / 8), ?_⟩
  intro n ι _ f hf
  rw [ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_ofNat]
  change mixedNorm (3 / 2) 1 (leafUniform n) f ≤
    (45 / 8) * mixedNorm (3 / 2) 1 (leafUniform n)
      (fun x j => dyadicSquareFunction n (fun y => f y j) x)
  exact mixedNorm_lower_square_l1 n f hf

/-- The finite dyadic martingale half of Lemma 3.1, with the explicit
coefficient (45 / 8) * 195 ≤ 1097 from the checked lower-square and product bounds. -/
theorem martingale_product_bound (n : ℕ) (ε : Fin n → ℝ)
    (hε : ∀ k, |ε k| ≤ 1) (u v : Leaf n → ι → ℝ) :
    mixedNorm (3 / 2) 1 (leafUniform n)
      (dyadicFamilyTransform n ε (dyadicFamilyProduct n ε u v)) ≤
      1097 * mixedNorm 3 2 (leafUniform n) u * mixedNorm 3 2 (leafUniform n) v := by
  have hzero : ∀ x j, leafAverage (𝕜 := ℝ) n 0
      (fun y => dyadicFamilyTransform n ε (dyadicFamilyProduct n ε u v) y j) x = 0 := by
    intro x j
    exact leafAverage_dyadicScalar_zero n ε _ x
  calc
    _ ≤ (45 / 8) * mixedNorm (3 / 2) 1 (leafUniform n)
        (dyadicFamilySquare n (dyadicFamilyTransform n ε (dyadicFamilyProduct n ε u v))) :=
      mixedNorm_lower_square_l1 n _ hzero
    _ ≤ (45 / 8) * (195 * mixedNorm 3 2 (leafUniform n) u *
        mixedNorm 3 2 (leafUniform n) v) :=
      mul_le_mul' le_rfl (dyadicSquareProduct_estimate n ε hε u v)
    _ ≤ _ := by
      have hc : (45 / 8 : ℝ≥0∞) * 195 ≤ 1097 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
      simpa only [← mul_assoc] using mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl

/-- The product coefficient is uniform in depth, dimension, and real
multipliers in [-1,1]. -/
theorem exists_martingale_product_bound :
    ∃ C : ℝ≥0, ∀ (n : ℕ) (ι : Type) [Fintype ι] (ε : Fin n → ℝ),
      (∀ k, |ε k| ≤ 1) → ∀ u v : Leaf n → ι → ℝ,
      mixedNorm (3 / 2) 1 (leafUniform n)
        (dyadicFamilyTransform n ε (dyadicFamilyProduct n ε u v)) ≤
        (C : ℝ≥0∞) * mixedNorm 3 2 (leafUniform n) u * mixedNorm 3 2 (leafUniform n) v := by
  refine ⟨1097, ?_⟩
  intro n ι _ ε hε u v
  simpa only [ENNReal.coe_ofNat] using martingale_product_bound n ε hε u v

end HilbertUMD
