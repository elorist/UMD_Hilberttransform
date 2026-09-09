import HilbertUMD.UMD.DyadicLower
import HilbertUMD.UMD.UMD
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The uniform finite probability model for the dyadic witness. -/

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace HilbertUMD

instance leafMeasurableSpace (n : ℕ) : MeasurableSpace (Leaf n) := ⊤

instance leafMeasurableSingleton (n : ℕ) : MeasurableSingletonClass (Leaf n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The uniform probability measure on the `2^n` leaves. -/
def leafUniform (n : ℕ) : Measure (Leaf n) := (2 ^ n : ℝ≥0∞)⁻¹ • Measure.count

instance leafUniform_probability (n : ℕ) : IsProbabilityMeasure (leafUniform n) where
  measure_univ := by
    simp [leafUniform, Measure.count_apply_finite, card_leaf]
    exact ENNReal.inv_mul_cancel (pow_ne_zero _ (by norm_num)) (by finiteness)

/-- A set is measurable at level `k` iff membership is constant on each block. -/
@[instance_reducible] def dyadicMeasurableSpace (n k : ℕ) : MeasurableSpace (Leaf n) where
  MeasurableSet' s := ∀ i j, j ∈ dyadicBlock n k i → (i ∈ s ↔ j ∈ s)
  measurableSet_empty := by simp
  measurableSet_compl := by
    intro s hs i j hij
    exact not_congr (hs i j hij)
  measurableSet_iUnion := by
    intro f hf i j hij
    simp only [Set.mem_iUnion]
    exact exists_congr (fun a => hf a i j hij)

theorem dyadicMeasurableSpace_mono (n : ℕ) : Monotone (dyadicMeasurableSpace n) := by
  intro k l hkl s hs i j hij
  exact hs i j (dyadicBlock_subset n k l hkl i hij)

/-- The chronological dyadic filtration, including the initial and terminal levels. -/
def leafFiltration (n : ℕ) : Filtration (Fin (n + 1)) (leafMeasurableSpace n) where
  seq k := dyadicMeasurableSpace n k.val
  mono' := fun _ _ h => dyadicMeasurableSpace_mono n h
  le' _ := le_top

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem leafAverage_indicator (n k : ℕ) (f : Leaf n → E) (s : Set (Leaf n))
    (hs : MeasurableSet[dyadicMeasurableSpace n k] s) :
    leafAverage (𝕜 := 𝕜) n k (s.indicator f) =
      s.indicator (leafAverage (𝕜 := 𝕜) n k f) := by
  classical
  funext i
  by_cases hi : i ∈ s
  · rw [Set.indicator_of_mem hi]
    unfold leafAverage
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact Set.indicator_of_mem ((hs i j hj).mp hi) f
  · rw [Set.indicator_of_notMem hi]
    unfold leafAverage
    have hz : ∑ j ∈ dyadicBlock n k i, s.indicator f j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact Set.indicator_of_notMem (fun hj' => hi ((hs i j hj).mpr hj')) f
    rw [hz, smul_zero]

theorem sum_indicator_leafAverage (n k : ℕ) (f : Leaf n → E) (s : Set (Leaf n))
    (hs : MeasurableSet[dyadicMeasurableSpace n k] s) :
    ∑ i, s.indicator (leafAverage (𝕜 := 𝕜) n k f) i = ∑ i, s.indicator f i := by
  rw [← leafAverage_indicator n k f s hs, sum_leafAverage]

theorem stronglyMeasurable_leafAverage (n k : ℕ) (f : Leaf n → E) :
    StronglyMeasurable[dyadicMeasurableSpace n k] (leafAverage (𝕜 := 𝕜) n k f) := by
  let : MeasurableSpace (Leaf n) := dyadicMeasurableSpace n k
  let fs : SimpleFunc (Leaf n) E :=
    ⟨leafAverage (𝕜 := 𝕜) n k f, fun x i j hij => by
      change leafAverage (𝕜 := 𝕜) n k f i = x ↔ leafAverage (𝕜 := 𝕜) n k f j = x
      rw [leafAverage_eq_of_mem n k f i j hij], Set.finite_range _⟩
  exact fs.stronglyMeasurable

theorem leaf_memLp (n : ℕ) (p : ℝ≥0∞) (f : Leaf n → E) : MemLp f p (leafUniform n) := by
  have hf : StronglyMeasurable f := (SimpleFunc.ofFinite f).stronglyMeasurable
  exact MemLp.of_bound hf.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall (fun i => norm_le_pi_norm f i))

section Integrals
variable [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_leafUniform (n : ℕ) (f : Leaf n → E) :
    ∫ i, f i ∂leafUniform n = ((2 : ℝ) ^ n)⁻¹ • ∑ i, f i := by
  rw [leafUniform, integral_smul_measure, integral_count]
  simp

theorem setIntegral_leafAverage (n k : ℕ) (f : Leaf n → E) (s : Set (Leaf n))
    (hs : MeasurableSet[dyadicMeasurableSpace n k] s) :
    ∫ i in s, leafAverage (𝕜 := 𝕜) n k f i ∂leafUniform n =
      ∫ i in s, f i ∂leafUniform n := by
  have hs' : MeasurableSet s := MeasurableSpace.measurableSet_top
  rw [← integral_indicator hs', ← integral_indicator hs', integral_leafUniform,
    integral_leafUniform, sum_indicator_leafAverage n k f s hs]

/-- Finite dyadic conditional averages form an Lp martingale for every exponent. -/
theorem isLpMartingale_leafAverage (n : ℕ) (p : ℝ≥0∞) (f : Leaf n → E) :
    IsLpMartingale (fun k : Fin (n + 1) => leafAverage (𝕜 := 𝕜) n k.val f)
      (leafFiltration n) p (leafUniform n) := by
  refine ⟨fun k => stronglyMeasurable_leafAverage n k.val f,
    fun k => leaf_memLp n p _, ?_⟩
  intro k l hkl s hs _
  rw [setIntegral_leafAverage n k.val f s hs,
    setIntegral_leafAverage n l.val f s ((leafFiltration n).mono hkl s hs)]

end Integrals

theorem lpNorm_leafUniform_two (n : ℕ) (f : Leaf n → E) :
    lpNorm f 2 (leafUniform n) = leafL2Norm n f := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (leaf_memLp n 2 f).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [integral_leafUniform]
  simp only [smul_eq_mul, leafL2Norm, Real.sqrt_eq_rpow, inv_pow, one_div]

theorem eLpNorm_leafUniform_two (n : ℕ) (f : Leaf n → E) :
    eLpNorm f 2 (leafUniform n) = ENNReal.ofReal (leafL2Norm n f) := by
  rw [← ofReal_lpNorm (leaf_memLp n 2 f), lpNorm_leafUniform_two]

/-- Add an independent symmetric sign before revealing the original leaves. -/
def signedLeafLift (n : ℕ) (f : Leaf n → E) : Leaf (n + 1) → E := Sum.elim f (-f)

theorem leafAverage_neg (n k : ℕ) (f : Leaf n → E) (i : Leaf n) :
    leafAverage (𝕜 := 𝕜) n k (-f) i = -leafAverage (𝕜 := 𝕜) n k f i := by
  simp [leafAverage, Finset.sum_neg_distrib]

@[simp] theorem leafAverage_signedLeafLift_zero (n : ℕ) (f : Leaf n → E)
    (i : Leaf (n + 1)) : leafAverage (𝕜 := 𝕜) (n + 1) 0 (signedLeafLift n f) i = 0 := by
  simp [leafAverage, dyadicBlock, Fintype.sum_sum_type, signedLeafLift,
    Finset.sum_neg_distrib]

@[simp] theorem leafAverage_signedLeafLift_inl (n k : ℕ) (f : Leaf n → E) (i : Leaf n) :
    leafAverage (𝕜 := 𝕜) (n + 1) (k + 1) (signedLeafLift n f) (Sum.inl i) =
      leafAverage (𝕜 := 𝕜) n k f i := by
  rw [leafAverage_succ_inl]
  rfl

@[simp] theorem leafAverage_signedLeafLift_inr (n k : ℕ) (f : Leaf n → E) (i : Leaf n) :
    leafAverage (𝕜 := 𝕜) (n + 1) (k + 1) (signedLeafLift n f) (Sum.inr i) =
      -leafAverage (𝕜 := 𝕜) n k f i := by
  rw [leafAverage_succ_inr]
  exact leafAverage_neg n k f i

def liftedBasisProcess (n : ℕ) : Fin (n + 2) → Leaf (n + 1) → L1Vec 𝕜 n :=
  fun k => leafAverage (𝕜 := 𝕜) (n + 1) k.val (signedLeafLift n (l1BasisWitness n))

def liftedAlternatingSigns (n : ℕ) (k : Fin (n + 1)) : 𝕜 := (-1 : 𝕜) ^ (n - k.val)

theorem norm_liftedAlternatingSigns (n : ℕ) (k : Fin (n + 1)) :
    ‖liftedAlternatingSigns (𝕜 := 𝕜) n k‖ = 1 := by simp [liftedAlternatingSigns]

theorem liftedBasisProcess_isLpMartingale (n : ℕ) :
    @IsLpMartingale (Leaf (n + 1)) (Fin (n + 2)) (L1Vec 𝕜 n)
      (leafMeasurableSpace (n + 1)) _ _ _
      (liftedBasisProcess (𝕜 := 𝕜) n) (leafFiltration (n + 1)) 2
      (leafUniform (n + 1)) := isLpMartingale_leafAverage (n + 1) 2 _

theorem differenceSum_liftedBasisProcess (n : ℕ) :
    differenceSum (liftedBasisProcess (𝕜 := 𝕜) n) =
      signedLeafLift n (l1BasisWitness (𝕜 := 𝕜) n) := by
  funext i
  rw [differenceSum_eq]
  simp [liftedBasisProcess]

theorem eLpNorm_differenceSum_liftedBasisProcess (n : ℕ) :
    eLpNorm (differenceSum (liftedBasisProcess (𝕜 := 𝕜) n)) 2 (leafUniform (n + 1)) = 1 := by
  rw [differenceSum_liftedBasisProcess]
  have hn : ∀ i : Leaf (n + 1), ‖signedLeafLift n (l1BasisWitness (𝕜 := 𝕜) n) i‖ = ‖(1 : ℝ)‖ := by
    intro i
    cases i <;> simp [signedLeafLift]
  rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall hn)]
  rw [eLpNorm_const' _ (by norm_num) (by norm_num)]
  rw [(leafUniform_probability (n + 1)).measure_univ]
  simp

theorem signedDyadicOperator_apply (n : ℕ) (x : L1Vec 𝕜 n) :
    signedDyadicOperator n x = signedDyadic n (WithLp.ofLp x) := rfl

theorem lifted_transform_inl (n : ℕ) (i : Leaf n) :
    martingaleTransform (signedDyadicOperator (𝕜 := 𝕜) n) (liftedAlternatingSigns n)
      (liftedBasisProcess n) (Sum.inl i) =
      (-1 : 𝕜) ^ n • signedDyadic n (basisAverage n 0 i) +
        signedDyadic n (alternatingWitness n i) := by
  rw [martingaleTransform, Fin.sum_univ_succ]
  simp only [liftedBasisProcess, liftedAlternatingSigns, Fin.val_zero, Fin.val_succ,
    Fin.val_castSucc, Nat.sub_zero, leafAverage_signedLeafLift_zero,
    leafAverage_signedLeafLift_inl, sub_zero]
  rw [signedDyadicOperator_apply, ofLp_leafAverage_l1BasisWitness]
  congr 1
  rw [alternatingWitness_forward]
  change _ = (signedDyadicLinear n) _
  rw [map_sum]
  simp only [map_smul, map_sub]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [signedDyadicOperator_apply, signedDyadicOperator_apply,
    ofLp_leafAverage_l1BasisWitness, ofLp_leafAverage_l1BasisWitness]
  rfl

theorem liftedBasisProcess_inr (n : ℕ) (k : Fin (n + 2)) (i : Leaf n) :
    liftedBasisProcess (𝕜 := 𝕜) n k (Sum.inr i) =
      -liftedBasisProcess (𝕜 := 𝕜) n k (Sum.inl i) := by
  rcases k with ⟨k, hk⟩
  cases k with
  | zero => simp [liftedBasisProcess]
  | succ k =>
    change leafAverage (𝕜 := 𝕜) (n + 1) (k + 1) (signedLeafLift n _) (Sum.inr i) = _
    rw [leafAverage_signedLeafLift_inr]
    change _ = -leafAverage (𝕜 := 𝕜) (n + 1) (k + 1) (signedLeafLift n _) (Sum.inl i)
    rw [leafAverage_signedLeafLift_inl]

theorem lifted_transform_inr (n : ℕ) (i : Leaf n) :
    martingaleTransform (signedDyadicOperator (𝕜 := 𝕜) n) (liftedAlternatingSigns n)
      (liftedBasisProcess n) (Sum.inr i) =
      -martingaleTransform (signedDyadicOperator (𝕜 := 𝕜) n) (liftedAlternatingSigns n)
        (liftedBasisProcess n) (Sum.inl i) := by
  rw [martingaleTransform, martingaleTransform, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [liftedBasisProcess_inr, liftedBasisProcess_inr, ← smul_neg, ← map_neg]
  congr 2
  abel

def liftedDyadicValue (n : ℕ) : ℝ :=
  2 * (n : ℝ) / 3 + 5 / 9 + 4 / 9 * (-1 / 2 : ℝ) ^ n

theorem liftedDyadicValue_ge (n : ℕ) : 2 * (n : ℝ) / 3 ≤ liftedDyadicValue n := by
  have ha : |(-1 / 2 : ℝ) ^ n| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (by norm_num)
  have h := neg_abs_le ((-1 / 2 : ℝ) ^ n)
  dsimp [liftedDyadicValue]
  linarith

theorem lifted_transform_diagonal (n : ℕ) (i : Leaf n) :
    martingaleTransform (signedDyadicOperator (𝕜 := 𝕜) n) (liftedAlternatingSigns n)
      (liftedBasisProcess n) (Sum.inl i) i = (liftedDyadicValue n : 𝕜) := by
  rw [lifted_transform_inl]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [signedDyadic_basisAverage_diagonal n 0 (by omega),
    signedDyadic_alternatingWitness_diagonal, Nat.sub_zero, dyadicRowMean_explicit]
  simp only [liftedDyadicValue, RCLike.ofReal_add, RCLike.ofReal_mul,
    RCLike.ofReal_div, RCLike.ofReal_natCast, RCLike.ofReal_ofNat,
    RCLike.ofReal_one, RCLike.ofReal_pow, RCLike.ofReal_neg]
  have hs : ((-1 : 𝕜) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    simp
  simp only [div_pow]
  field_simp
  linear_combination 9 * (2 : 𝕜) ^ n * hs

theorem norm_lifted_transform_ge (n : ℕ) (i : Leaf (n + 1)) :
    2 * (n : ℝ) / 3 ≤ ‖martingaleTransform (signedDyadicOperator (𝕜 := 𝕜) n)
      (liftedAlternatingSigns n) (liftedBasisProcess n) i‖ := by
  have hleft (j : Leaf n) :
      2 * (n : ℝ) / 3 ≤ ‖martingaleTransform (signedDyadicOperator (𝕜 := 𝕜) n)
        (liftedAlternatingSigns n) (liftedBasisProcess n) (Sum.inl j)‖ := by
    have hpos : 0 ≤ liftedDyadicValue n :=
      (by positivity : 0 ≤ 2 * (n : ℝ) / 3).trans (liftedDyadicValue_ge n)
    calc
      2 * (n : ℝ) / 3 ≤ liftedDyadicValue n := liftedDyadicValue_ge n
      _ = ‖(liftedDyadicValue n : 𝕜)‖ := by simp [abs_of_nonneg hpos]
      _ = ‖martingaleTransform (signedDyadicOperator (𝕜 := 𝕜) n)
          (liftedAlternatingSigns n) (liftedBasisProcess n) (Sum.inl j) j‖ := by
        rw [lifted_transform_diagonal]
      _ ≤ _ := norm_le_pi_norm _ j
  cases i with
  | inl i => exact hleft i
  | inr i =>
    rw [lifted_transform_inr, norm_neg]
    exact hleft i

theorem eLpNorm_lifted_transform_ge (n : ℕ) :
    ENNReal.ofReal (2 * (n : ℝ) / 3) ≤
      eLpNorm (martingaleTransform (signedDyadicOperator (𝕜 := 𝕜) n)
        (liftedAlternatingSigns n) (liftedBasisProcess n)) 2 (leafUniform (n + 1)) := by
  rw [eLpNorm_leafUniform_two]
  exact ENNReal.ofReal_le_ofReal (leafL2Norm_ge_of_pointwise (n + 1) _ _ (by positivity)
    (norm_lifted_transform_ge n))

/-- The signed matrix has operator UMD constant at least `2*n/3`, directly for
the universal martingale-difference inequality. The extra independent sign
makes the initial value zero, so no terminal-value reduction is assumed. -/
theorem signedDyadic_UMDBound_lower (n : ℕ) (C : ℝ≥0)
    (hC : UMDBound.{0} 2 (signedDyadicOperator (𝕜 := 𝕜) n) C) :
    ENNReal.ofReal (2 * (n : ℝ) / 3) ≤ C := by
  let : MeasurableSpace (Leaf (n + 1)) := leafMeasurableSpace (n + 1)
  let : IsProbabilityMeasure (leafUniform (n + 1)) := leafUniform_probability (n + 1)
  have h := hC (Leaf (n + 1)) (leafMeasurableSpace (n + 1)) (leafUniform (n + 1))
    inferInstance (n + 1) (by omega) (leafFiltration (n + 1)) inferInstance
    (liftedBasisProcess n) (liftedBasisProcess_isLpMartingale n)
    (liftedAlternatingSigns n) (norm_liftedAlternatingSigns n)
  rw [eLpNorm_differenceSum_liftedBasisProcess, mul_one] at h
  exact (eLpNorm_lifted_transform_ge n).trans h

theorem signedDyadic_umdConstant_lower (n : ℕ) :
    ENNReal.ofReal (2 * (n : ℝ) / 3) ≤ umdConstant.{0} 2 (signedDyadicOperator (𝕜 := 𝕜) n) :=
  le_umdConstant (signedDyadic_UMDBound_lower n)

section OperatorNormLower

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ E] [CompleteSpace E]

end OperatorNormLower

end HilbertUMD
