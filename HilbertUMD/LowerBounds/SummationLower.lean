import HilbertUMD.UMD.Rademacher
import HilbertUMD.Foundations.OperatorSpaces

/-! A direct dyadic lower bound for the summation operator and X_n.
The argument uses the actual conditional averages of the coordinate-vector
witness and finite Rademacher orthogonality. No external comparison is used. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace HilbertUMD

def summationAverageDiagonal (n k : ℕ) (i : Leaf n) : ℝ :=
  summation n (basisAverage (𝕜 := ℝ) n k i) i

theorem total_basisAverage_zero (n : ℕ) (i : Leaf n) :
    total (basisAverage (𝕜 := ℝ) n 0 i) = 1 := by
  simp [total, basisAverage, dyadicBlock, card_leaf]

theorem left_basisAverage_zero (n : ℕ) (i : Leaf (n+1)) (j : Leaf n) :
    left (basisAverage (𝕜 := ℝ) (n+1) 0 i) = (1/2 : ℝ) • basisAverage n 0 j := by
  ext k
  simp [left, basisAverage, dyadicBlock, pow_succ, mul_inv_rev, smul_eq_mul]

theorem right_basisAverage_zero (n : ℕ) (i : Leaf (n+1)) (j : Leaf n) :
    right (basisAverage (𝕜 := ℝ) (n+1) 0 i) = (1/2 : ℝ) • basisAverage n 0 j := by
  ext k
  simp [right, basisAverage, dyadicBlock, pow_succ, mul_inv_rev, smul_eq_mul]

theorem summationAverageDiagonal_zero_inl (n : ℕ) (i : Leaf n) :
    summationAverageDiagonal (n+1) 0 (Sum.inl i) = summationAverageDiagonal n 0 i / 2 := by
  change summation n (left _) i = _
  rw [left_basisAverage_zero n _ i, summation_smul]
  simp [summationAverageDiagonal, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem summationAverageDiagonal_zero_inr (n : ℕ) (i : Leaf n) :
    summationAverageDiagonal (n+1) 0 (Sum.inr i) =
      summationAverageDiagonal n 0 i / 2 + 1/2 := by
  change total (left _) + summation n (right _) i = _
  rw [left_basisAverage_zero n _ i, right_basisAverage_zero n _ i,
    total_smul, total_basisAverage_zero, summation_smul]
  simp [summationAverageDiagonal, smul_eq_mul]
  ring

theorem summationAverageDiagonal_succ_inl (n k : ℕ) (i : Leaf n) :
    summationAverageDiagonal (n+1) (k+1) (Sum.inl i) = summationAverageDiagonal n k i := by
  change summation n (left _) i = _
  rw [left_basisAverage_inl]
  rfl

theorem summationAverageDiagonal_succ_inr (n k : ℕ) (i : Leaf n) :
    summationAverageDiagonal (n+1) (k+1) (Sum.inr i) = summationAverageDiagonal n k i := by
  change total (left _) + summation n (right _) i = _
  rw [left_basisAverage_inr, right_basisAverage_inr, total_zero, zero_add]
  rfl

def summationTransformDiagonal (n : ℕ) (i : Leaf n) : ℝ :=
  ∑ k : Fin n, (-1 : ℝ)^(k.val+1) *
    (summationAverageDiagonal n (k.val+1) i - summationAverageDiagonal n k.val i)

theorem summationTransformDiagonal_inl (n : ℕ) (i : Leaf n) :
    summationTransformDiagonal (n+1) (Sum.inl i) =
      -summationTransformDiagonal n i - summationAverageDiagonal n 0 i / 2 := by
  rw [summationTransformDiagonal, Fin.sum_univ_succ]
  simp only [Fin.val_zero, zero_add, pow_one, Fin.val_succ,
    summationAverageDiagonal_succ_inl, summationAverageDiagonal_zero_inl]
  have ht : (∑ k : Fin n, (-1 : ℝ)^(k.val+1+1) *
      (summationAverageDiagonal n (k.val+1) i - summationAverageDiagonal n k.val i)) =
        -summationTransformDiagonal n i := by
    simp only [pow_succ, summationTransformDiagonal, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [ht]
  ring

theorem summationTransformDiagonal_inr (n : ℕ) (i : Leaf n) :
    summationTransformDiagonal (n+1) (Sum.inr i) =
      -summationTransformDiagonal n i - summationAverageDiagonal n 0 i / 2 + 1/2 := by
  rw [summationTransformDiagonal, Fin.sum_univ_succ]
  simp only [Fin.val_zero, zero_add, pow_one, Fin.val_succ,
    summationAverageDiagonal_succ_inr, summationAverageDiagonal_zero_inr]
  have ht : (∑ k : Fin n, (-1 : ℝ)^(k.val+1+1) *
      (summationAverageDiagonal n (k.val+1) i - summationAverageDiagonal n k.val i)) =
        -summationTransformDiagonal n i := by
    simp only [pow_succ, summationTransformDiagonal, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [ht]
  ring

def summationAverageCoeff (k : ℕ) : ℝ := -(1/2 : ℝ)^(k+2)
def summationLowerCoeff (k : ℕ) : ℝ := -(-1 : ℝ)^k/3 + (1/2 : ℝ)^(k+1)/6
def summationLowerMean (n : ℕ) : ℝ := ((-1 : ℝ)^n - (1/2 : ℝ)^n)/6

theorem summationAverageDiagonal_zero_rademacher (n : ℕ) (i : Leaf n) :
    summationAverageDiagonal n 0 i = 1/2 + (1/2 : ℝ)^(n+1) +
      leafRademacherSum n (fun k => summationAverageCoeff k.val) i := by
  induction n with
  | zero => norm_num [summationAverageDiagonal, summation, basisAverage, dyadicBlock,
      leafRademacherSum, Leaf, Subsingleton.elim i (0 : Fin 1)]
  | succ n ih =>
    have htail (i : Leaf n) :
        leafRademacherSum n (fun k => summationAverageCoeff k.succ.val) i =
          leafRademacherSum n (fun k => summationAverageCoeff k.val) i / 2 := by
      simp only [leafRademacherSum, summationAverageCoeff, Fin.val_succ,
        pow_succ, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    cases i with
    | inl i =>
      rw [summationAverageDiagonal_zero_inl, ih i, leafRademacherSum_inl, htail]
      norm_num [summationAverageCoeff, pow_succ]
      ring
    | inr i =>
      rw [summationAverageDiagonal_zero_inr, ih i, leafRademacherSum_inr, htail]
      norm_num [summationAverageCoeff, pow_succ]
      ring

theorem summationTransformDiagonal_rademacher (n : ℕ) (i : Leaf n) :
    summationTransformDiagonal n i = summationLowerMean n +
      leafRademacherSum n (fun k => summationLowerCoeff k.val) i := by
  induction n with
  | zero => simp [summationTransformDiagonal, summationLowerMean, leafRademacherSum]
  | succ n ih =>
    have htail (i : Leaf n) :
        leafRademacherSum n (fun k => summationLowerCoeff k.succ.val) i =
          -leafRademacherSum n (fun k => summationLowerCoeff k.val) i -
            leafRademacherSum n (fun k => summationAverageCoeff k.val) i / 2 := by
      simp only [leafRademacherSum, summationLowerCoeff, summationAverageCoeff,
        Fin.val_succ, pow_succ, Finset.sum_div, ← Finset.sum_neg_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    cases i with
    | inl i =>
      rw [summationTransformDiagonal_inl, ih i, summationAverageDiagonal_zero_rademacher,
        leafRademacherSum_inl, htail]
      norm_num [summationLowerMean, summationLowerCoeff, pow_succ]
      ring
    | inr i =>
      rw [summationTransformDiagonal_inr, ih i, summationAverageDiagonal_zero_rademacher,
        leafRademacherSum_inr, htail]
      norm_num [summationLowerMean, summationLowerCoeff, pow_succ]
      ring

theorem abs_summationLowerCoeff_ge (k : ℕ) : 1/4 ≤ |summationLowerCoeff k| := by
  have hpow : (1/2 : ℝ)^(k+1) ≤ 1/2 := by
    rw [pow_succ]
    calc
      _ ≤ 1 * (1/2 : ℝ) := mul_le_mul_of_nonneg_right
        (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)) (by norm_num)
      _ = _ := by ring
  have hpos : 0 ≤ (1/2 : ℝ)^(k+1) := by positivity
  have hs : ((-1 : ℝ)^k)^2 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; simp
  rcases sq_eq_one_iff.mp hs with h | h
  · have ha := neg_le_abs (summationLowerCoeff k)
    dsimp [summationLowerCoeff] at ha ⊢
    rw [h] at ha ⊢
    linarith
  · have ha := le_abs_self (summationLowerCoeff k)
    dsimp [summationLowerCoeff] at ha ⊢
    rw [h] at ha ⊢
    linarith

theorem sum_sq_shifted_leafRademacherSum (n : ℕ) (a : ℝ) (c : Fin n → ℝ) :
    ∑ x : Leaf n, (a + leafRademacherSum n c x)^2 =
      (2 : ℝ)^n * (a^2 + ∑ k : Fin n, c k ^ 2) := by
  induction n generalizing a with
  | zero => simp [leafRademacherSum, Leaf]
  | succ n ih =>
    rw [Fintype.sum_sum_type]
    simp only [leafRademacherSum_inl, leafRademacherSum_inr, ← add_assoc]
    rw [ih, ih, Fin.sum_univ_succ, pow_succ]
    ring

theorem leafL2Norm_summationTransformDiagonal_sq (n : ℕ) :
    leafL2Norm n (summationTransformDiagonal n) ^ 2 =
      summationLowerMean n ^ 2 + ∑ k : Fin n, summationLowerCoeff k.val ^ 2 := by
  unfold leafL2Norm
  rw [Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs, summationTransformDiagonal_rademacher]
  rw [sum_sq_shifted_leafRademacherSum]
  rw [← mul_assoc, ← mul_pow]
  norm_num

theorem summationTransformDiagonal_L2_lower (n : ℕ) :
    Real.sqrt (n : ℝ) / 4 ≤ leafL2Norm n (summationTransformDiagonal n) := by
  have hsq : (n : ℝ) / 16 ≤ ∑ k : Fin n, summationLowerCoeff k.val ^ 2 := by
    calc
      _ = ∑ _k : Fin n, (1/16 : ℝ) := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/4) (abs_summationLowerCoeff_ge k.val) 2
        norm_num only [sq_abs] at h
        linarith
  apply (sq_le_sq₀ (by positivity)
    (show 0 ≤ leafL2Norm n (summationTransformDiagonal n) from Real.sqrt_nonneg _)).mp
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n), leafL2Norm_summationTransformDiagonal_sq]
  nlinarith [sq_nonneg (summationLowerMean n)]

section ScalarFields
variable {𝕜 : Type*} [RCLike 𝕜]

theorem summation_ofReal_rclike (n : ℕ) (x : Vec ℝ n) (i : Leaf n) :
    summation n (fun j => (x j : 𝕜)) i = ((summation n x i : ℝ) : 𝕜) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases i with
    | inl i =>
      change summation n (fun j => ((left x j : ℝ) : 𝕜)) i = ((summation n (left x) i : ℝ) : 𝕜)
      exact ih (left x) i
    | inr i =>
      change total (fun j => ((left x j : ℝ) : 𝕜)) +
        summation n (fun j => ((right x j : ℝ) : 𝕜)) i = _
      rw [ih]
      simp [summation, total]

theorem basisAverage_ofReal_rclike (n k : ℕ) (i : Leaf n) :
    basisAverage (𝕜 := 𝕜) n k i = fun j => ((basisAverage (𝕜 := ℝ) n k i j : ℝ) : 𝕜) := by
  ext j
  by_cases hj : j ∈ dyadicBlock n k i <;> simp [basisAverage, hj, map_ofNat]

theorem summationAverageDiagonal_ofReal (n k : ℕ) (i : Leaf n) :
    summation n (basisAverage (𝕜 := 𝕜) n k i) i = (summationAverageDiagonal n k i : 𝕜) := by
  rw [basisAverage_ofReal_rclike, summation_ofReal_rclike]
  rfl

def summationLowerSigns (n : ℕ) (k : Fin n) : 𝕜 := (-1 : 𝕜)^(k.val+1)

theorem norm_summationLowerSigns (n : ℕ) (k : Fin n) :
    ‖summationLowerSigns (𝕜 := 𝕜) n k‖ = 1 := by simp [summationLowerSigns]

def summationLowerTransform (n : ℕ) : Leaf n → Vec 𝕜 n :=
  martingaleTransform (summationOperator (𝕜 := 𝕜) n) (summationLowerSigns n)
    (fun k : Fin (n+1) => leafAverage (𝕜 := 𝕜) n k.val (l1BasisWitness n))

theorem summationLowerTransform_diagonal (n : ℕ) (i : Leaf n) :
    summationLowerTransform (𝕜 := 𝕜) n i i = (summationTransformDiagonal n i : 𝕜) := by
  unfold summationLowerTransform martingaleTransform summationTransformDiagonal
  simp only [map_sub, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    RCLike.ofReal_sum, RCLike.ofReal_mul, RCLike.ofReal_pow,
    RCLike.ofReal_neg, RCLike.ofReal_one]
  apply Finset.sum_congr rfl
  intro k _
  change (-1 : 𝕜)^(k.val+1) *
    (summation n (WithLp.ofLp (leafAverage (𝕜 := 𝕜) n k.succ.val (l1BasisWitness n) i)) i -
      summation n (WithLp.ofLp (leafAverage (𝕜 := 𝕜) n k.castSucc.val (l1BasisWitness n) i)) i) = _
  rw [ofLp_leafAverage_l1BasisWitness, ofLp_leafAverage_l1BasisWitness,
    summationAverageDiagonal_ofReal, summationAverageDiagonal_ofReal]
  rfl

theorem summationLowerTransform_L2_lower (n : ℕ) :
    Real.sqrt (n : ℝ) / 4 ≤ leafL2Norm n (summationLowerTransform (𝕜 := 𝕜) n) := by
  apply (summationTransformDiagonal_L2_lower n).trans
  unfold leafL2Norm
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  have h : ‖summationTransformDiagonal n i‖ ≤ ‖summationLowerTransform (𝕜 := 𝕜) n i‖ := by
    calc
      _ = ‖(summationTransformDiagonal n i : 𝕜)‖ := (RCLike.norm_ofReal _).symm
      _ = ‖summationLowerTransform (𝕜 := 𝕜) n i i‖ := by rw [summationLowerTransform_diagonal]
      _ ≤ _ := norm_le_pi_norm _ _
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- Direct finite-witness bound. The checked independent-sign terminal lift
improves the centered-witness coefficient 1/8 to 1/4. No external reduction
or Hilbert/UMD comparison is used. -/
theorem summation_UMDBound_sqrt_lower_quarter (n : ℕ) (C : ℝ≥0)
    (hC : UMDBound.{0} 2 (summationOperator (𝕜 := 𝕜) n) C) :
    ENNReal.ofReal (Real.sqrt (n : ℝ) / 4) ≤ C := by
  have h := (finiteDyadicTerminalBound_two_iff _ _).mp hC.finiteDyadicTerminal_two
    n (l1BasisWitness n) (summationLowerSigns n) (norm_summationLowerSigns n)
  rw [leafL2Norm_l1BasisWitness, mul_one] at h
  have hl := (summationLowerTransform_L2_lower (𝕜 := 𝕜) n).trans h
  exact (ENNReal.ofReal_le_ofReal hl).trans_eq ENNReal.ofReal_coe_nnreal

theorem summation_umdConstant_sqrt_lower_quarter (n : ℕ) :
    ENNReal.ofReal (Real.sqrt (n : ℝ) / 4) ≤
      umdConstant.{0} 2 (summationOperator (𝕜 := 𝕜) n) :=
  le_umdConstant (summation_UMDBound_sqrt_lower_quarter n)

theorem summation_umdConstant_sqrt_depth_lower_direct (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (Real.sqrt ((n : ℝ) + 1) / (4 * Real.sqrt 2)) ≤
      umdConstant.{0} 2 (summationOperator (𝕜 := 𝕜) n) := by
  apply (ENNReal.ofReal_le_ofReal ?_).trans (summation_umdConstant_sqrt_lower_quarter n)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1), Real.sq_sqrt (Nat.cast_nonneg n)]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num
  nlinarith

/-- The sqrt(n+1) form retains the exact conversion factor sqrt(2). -/
theorem xSpace_umdConstant_sqrt_depth_lower_direct (n : ℕ) (hn : 1 ≤ n)
    [NormedSpace ℝ (XSpace 𝕜 n)] :
    ENNReal.ofReal (Real.sqrt ((n : ℝ) + 1) / (4 * Real.sqrt 2)) ≤
      umdConstant.{0} 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) :=
  (summation_umdConstant_sqrt_depth_lower_direct n hn).trans umdConstant_summation_le_xSpace

end ScalarFields
end HilbertUMD
