import HilbertUMD.UMD.DyadicMatrixData
import HilbertUMD.Matrices.MatrixCubic
import HilbertUMD.Matrices.MatrixBound
import HilbertUMD.Interfaces.MartingaleReduction
import HilbertUMD.Matrices.MatrixComplexBridge

/-! Checked assembly of the summation operator upper bound from the original
antisymmetric matrix estimate. All finite norm and scalar-field bridges here
are proved; the matrix estimate is supplied by the product/cubic argument. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace HilbertUMD

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem norm_vec_sq_le_sum (x : Vec 𝕜 n) : ‖x‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 := by
  have hn : ‖x‖ ≤ Real.sqrt (∑ j, ‖x j‖ ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    exact Finset.single_le_sum (fun i _ => sq_nonneg ‖x i‖) (Finset.mem_univ j)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt (by positivity))

/-- Coordinate amplification of a scalar L2 contraction maps finite L2(l1)
into L2(l∞) contractively. This is the identity-matrix remainder estimate. -/
theorem finiteL2_coordinateAction_l1_le {ι : Type*} [Fintype ι]
    (U : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜))
    (hU : ∀ f, (∑ i, ‖U f i‖ ^ 2) ≤ ∑ i, ‖f i‖ ^ 2)
    (f : ι → Vec 𝕜 n) :
    finiteL2 (normSeminorm 𝕜 (Vec 𝕜 n)) (coordinateAction U f) ≤ finiteL2 (l1Norm n) f := by
  apply (sq_le_sq₀ (finiteL2_nonneg _ _) (finiteL2_nonneg _ _)).mp
  simp only [finiteL2_sq, coe_normSeminorm]
  calc
    _ ≤ ∑ i, ∑ j, ‖coordinateAction U f i j‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => norm_vec_sq_le_sum _)
    _ = ∑ j, ∑ i, ‖U (fun k => f k j) i‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ j, ∑ i, ‖f i j‖ ^ 2 := Finset.sum_le_sum (fun j _ => hU _)
    _ = ∑ i, ∑ j, ‖f i j‖ ^ 2 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
      Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg (f i j)))

theorem total_coordinateAction {ι : Type*}
    (U : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜)) (f : ι → Vec 𝕜 n) (i : ι) :
    total (coordinateAction U f i) = U (fun k => total (f k)) i := by
  have hs : (fun k => total (f k)) = ∑ j, (fun k => f k j) := by ext k; simp [total]
  rw [hs, map_sum]
  simp [coordinateAction, total]

/-- The all-ones matrix remainder has the same dimension-independent bound. -/
theorem finiteL2_total_coordinateAction_le {ι : Type*} [Fintype ι]
    (U : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜))
    (hU : ∀ f, (∑ i, ‖U f i‖ ^ 2) ≤ ∑ i, ‖f i‖ ^ 2)
    (f : ι → Vec 𝕜 n) :
    finiteL2 (normSeminorm 𝕜 (Vec 𝕜 n)) (fun i _ => total (coordinateAction U f i)) ≤
      finiteL2 (l1Norm n) f := by
  apply (sq_le_sq₀ (finiteL2_nonneg _ _) (finiteL2_nonneg _ _)).mp
  simp only [finiteL2_sq, coe_normSeminorm, pi_norm_const, total_coordinateAction]
  exact (hU _).trans (Finset.sum_le_sum (fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_total_le n (f i)) 2))

set_option maxHeartbeats 800000 in
/-- Solving K=2Σ-J-I gives the summation estimate. The input is the actual
scalar contraction and an upper estimate for its antisymmetric matrix action. -/
theorem finiteL2_summation_of_tree_bound {ι : Type*} [Fintype ι]
    (U : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜))
    (hU : ∀ f, (∑ i, ‖U f i‖ ^ 2) ≤ ∑ i, ‖f i‖ ^ 2)
    (C : ℝ) (hC : ∀ f : ι → Vec 𝕜 n,
      finiteL2 (normSeminorm 𝕜 (Vec 𝕜 n))
        (fun i => treeMatrix (-1) (fun _ => (-1 : 𝕜)) n (coordinateAction U f i)) ≤
          C * finiteL2 (l1Norm n) f)
    (f : ι → Vec 𝕜 n) :
    finiteL2 (normSeminorm 𝕜 (Vec 𝕜 n)) (fun i => summation n (coordinateAction U f i)) ≤
      ((C + 2) / 2) * finiteL2 (l1Norm n) f := by
  let K : ι → Vec 𝕜 n := fun i => treeMatrix (-1) (fun _ => (-1 : 𝕜)) n (coordinateAction U f i)
  let J : ι → Vec 𝕜 n := fun i _ => total (coordinateAction U f i)
  let V : ι → Vec 𝕜 n := coordinateAction U f
  have he : (fun i => summation n (V i)) = (1/2 : 𝕜) • ((K + J) + V) := by
    ext i j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, K, J, V, treeMatrix_sign]
    ring
  rw [he]
  have hnorm : finiteL2 (normSeminorm 𝕜 (Vec 𝕜 n)) ((1/2 : 𝕜) • ((K + J) + V)) =
      (1/2 : ℝ) * finiteL2 (normSeminorm 𝕜 (Vec 𝕜 n)) ((K + J) + V) := by
    unfold finiteL2
    simp only [Pi.smul_apply, coe_normSeminorm, norm_smul, norm_div, norm_one,
      RCLike.norm_ofNat]
    exact sampleL2_mul (1/2) (by norm_num) _
  rw [hnorm]
  have ht := (finiteL2_add_le (normSeminorm 𝕜 (Vec 𝕜 n)) (K + J) V).trans
    (add_le_add (finiteL2_add_le (normSeminorm 𝕜 (Vec 𝕜 n)) K J) le_rfl)
  have hk := hC f
  have hj := finiteL2_total_coordinateAction_le U hU f
  have hv := finiteL2_coordinateAction_l1_le U hU f
  change finiteL2 _ K ≤ _ at hk
  change finiteL2 _ J ≤ _ at hj
  change finiteL2 _ V ≤ _ at hv
  nlinarith

theorem norm_leafLp_two {E : Type*} [NormedAddCommGroup E]
    (d : ℕ) (f : Lp E 2 (leafUniform d)) : ‖f‖ = leafL2Norm d (f : Leaf d → E) := by
  rw [Lp.norm_def, eLpNorm_leafUniform_two,
    ENNReal.toReal_ofReal (show 0 ≤ leafL2Norm d (f : Leaf d → E) from Real.sqrt_nonneg _)]

theorem cubicComplexL1Norm_leafToLp (d n : ℕ) (f : Leaf d → Vec ℂ n) :
    CubicLp.complexL1Norm (leafUniform d) 2 (leafToLpLinear d 2 f) =
      Real.sqrt ((2 : ℝ)⁻¹ ^ d) * finiteL2 (l1Norm n) f := by
  change ‖(CubicLp.complexToL1 (ι := Leaf n)).compLpL 2 (leafUniform d) (leafToLpLinear d 2 f)‖ = _
  rw [norm_leafLp_two]
  have h := eq_of_leaf_aeEq d ((CubicLp.complexToL1 (ι := Leaf n)).coeFn_compLpL (leafToLpLinear d 2 f))
  rw [h, leafToLpLinear_coe, leafL2Norm_eq_finiteL2 (𝕜 := ℂ)]
  congr 1
  unfold finiteL2
  congr 1
  funext x
  exact PiLp.norm_eq_of_L1 _

theorem dyadicScalar_contraction_le (d : ℕ) (ε : Fin d → 𝕜) (hε : ∀ k, ‖ε k‖ ≤ 1)
    (f : Leaf d → 𝕜) : (∑ x, ‖dyadicScalar d ε f x‖ ^ 2) ≤ ∑ x, ‖f x‖ ^ 2 := by
  have h := eLpNorm_dyadicScalar_two_le d ε hε f
  rw [eLpNorm_leafUniform_two, eLpNorm_leafUniform_two] at h
  have hn := (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ leafL2Norm d f from Real.sqrt_nonneg _)).mp h
  have hsq := pow_le_pow_left₀ (show 0 ≤ leafL2Norm d (dyadicScalar d ε f) from Real.sqrt_nonneg _) hn 2
  unfold leafL2Norm at hsq
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hsq
  exact (mul_le_mul_iff_right₀ (by positivity)).mp hsq

/-- The finite raw-function estimate is exactly the required terminal-value
test bound. The transform here omits the initial conditional mean, while the
denominator is the full terminal norm, as in FiniteDyadicTerminalBound. -/
theorem finiteDyadicTerminal_summation_of_raw (n : ℕ) (C : ℝ≥0)
    (hC : ∀ (d : ℕ) (ε : Fin d → 𝕜), (∀ k, ‖ε k‖ = 1) → ∀ f : Leaf d → Vec 𝕜 n,
      finiteL2 (normSeminorm 𝕜 (Vec 𝕜 n)) (fun x => summation n (coordinateAction (dyadicScalar d ε) f x)) ≤
        (C : ℝ) * finiteL2 (l1Norm n) f) :
    FiniteDyadicTerminalBound 2 (summationOperator (𝕜 := 𝕜) n) C := by
  apply (finiteDyadicTerminalBound_two_iff _ _).mpr
  intro d f ε hε
  let fv : Leaf d → Vec 𝕜 n := fun x => WithLp.ofLp (f x)
  let hlin : ∀ (x : Vec 𝕜 n) (i : Leaf n), ‖summationLinear n x i‖ ≤ l1Norm n x := summation_le_l1 n
  change leafL2Norm d (martingaleTransform (asL1Operator n (summationLinear n) hlin) ε
    (fun k : Fin (d+1) => leafAverage (𝕜 := 𝕜) d k.val
      (fun x => (WithLp.toLp 1 (fv x) : L1Vec 𝕜 n)))) ≤
    (C : ℝ) * leafL2Norm d (fun x => (WithLp.toLp 1 (fv x) : L1Vec 𝕜 n))
  rw [asL1_dyadic_transform (summationLinear n) hlin d ε fv,
    leafL2Norm_toL1, leafL2Norm_eq_finiteL2 (𝕜 := 𝕜)]
  calc
    _ ≤ Real.sqrt ((2 : ℝ)⁻¹ ^ d) * ((C : ℝ) * finiteL2 (l1Norm n) fv) :=
      mul_le_mul_of_nonneg_left (hC d ε hε fv) (Real.sqrt_nonneg _)
    _ = _ := by ring

def summationUpperFactor (P : ℝ≥0) : ℝ≥0 :=
  ⟨(127 / 40) * Real.sqrt (9 * (8 + 2 * (P : ℝ))) + 2, by positivity⟩

def summationDepthBound (P : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  ⟨(summationUpperFactor P : ℝ) * Real.sqrt ((n : ℝ) + 1), by positivity⟩

theorem summation_matrix_constant_le (n : ℕ) (P : ℝ≥0) :
    matrixUpperConstant n 2 P + 2 ≤ (summationDepthBound P n : ℝ) := by
  have hm := matrixUpperConstant_le_mul_sqrt_succ n 2 P
  have hs : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  change matrixUpperConstant n 2 P + 2 ≤
    ((127 / 40) * Real.sqrt (9 * (8 + 2 * (P : ℝ))) + 2) * Real.sqrt ((n : ℝ) + 1)
  simp only [show (2 : ℝ) * 2 ^ 2 = 8 by norm_num] at hm
  nlinarith

theorem dyadic_tree_complex_realCoeff_finiteL2_le (d n : ℕ) (ε : Fin d → ℝ)
    (P : ℝ≥0) (R : ScalarMatrixData (leafUniform d) (-1) 2 P)
    (hR : R.atThree = dyadicLpScalar d 3 ε) (f : Leaf d → Vec ℂ n) :
    finiteL2 (normSeminorm ℂ (Vec ℂ n))
      (fun x => treeMatrix (-1) (fun _ => (-1 : ℂ)) n
        (coordinateAction (dyadicScalar d (fun k => (ε k : ℂ))) f x)) ≤
          matrixUpperConstant n 2 P * finiteL2 (l1Norm n) f := by
  have hAgree : ∀ (g : Leaf d → ℝ) (hp : MemLp g 2 (leafUniform d)) (hq : MemLp g 3 (leafUniform d)),
      dyadicLpScalar d 2 ε (hp.toLp g) =ᵐ[leafUniform d] R.atThree (hq.toLp g) := by
    intro g hp hq
    rw [hR]
    exact dyadicLpScalar_compatible d ε 2 3 g hp hq
  have hSkew : ∀ (g h : Lp ℝ 2 (leafUniform d)),
      (∫ x, dyadicLpScalar d 2 ε g x * h x ∂leafUniform d) =
        -(-1 : ℝ) * ∫ x, g x * dyadicLpScalar d 2 ε h x ∂leafUniform d := by
    intro g h
    simpa using dyadicLpScalar_integral_pairing d ε g h
  have hm := R.matrix_bound_complex (leafUniform d) (by norm_num) (by norm_num) P.coe_nonneg
    (fun _ => (-1 : ℝ)) (by intro k; norm_num) n (dyadicLpScalar d 2 ε) hAgree hSkew
    (leafToLpLinear d 2 f)
  rw [norm_leafLp_two, dyadic_matrix_complexify_coe, leafToLpLinear_coe,
    leafL2Norm_eq_finiteL2 (𝕜 := ℂ), cubicComplexL1Norm_leafToLp] at hm
  apply (mul_le_mul_iff_right₀ (show 0 < Real.sqrt ((2 : ℝ)⁻¹ ^ d) by positivity)).mp
  simpa only [Complex.ofReal_neg, Complex.ofReal_one, mul_left_comm] using hm

theorem dyadic_tree_complex_finiteL2_le (P : ℝ≥0)
    (hP : ∀ (d : ℕ) (ε : Fin d → ℝ), (∀ k, |ε k| ≤ 1) →
      ∃ R : ScalarMatrixData (leafUniform d) (-1) 2 P,
        R.atThree = dyadicLpScalar d 3 ε)
    (d n : ℕ) (ε : Fin d → ℂ) (hε : ∀ k, ‖ε k‖ ≤ 1) (f : Leaf d → Vec ℂ n) :
    finiteL2 (normSeminorm ℂ (Vec ℂ n))
      (fun x => treeMatrix (-1) (fun _ => (-1 : ℂ)) n (coordinateAction (dyadicScalar d ε) f x)) ≤
        (2 * matrixUpperConstant n 2 P) * finiteL2 (l1Norm n) f := by
  let er : Fin d → ℝ := fun k => (ε k).re
  let ei : Fin d → ℝ := fun k => (ε k).im
  obtain ⟨Rr, hr⟩ := hP d er (fun k => (abs_re_im_le_one_of_norm_le_one (ε k) (hε k)).1)
  obtain ⟨Ri, hi⟩ := hP d ei (fun k => (abs_re_im_le_one_of_norm_le_one (ε k) (hε k)).2)
  have hreal := dyadic_tree_complex_realCoeff_finiteL2_le d n er P Rr hr f
  have himag := dyadic_tree_complex_realCoeff_finiteL2_le d n ei P Ri hi f
  let A : Leaf d → Vec ℂ n := fun x => treeMatrix (-1) (fun _ => (-1 : ℂ)) n
    (coordinateAction (dyadicScalar d (fun k => (er k : ℂ))) f x)
  let B : Leaf d → Vec ℂ n := fun x => treeMatrix (-1) (fun _ => (-1 : ℂ)) n
    (coordinateAction (dyadicScalar d (fun k => (ei k : ℂ))) f x)
  have hcoord : coordinateAction (dyadicScalar d ε) f =
      coordinateAction (dyadicScalar d (fun k => (er k : ℂ))) f +
        Complex.I • coordinateAction (dyadicScalar d (fun k => (ei k : ℂ))) f := by
    ext x j
    simp only [coordinateAction, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply]
    rw [dyadicScalar_complex_decomposition]
    rfl
  have htree : (fun x => treeMatrix (-1) (fun _ => (-1 : ℂ)) n
      (coordinateAction (dyadicScalar d ε) f x)) = A + Complex.I • B := by
    rw [hcoord]
    ext x j
    simp only [Pi.add_apply, Pi.smul_apply, treeMatrix_add, treeMatrix_smul, A, B]
  rw [htree]
  have hb : finiteL2 (normSeminorm ℂ (Vec ℂ n)) (Complex.I • B) =
      finiteL2 (normSeminorm ℂ (Vec ℂ n)) B := by
    simp only [finiteL2, Pi.smul_apply, coe_normSeminorm, norm_smul, Complex.norm_I, one_mul]
  have ht := finiteL2_add_le (normSeminorm ℂ (Vec ℂ n)) A (Complex.I • B)
  rw [hb] at ht
  change finiteL2 _ A ≤ _ at hreal
  change finiteL2 _ B ≤ _ at himag
  linarith

theorem dyadic_summation_complex_bound (P : ℝ≥0)
    (hP : ∀ (d : ℕ) (ε : Fin d → ℝ), (∀ k, |ε k| ≤ 1) →
      ∃ R : ScalarMatrixData (leafUniform d) (-1) 2 P,
        R.atThree = dyadicLpScalar d 3 ε) (n : ℕ) :
    FiniteDyadicTerminalBound 2 (summationOperator (𝕜 := ℂ) n) (summationDepthBound P n) := by
  apply finiteDyadicTerminal_summation_of_raw
  intro d ε hε f
  have he : ∀ k, ‖ε k‖ ≤ 1 := fun k => le_of_eq (hε k)
  have ht := finiteL2_summation_of_tree_bound (dyadicScalar d ε)
    (dyadicScalar_contraction_le d ε he) (2 * matrixUpperConstant n 2 P)
    (dyadic_tree_complex_finiteL2_le P hP d n ε he) f
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (finiteL2_nonneg _ _)
  have hb := summation_matrix_constant_le n P
  linarith

/-- The explicit matrix coefficient supplied by the checked scalar estimates. -/
def summationUMDUpperConstant : ℝ≥0 := summationUpperFactor 1097

/-- The complex p=2 summation estimate with its numerical witness exposed. -/
theorem summation_umdBound_complex (n : ℕ) :
    UMDBound.{0} 2 (summationOperator (𝕜 := ℂ) n)
      ⟨(summationUMDUpperConstant : ℝ) * Real.sqrt ((n : ℝ) + 1), by positivity⟩ := by
  apply Interfaces.complex_umdBound_of_finiteDyadicTerminalBound
  apply dyadic_summation_complex_bound 1097
  intro d ε hε
  obtain ⟨R, hR, _⟩ := dyadic_scalarMatrixData d ε hε
  exact ⟨R, hR⟩

theorem summation_umdConstant_upper_complex (n : ℕ) :
    umdConstant.{0} 2 (summationOperator (𝕜 := ℂ) n) ≤
      ENNReal.ofReal ((summationUMDUpperConstant : ℝ) * Real.sqrt ((n : ℝ) + 1)) := by
  let C : ℝ≥0 := ⟨(summationUMDUpperConstant : ℝ) * Real.sqrt ((n : ℝ) + 1), by positivity⟩
  change _ ≤ ENNReal.ofReal (C : ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  exact umdConstant_le (summation_umdBound_complex n)

/-- The complex p=2 summation-operator estimate, with one universal
coefficient chosen before the depth. -/
theorem exists_summation_umdBound_complex :
    ∃ A : ℝ≥0, ∀ n : ℕ,
      UMDBound.{0} 2 (summationOperator (𝕜 := ℂ) n)
        ⟨(A : ℝ) * Real.sqrt ((n : ℝ) + 1), by positivity⟩ :=
  ⟨summationUMDUpperConstant, summation_umdBound_complex⟩

theorem exists_summation_umdConstant_upper_complex :
    ∃ A : ℝ≥0, ∀ n : ℕ,
      umdConstant.{0} 2 (summationOperator (𝕜 := ℂ) n) ≤
        ENNReal.ofReal ((A : ℝ) * Real.sqrt ((n : ℝ) + 1)) :=
  ⟨summationUMDUpperConstant, summation_umdConstant_upper_complex⟩

end HilbertUMD
