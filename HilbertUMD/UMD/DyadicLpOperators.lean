import HilbertUMD.UMD.MartingaleProductEstimate
import HilbertUMD.Analysis.ScalarLpOperators
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual dyadic operator pairings and L2/L3 realizations. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace HilbertUMD

local instance factOneLeThreeDyadic : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Self-adjointness against arbitrary finite real functions. -/
theorem sum_mul_dyadicScalar (n : ℕ) (ε : Fin n → ℝ) (f g : Leaf n → ℝ) :
    ∑ x, f x * dyadicScalar n ε g x = ∑ x, dyadicScalar n ε f x * g x := by
  simp only [dyadicScalar_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := Leaf n))]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ε k * ∑ x, f x * dyadicDifference n k g x := by rw [Finset.mul_sum]; congr 1; ext x; ring
    _ = ε k * ∑ x, dyadicDifference n k f x * g x := by rw [sum_mul_dyadicDifference]
    _ = _ := by rw [Finset.mul_sum]; congr 1; ext x; ring

theorem integral_mul_dyadicScalar (n : ℕ) (ε : Fin n → ℝ) (f g : Leaf n → ℝ) :
    ∫ x, f x * dyadicScalar n ε g x ∂leafUniform n =
      ∫ x, dyadicScalar n ε f x * g x ∂leafUniform n := by
  rw [integral_leafUniform, integral_leafUniform, sum_mul_dyadicScalar]

section OrthogonalContractions
variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

theorem norm_contractive_sum_le (d : ι → E)
    (hd : Pairwise fun i j => inner 𝕜 (d i) (d j) = 0)
    (ε : ι → 𝕜) (hε : ∀ i, ‖ε i‖ ≤ 1) :
    ‖∑ i, ε i • d i‖ ≤ ‖∑ i, d i‖ := by
  have hεd : Pairwise fun i j => inner 𝕜 (ε i • d i) (ε j • d j) = 0 := by
    intro i j hij
    simp [inner_smul_left, inner_smul_right, hd hij]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sum_sq_of_pairwise_orthogonal _ hεd,
    norm_sum_sq_of_pairwise_orthogonal _ hd]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  apply pow_le_pow_left₀ (by positivity)
  simpa using mul_le_mul_of_nonneg_right (hε i) (norm_nonneg (d i))

end OrthogonalContractions

section MartingaleContractions
variable {Ω E 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {m : ℕ} {ℱ : Filtration (Fin (m + 1)) ‹MeasurableSpace Ω›}
  {f : Fin (m + 1) → Ω → E}

theorem IsLpMartingale.eLpNorm_transform_le (hf : IsLpMartingale f ℱ 2 μ)
    (ε : Fin m → 𝕜) (hε : ∀ k, ‖ε k‖ ≤ 1) :
    eLpNorm (martingaleTransform (ContinuousLinearMap.id 𝕜 E) ε f) 2 μ ≤
      eLpNorm (differenceSum f) 2 μ := by
  rw [← eLpNorm_congr_ae (hf.transform_l2Difference_coe ε),
    ← eLpNorm_congr_ae hf.sum_l2Difference_coe, ← Lp.enorm_def, ← Lp.enorm_def]
  change (↑‖∑ k, ε k • hf.l2Difference k‖₊ : ℝ≥0∞) ≤ ↑‖∑ k, hf.l2Difference k‖₊
  exact ENNReal.coe_le_coe.mpr
    (norm_contractive_sum_le hf.l2Difference hf.l2Difference_orthogonal ε hε)

end MartingaleContractions

/-- The scalar L2 contraction holds also for coefficients inside the unit
disk, as required for real coefficients in [-1,1]. -/
theorem eLpNorm_dyadicScalar_two_le {𝕜 : Type*} [RCLike 𝕜]
    (n : ℕ) (ε : Fin n → 𝕜) (hε : ∀ k, ‖ε k‖ ≤ 1) (f : Leaf n → 𝕜) :
    eLpNorm (dyadicScalar n ε f) 2 (leafUniform n) ≤ eLpNorm f 2 (leafUniform n) := by
  let P : Fin (n + 1) → Leaf n → 𝕜 := fun k => leafAverage (𝕜 := 𝕜) n k.val f
  have hP : IsLpMartingale P (leafFiltration n) 2 (leafUniform n) := isLpMartingale_leafAverage n 2 f
  have hfirst := hP.eLpNorm_transform_le ε hε
  have hlast := (UMDBound.finiteDyadicTerminal_two.{0} (𝕜 := 𝕜) umdBound_two_hilbert)
    n f (fun _ => 1) (by simp)
  have hone : martingaleTransform (ContinuousLinearMap.id 𝕜 𝕜) (fun _ : Fin n => 1) P =
      differenceSum P := by
    ext x
    simp [martingaleTransform, differenceSum]
  change eLpNorm (martingaleTransform (ContinuousLinearMap.id 𝕜 𝕜) (fun _ : Fin n => 1) P)
    2 (leafUniform n) ≤ _ at hlast
  rw [hone] at hlast
  simpa only [dyadicScalar_apply, P, one_mul, ENNReal.coe_one] using hfirst.trans hlast

theorem leafUniform_singleton_ne_zero (n : ℕ) (x : Leaf n) : leafUniform n {x} ≠ 0 := by
  simp [leafUniform, Measure.smul_apply]

/-- Uniform finite leaves have no nonempty null sets. Consequently Lp
representatives agree pointwise whenever they agree almost everywhere. -/
theorem eq_of_leaf_aeEq {E : Type*} (n : ℕ) {f g : Leaf n → E}
    (h : f =ᵐ[leafUniform n] g) : f = g := by
  funext x
  exact (ae_iff_of_countable.mp h) x (leafUniform_singleton_ne_zero n x)

section LpRealizations
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual quotient map from all functions on the finite probability
space to Lp; no values are discarded because every point has positive mass. -/
def leafToLpLinear (n : ℕ) (p : ℝ≥0∞) : (Leaf n → E) →ₗ[ℝ] Lp E p (leafUniform n) where
  toFun f := (leaf_memLp n p f).toLp f
  map_add' f g := (leaf_memLp n p f).toLp_add (leaf_memLp n p g)
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(leaf_memLp n p (c • f)).coeFn_toLp,
      (leaf_memLp n p f).coeFn_toLp, Lp.coeFn_smul c ((leaf_memLp n p f).toLp f)] with x hx hf hc
    simp only [RingHom.id_apply]
    rw [hx, hc]
    simp only [Pi.smul_apply, hf]

theorem leafToLpLinear_coe (n : ℕ) (p : ℝ≥0∞) (f : Leaf n → E) :
    (leafToLpLinear n p f : Leaf n → E) = f :=
  eq_of_leaf_aeEq n (leaf_memLp n p f).coeFn_toLp

theorem leafToLpLinear_surjective (n : ℕ) (p : ℝ≥0∞) :
    Function.Surjective (leafToLpLinear (E := E) n p) := by
  intro f
  refine ⟨f, ?_⟩
  apply Lp.ext
  exact (leaf_memLp n p (f : Leaf n → E)).coeFn_toLp

/-- Canonical finite-model identification with actual mathlib Lp classes. -/
def leafLpEquiv (n : ℕ) (p : ℝ≥0∞) : (Leaf n → E) ≃ₗ[ℝ] Lp E p (leafUniform n) :=
  LinearEquiv.ofBijective (leafToLpLinear n p) ⟨fun f g h => by
    simpa only [leafToLpLinear_coe] using congrArg (fun h : Lp E p (leafUniform n) => (h : Leaf n → E)) h,
    leafToLpLinear_surjective n p⟩

theorem leafLpEquiv_symm_apply (n : ℕ) (p : ℝ≥0∞) (f : Lp E p (leafUniform n)) :
    (leafLpEquiv n p).symm f = (f : Leaf n → E) := by
  have h : leafToLpLinear n p ((leafLpEquiv n p).symm f) = f :=
    (leafLpEquiv n p).apply_symm_apply f
  have hc := congrArg (fun h : Lp E p (leafUniform n) => (h : Leaf n → E)) h
  simpa only [leafToLpLinear_coe] using hc

instance leafLpFiniteDimensional [FiniteDimensional ℝ E] (n : ℕ) (p : ℝ≥0∞) :
    FiniteDimensional ℝ (Lp E p (leafUniform n)) :=
  FiniteDimensional.of_surjective (leafToLpLinear n p) (leafToLpLinear_surjective n p)

/-- Every finite raw-function linear map has an actual bounded Lp realization.
Sharp bounds, when needed, are established separately from this construction. -/
def leafLiftLp [FiniteDimensional ℝ E] (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : (Leaf n → E) →ₗ[ℝ] (Leaf n → E)) :
    Lp E p (leafUniform n) →L[ℝ] Lp E p (leafUniform n) :=
  (((leafLpEquiv n p).toLinearMap.comp T).comp (leafLpEquiv n p).symm.toLinearMap).toContinuousLinearMap

theorem leafLiftLp_coe [FiniteDimensional ℝ E] (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : (Leaf n → E) →ₗ[ℝ] (Leaf n → E)) (f : Lp E p (leafUniform n)) :
    (leafLiftLp n p T f : Leaf n → E) = T (f : Leaf n → E) := by
  change (leafToLpLinear n p (T ((leafLpEquiv n p).symm f)) : Leaf n → E) = _
  rw [leafToLpLinear_coe, leafLpEquiv_symm_apply]

end LpRealizations

def dyadicLpScalar (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : Fin n → ℝ) :
    Lp ℝ p (leafUniform n) →L[ℝ] Lp ℝ p (leafUniform n) :=
  leafLiftLp n p (dyadicScalar n ε)

theorem dyadicLpScalar_coe (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : Fin n → ℝ)
    (f : Lp ℝ p (leafUniform n)) :
    (dyadicLpScalar n p ε f : Leaf n → ℝ) = dyadicScalar n ε (f : Leaf n → ℝ) :=
  leafLiftLp_coe n p _ f

theorem dyadicLpScalar_compatible (n : ℕ) (ε : Fin n → ℝ) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (f : Leaf n → ℝ)
    (hp : MemLp f p (leafUniform n)) (hq : MemLp f q (leafUniform n)) :
    dyadicLpScalar n p ε (hp.toLp f) =ᵐ[leafUniform n] dyadicLpScalar n q ε (hq.toLp f) := by
  rw [dyadicLpScalar_coe, dyadicLpScalar_coe,
    eq_of_leaf_aeEq n hp.coeFn_toLp, eq_of_leaf_aeEq n hq.coeFn_toLp]

theorem dyadicLpScalar_integral_pairing (n : ℕ) (ε : Fin n → ℝ)
    (f g : Lp ℝ 2 (leafUniform n)) :
    (∫ x, dyadicLpScalar n 2 ε f x * g x ∂leafUniform n) =
      ∫ x, f x * dyadicLpScalar n 2 ε g x ∂leafUniform n := by
  rw [dyadicLpScalar_coe, dyadicLpScalar_coe]
  exact (integral_mul_dyadicScalar n ε f g).symm

/-- The same finite self-adjoint pairing is valid between any two actual Lp
realizations. Finiteness guarantees the integrability of every function. -/
theorem dyadicLpScalar_integral_pairing_exponents (n : ℕ) (ε : Fin n → ℝ)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp ℝ p (leafUniform n)) (g : Lp ℝ q (leafUniform n)) :
    (∫ x, dyadicLpScalar n p ε f x * g x ∂leafUniform n) =
      ∫ x, f x * dyadicLpScalar n q ε g x ∂leafUniform n := by
  rw [dyadicLpScalar_coe, dyadicLpScalar_coe]
  exact (integral_mul_dyadicScalar n ε f g).symm

/-- The generic coordinate amplification agrees pointwise with the genuine
finite dyadic transform in every coordinate. -/
theorem dyadicLpScalar_amplification_coe {ι : Type*} [Fintype ι]
    (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : Fin n → ℝ)
    (f : Lp (ι → ℝ) p (leafUniform n)) :
    (ScalarLp.amplification (leafUniform n) p (dyadicLpScalar n p ε) f : Leaf n → ι → ℝ) =
      fun x j => dyadicScalar n ε (fun y => f y j) x := by
  have h := eq_of_leaf_aeEq n
    (ScalarLp.coeFn_amplification (leafUniform n) p (dyadicLpScalar n p ε) f)
  rw [h]
  funext x j
  rw [dyadicLpScalar_coe, eq_of_leaf_aeEq n ((ScalarLp.coordinate j).coeFn_compLpL f)]
  rfl

theorem dyadicScalar_add_coeff {𝕜 : Type*} [RCLike 𝕜]
    (n : ℕ) (ε δ : Fin n → 𝕜) :
    dyadicScalar n (ε + δ) = dyadicScalar n ε + dyadicScalar n δ := by
  simp only [dyadicScalar, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem dyadicScalar_smul_coeff {𝕜 : Type*} [RCLike 𝕜]
    (n : ℕ) (c : 𝕜) (ε : Fin n → 𝕜) :
    dyadicScalar n (c • ε) = c • dyadicScalar n ε := by
  simp only [dyadicScalar, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- A complex martingale multiplier is the sum of two real-coefficient
transforms, with the imaginary part multiplied by i. -/
theorem dyadicScalar_complex_decomposition (n : ℕ) (ε : Fin n → ℂ) :
    dyadicScalar n ε = dyadicScalar n (fun k => (ε k).re : Fin n → ℂ) +
      Complex.I • dyadicScalar n (fun k => (ε k).im : Fin n → ℂ) := by
  rw [← dyadicScalar_smul_coeff, ← dyadicScalar_add_coeff]
  congr 1
  ext k
  simp [Complex.re_add_im, mul_comm Complex.I]

theorem abs_re_im_le_one_of_norm_le_one (z : ℂ) (hz : ‖z‖ ≤ 1) :
    |z.re| ≤ 1 ∧ |z.im| ≤ 1 :=
  ⟨z.abs_re_le_norm.trans hz, z.abs_im_le_norm.trans hz⟩

theorem leafAverage_re (n k : ℕ) (f : Leaf n → ℂ) (x : Leaf n) :
    (leafAverage (𝕜 := ℂ) n k f x).re =
      leafAverage (𝕜 := ℝ) n k (fun y => (f y).re) x := by
  simp [leafAverage, smul_eq_mul, Complex.mul_re]

theorem leafAverage_im (n k : ℕ) (f : Leaf n → ℂ) (x : Leaf n) :
    (leafAverage (𝕜 := ℂ) n k f x).im =
      leafAverage (𝕜 := ℝ) n k (fun y => (f y).im) x := by
  simp [leafAverage, smul_eq_mul, Complex.mul_im]

theorem dyadicScalar_re (n : ℕ) (ε : Fin n → ℝ) (f : Leaf n → ℂ) (x : Leaf n) :
    (dyadicScalar n (fun k => (ε k : ℂ)) f x).re =
      dyadicScalar n ε (fun y => (f y).re) x := by
  simp [dyadicScalar, leafAverageLinear, Complex.mul_re, leafAverage_re]

theorem dyadicScalar_im (n : ℕ) (ε : Fin n → ℝ) (f : Leaf n → ℂ) (x : Leaf n) :
    (dyadicScalar n (fun k => (ε k : ℂ)) f x).im =
      dyadicScalar n ε (fun y => (f y).im) x := by
  simp [dyadicScalar, leafAverageLinear, Complex.mul_im, leafAverage_im]

end HilbertUMD
