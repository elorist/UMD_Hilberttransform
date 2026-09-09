import HilbertUMD.Matrices.MatrixCubic
import HilbertUMD.Analysis.MixedNorm
import HilbertUMD.Analysis.CubicLp

/-! Mixed Hölder estimates for the original matrix energy increments. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace HilbertUMD

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S)

/-- Hölder after an a.e. pointwise domination, retaining extended norms. -/
theorem abs_integral_le_eLpNorm_product {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    (f : S → ℝ) (a : S → E) (b : S → F)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖a x‖ * ‖b x‖) :
    ENNReal.ofReal |∫ x, f x ∂μ| ≤ eLpNorm a p μ * eLpNorm b q μ := by
  have hInt : ENNReal.ofReal |∫ x, f x ∂μ| ≤ eLpNorm f 1 μ := by
    simpa only [Real.enorm_eq_ofReal_abs, eLpNorm_one_eq_lintegral_enorm] using
      enorm_integral_le_lintegral_enorm (μ := μ) f
  have hMono : eLpNorm f 1 μ ≤ eLpNorm (fun x => ‖a x‖ * ‖b x‖) 1 μ := by
    apply eLpNorm_mono_ae
    filter_upwards [h] with x hx
    simpa only [norm_mul, norm_norm] using hx
  have hHolder := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (p := p) (q := q) (r := 1) ha hb (fun u v => ‖u‖ * ‖v‖) 1
    (Filter.Eventually.of_forall fun x => by simp only [norm_mul, norm_norm, NNReal.coe_one, one_mul, le_refl])
  exact hInt.trans (hMono.trans (by simpa only [ENNReal.coe_one, one_mul] using hHolder))

theorem abs_sum_mul_le_mass (b w : ι → ℝ) (g : ℝ) (hb : ∀ i, |b i| ≤ g) :
    |∑ i, b i * w i| ≤ |g| * ∑ i, |w i| := by
  calc
    _ ≤ ∑ i, |b i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |b i| * |w i| := by simp only [abs_mul]
    _ ≤ ∑ i, |g| * |w i| := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right ((hb i).trans (le_abs_self _)) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The second integral in the energy increment: a bounded row paired with
an L(3/2)(l1) product output. No skew identity is assumed in this estimate. -/
theorem block_pair_integral_bound (g : S → ℝ) (b w : S → ι → ℝ)
    (hg : MemLp g 3 μ)
    (hw : MemLp (fun s => (WithLp.toLp 1 (w s) : PiLp 1 (fun _ : ι => ℝ))) (3/2) μ)
    (hb : ∀ᵐ s ∂μ, ∀ i, |b s i| ≤ g s) :
    ENNReal.ofReal |∫ s, ∑ i, b s i * w s i ∂μ| ≤
      eLpNorm g 3 μ * mixedNorm (3/2) 1 μ w := by
  apply abs_integral_le_eLpNorm_product μ _ g
    (fun s => (WithLp.toLp 1 (w s) : PiLp 1 (fun _ : ι => ℝ))) hg.1 hw.1
  filter_upwards [hb] with s hs
  simpa only [Real.norm_eq_abs, PiLp.norm_eq_of_L1] using abs_sum_mul_le_mass (b s) (w s) (g s) hs

/-- Norm of the sum of coordinate squares in L(3/2) is the square of the
genuine L3(l2) norm. -/
theorem eLpNorm_sum_squares (v : S → ι → ℝ) :
    eLpNorm (fun s => ∑ i, (v s i)^2) (3/2) μ = mixedNorm 3 2 μ v ^ 2 := by
  let V : S → PiLp 2 (fun _ : ι => ℝ) := fun s => WithLp.toLp 2 (v s)
  have hs : (fun s => ∑ i, (v s i)^2) = (fun s => ‖V s‖ ^ (2 : ℝ)) := by
    funext s
    rw [Real.rpow_two, PiLp.norm_eq_of_L2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp only [V, Real.norm_eq_abs, sq_abs]
  rw [hs, eLpNorm_norm_rpow _ (by norm_num)]
  norm_num [ENNReal.rpow_two]
  congr 2
  exact ENNReal.div_mul_cancel (by norm_num) (by simp)

/-- The diagonal integral is bounded by one scalar L3 norm times the square
of the L3(l2) norm of the transformed child family. -/
theorem block_square_integral_bound (g : S → ℝ) (u v : S → ι → ℝ)
    (hg : MemLp g 3 μ)
    (hv : MemLp (fun s => (WithLp.toLp 2 (v s) : PiLp 2 (fun _ : ι => ℝ))) 3 μ)
    (hu : ∀ᵐ s ∂μ, ∀ i, |u s i| ≤ g s) :
    ENNReal.ofReal |∫ s, ∑ i, u s i * (v s i)^2 ∂μ| ≤
      eLpNorm g 3 μ * mixedNorm 3 2 μ v ^ 2 := by
  have hsq : AEStronglyMeasurable (fun s => ∑ i, (v s i)^2) μ := by
    have hh : (fun s => ∑ i, (v s i)^2) =
        (fun s => ‖(WithLp.toLp 2 (v s) : PiLp 2 (fun _ : ι => ℝ))‖ ^ 2) := by
      funext s
      rw [PiLp.norm_eq_of_L2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      simp only [Real.norm_eq_abs, sq_abs]
    rw [hh]
    exact hv.1.norm.pow 2
  rw [← eLpNorm_sum_squares μ v]
  apply abs_integral_le_eLpNorm_product μ _ g (fun s => ∑ i, (v s i)^2) hg.1 hsq
  filter_upwards [hu] with s hs
  have h := abs_sum_mul_le_mass (u s) (fun i => (v s i)^2) (g s) hs
  simpa only [Real.norm_eq_abs, abs_sq,
    abs_of_nonneg (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (v s i)))] using h

theorem abs_le_of_ofReal_bound {a A : ℝ} (hA : 0 ≤ A)
    (h : ENNReal.ofReal |a| ≤ ENNReal.ofReal A) : |a| ≤ A := by
  exact (ENNReal.ofReal_le_ofReal_iff hA).mp h

/-- A finite real form of the diagonal Hölder estimate. -/
theorem block_square_integral_le (g : S → ℝ) (u v : S → ι → ℝ)
    (hg : MemLp g 3 μ)
    (hv : MemLp (fun s => (WithLp.toLp 2 (v s) : PiLp 2 (fun _ : ι => ℝ))) 3 μ)
    (hu : ∀ᵐ s ∂μ, ∀ i, |u s i| ≤ g s)
    (G M : ℝ) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hgNorm : eLpNorm g 3 μ ≤ ENNReal.ofReal G)
    (hvNorm : mixedNorm 3 2 μ v ≤ ENNReal.ofReal (M * G)) :
    |∫ s, ∑ i, u s i * (v s i)^2 ∂μ| ≤ M^2 * G^3 := by
  apply abs_le_of_ofReal_bound (by positivity)
  calc
    _ ≤ eLpNorm g 3 μ * mixedNorm 3 2 μ v ^ 2 := block_square_integral_bound μ g u v hg hv hu
    _ ≤ ENNReal.ofReal G * ENNReal.ofReal (M * G) ^ 2 :=
      mul_le_mul' hgNorm (pow_le_pow_left' hvNorm 2)
    _ = ENNReal.ofReal (G * (M * G)^2) := by
      rw [ENNReal.ofReal_mul hG, ENNReal.ofReal_pow (mul_nonneg hM hG)]
    _ = _ := by congr 1; ring

/-- A finite real form of the row/product Hölder estimate. -/
theorem block_pair_integral_le (g : S → ℝ) (b w : S → ι → ℝ)
    (hg : MemLp g 3 μ)
    (hw : MemLp (fun s => (WithLp.toLp 1 (w s) : PiLp 1 (fun _ : ι => ℝ))) (3/2) μ)
    (hb : ∀ᵐ s ∂μ, ∀ i, |b s i| ≤ g s)
    (G P : ℝ) (hG : 0 ≤ G) (hP : 0 ≤ P)
    (hgNorm : eLpNorm g 3 μ ≤ ENNReal.ofReal G)
    (hwNorm : mixedNorm (3/2) 1 μ w ≤ ENNReal.ofReal (P * G^2)) :
    |∫ s, ∑ i, b s i * w s i ∂μ| ≤ P * G^3 := by
  apply abs_le_of_ofReal_bound (by positivity)
  calc
    _ ≤ eLpNorm g 3 μ * mixedNorm (3/2) 1 μ w := block_pair_integral_bound μ g b w hg hw hb
    _ ≤ ENNReal.ofReal G * ENNReal.ofReal (P * G^2) := mul_le_mul' hgNorm hwNorm
    _ = ENNReal.ofReal (G * (P * G^2)) := (ENNReal.ofReal_mul hG).symm
    _ = _ := by congr 1; ring

/-- One integrated dyadic level, with the scalar duality and product bounds
explicit. The estimates use genuine mixed norms and yield a universal
coefficient 2M²+2P, independent of the number of parent blocks. -/
theorem block_energy_integral_le (g : S → ℝ) (u v b Ru Rv Rb w W : S → ι → ℝ)
    (hg : MemLp g 3 μ)
    (hRu : MemLp (fun s => (WithLp.toLp 2 (Ru s) : PiLp 2 (fun _ : ι => ℝ))) 3 μ)
    (hRv : MemLp (fun s => (WithLp.toLp 2 (Rv s) : PiLp 2 (fun _ : ι => ℝ))) 3 μ)
    (hW : MemLp (fun s => (WithLp.toLp 1 (W s) : PiLp 1 (fun _ : ι => ℝ))) (3/2) μ)
    (hu : ∀ᵐ s ∂μ, ∀ i, |u s i| ≤ g s)
    (hv : ∀ᵐ s ∂μ, ∀ i, |v s i| ≤ g s)
    (hb : ∀ᵐ s ∂μ, ∀ i, |b s i| ≤ g s)
    (hUI : Integrable (fun s => ∑ i, u s i * (Rv s i)^2) μ)
    (hVI : Integrable (fun s => ∑ i, v s i * (Ru s i)^2) μ)
    (hBI : Integrable (fun s => ∑ i, Rb s i * w s i) μ)
    (hdual : |∫ s, ∑ i, Rb s i * w s i ∂μ| = |∫ s, ∑ i, b s i * W s i ∂μ|)
    (c G M P : ℝ) (hc : |c| ≤ 1) (hG : 0 ≤ G) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (hgNorm : eLpNorm g 3 μ ≤ ENNReal.ofReal G)
    (hRuNorm : mixedNorm 3 2 μ Ru ≤ ENNReal.ofReal (M * G))
    (hRvNorm : mixedNorm 3 2 μ Rv ≤ ENNReal.ofReal (M * G))
    (hWNorm : mixedNorm (3/2) 1 μ W ≤ ENNReal.ofReal (P * G^2)) :
    (∫ s, ∑ i, (u s i * (Rv s i)^2 + v s i * (Ru s i)^2 +
      2 * c * Rb s i * w s i) ∂μ) ≤ (2 * M^2 + 2 * P) * G^3 := by
  have huBound := block_square_integral_le μ g u Rv hg hRv hu G M hG hM hgNorm hRvNorm
  have hvBound := block_square_integral_le μ g v Ru hg hRu hv G M hG hM hgNorm hRuNorm
  have hwBound := block_pair_integral_le μ g b W hg hW hb G P hG hP hgNorm hWNorm
  rw [← hdual] at hwBound
  have hcTerm : 2 * c * (∫ s, ∑ i, Rb s i * w s i ∂μ) ≤ 2 * P * G^3 := by
    calc
      _ ≤ |2 * c * (∫ s, ∑ i, Rb s i * w s i ∂μ)| := le_abs_self _
      _ = 2 * |c| * |∫ s, ∑ i, Rb s i * w s i ∂μ| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * 1 * (P * G^3) := mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num))
        hwBound (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have heq : (fun s => ∑ i, (u s i * (Rv s i)^2 + v s i * (Ru s i)^2 +
      2 * c * Rb s i * w s i)) =
      (fun s => (∑ i, u s i * (Rv s i)^2) + (∑ i, v s i * (Ru s i)^2) +
        (2*c) * (∑ i, Rb s i * w s i)) := by
    funext s
    simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hUV : Integrable (fun s => (∑ i, u s i * (Rv s i)^2) +
      (∑ i, v s i * (Ru s i)^2)) μ := hUI.add hVI
  rw [heq, integral_add hUV (hBI.const_mul (2*c)),
    integral_add hUI hVI, integral_const_mul]
  have hau := le_abs_self (∫ s, ∑ i, u s i * (Rv s i)^2 ∂μ)
  have hav := le_abs_self (∫ s, ∑ i, v s i * (Ru s i)^2 ∂μ)
  nlinarith

/-- Positivity of a partition controls its l2 norm by the scalar total mass. -/
theorem norm_toLp_two_le_mass (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    ‖(WithLp.toLp 2 u : PiLp 2 (fun _ : ι => ℝ))‖ ≤ ∑ i, (u i + v i) := by
  have hsum : (∑ i, u i) ≤ ∑ i, (u i + v i) :=
    Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (hv i)
  apply le_trans _ hsum
  rw [PiLp.norm_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]
  apply (Real.sqrt_le_left (Finset.sum_nonneg fun i _ => hu i)).mpr
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hu i)

theorem mixedNorm_two_le_mass (u v : S → ι → ℝ) (g : S → ℝ)
    (hu : ∀ᵐ s ∂μ, ∀ i, 0 ≤ u s i) (hv : ∀ᵐ s ∂μ, ∀ i, 0 ≤ v s i)
    (hsum : ∀ᵐ s ∂μ, ∑ i, (u s i + v s i) = g s) :
    mixedNorm 3 2 μ u ≤ eLpNorm g 3 μ := by
  apply eLpNorm_mono_ae
  filter_upwards [hu, hv, hsum] with s hu hv hs
  exact (norm_toLp_two_le_mass (u s) (v s) hu hv).trans
    (hs.le.trans (le_abs_self (g s)))

/-- Summing the checked level estimates gives the required linear-in-depth
cubic coefficient. Level estimates remain explicit in this general lemma. -/
theorem tree_cubic_integral_le_of_levels (η : ℝ) (c : ℕ → ℝ)
    (hη : η^2 = 1) (hc : ∀ k, c k ^ 2 = 1) (n : ℕ)
    (f Rf : S → Vec ℝ n) (C G : ℝ)
    (hint : ∀ k ∈ Finset.range n, Integrable (fun s => treeLevelJump η c n k (f s) (Rf s) 0) μ)
    (hlevel : ∀ k ∈ Finset.range n,
      (∫ s, treeLevelJump η c n k (f s) (Rf s) 0 ∂μ) ≤ C * G^3) :
    (∫ s, ∑ i, f s i * (treeMatrix η c n (Rf s) i)^2 ∂μ) ≤ (n : ℝ) * C * G^3 := by
  have heq : (fun s => ∑ i, f s i * (treeMatrix η c n (Rf s) i)^2) =
      (fun s => ∑ k ∈ Finset.range n, treeLevelJump η c n k (f s) (Rf s) 0) := by
    funext s
    exact tree_cubic_energy_eq η c hη hc n (f s) (Rf s)
  rw [heq, integral_finsetSum _ hint]
  calc
    _ ≤ ∑ k ∈ Finset.range n, C * G^3 := Finset.sum_le_sum hlevel
    _ = _ := by simp; ring

end HilbertUMD
