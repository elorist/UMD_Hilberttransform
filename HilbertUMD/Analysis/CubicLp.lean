import HilbertUMD.Analysis.Cubic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual Lp realizations and the positive-testing part of the cubic lemma.
All results here are checked independently of external norming or interpolation.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HilbertUMD.CubicLp

instance factOneLeThree : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
instance factOneLeThreeHalves : Fact (1 ≤ (3 / 2 : ℝ≥0∞)) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mp
  norm_num⟩
instance holderThreeThree : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2) := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by simp)).mp
  norm_num [ENNReal.toReal_add]⟩
instance holderThreeHalvesThree : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) 3 1 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]⟩

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S)

abbrev Space (p : ℝ≥0∞) := Lp (ι → ℝ) p μ

def toL1 : (ι → ℝ) →L[ℝ] PiLp 1 (fun _ : ι => ℝ) :=
  (WithLp.linearEquiv 1 ℝ (ι → ℝ)).symm.toLinearMap.toContinuousLinearMap

def fromL1 : PiLp 1 (fun _ : ι => ℝ) →L[ℝ] (ι → ℝ) :=
  (WithLp.linearEquiv 1 ℝ (ι → ℝ)).toLinearMap.toContinuousLinearMap

def l1Norm (p : ℝ≥0∞) [Fact (1 ≤ p)] : Seminorm ℝ (Space (ι := ι) μ p) :=
  (normSeminorm ℝ (Lp (PiLp 1 (fun _ : ι => ℝ)) p μ)).comp
    ((toL1 (ι := ι)).compLpL p μ).toLinearMap

theorem l1Norm_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    l1Norm μ p f = ‖(toL1 (ι := ι)).compLpL p μ f‖ := rfl

theorem norm_toL1 (x : ι → ℝ) : ‖toL1 x‖ = ∑ i, |x i| :=
  PiLp.norm_eq_of_L1 _

def Nonnegative {p : ℝ≥0∞} (f : Space (ι := ι) μ p) : Prop :=
  ∀ᵐ x ∂μ, ∀ i, 0 ≤ f x i

theorem Nonnegative.add {f g : Space (ι := ι) μ 3}
    (hf : Nonnegative μ f) (hg : Nonnegative μ g) : Nonnegative μ (f + g) := by
  filter_upwards [hf, hg, Lp.coeFn_add f g] with x hf hg hfg
  intro i
  rw [hfg]
  exact add_nonneg (hf i) (hg i)

theorem memLp_abs {p : ℝ≥0∞} (f : Space (ι := ι) μ p) :
    MemLp (fun x i => |f x i|) p μ := by
  apply memLp_pi_iff.mpr
  intro i
  simpa only [Real.norm_eq_abs] using (memLp_pi_iff.mp (Lp.memLp f) i).norm

def absLp {p : ℝ≥0∞} (f : Space (ι := ι) μ p) : Space (ι := ι) μ p :=
  (memLp_abs μ f).toLp (fun x i => |f x i|)

theorem coeFn_absLp {p : ℝ≥0∞} (f : Space (ι := ι) μ p) :
    absLp μ f =ᵐ[μ] (fun x i => |f x i|) := (memLp_abs μ f).coeFn_toLp

theorem nonnegative_absLp {p : ℝ≥0∞} (f : Space (ι := ι) μ p) :
    Nonnegative μ (absLp μ f) := by
  filter_upwards [coeFn_absLp μ f] with x hx
  intro i
  rw [hx]
  exact abs_nonneg _

theorem l1Norm_absLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    l1Norm μ p (absLp μ f) = l1Norm μ p f := by
  rw [l1Norm_apply, l1Norm_apply, Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [(toL1 (ι := ι)).coeFn_compLpL (absLp μ f),
    (toL1 (ι := ι)).coeFn_compLpL f, coeFn_absLp μ f] with x ha hf habs
  rw [ha, hf, habs, norm_toL1, norm_toL1]
  simp only [abs_abs]

theorem memLp_square (f : Space (ι := ι) μ 3) :
    MemLp (fun x i => (f x i) ^ 2) (3 / 2) μ := by
  apply memLp_pi_iff.mpr
  intro i
  have hi := memLp_pi_iff.mp (Lp.memLp f) i
  simp only [pow_two]
  change MemLp ((fun x => f x i) * (fun x => f x i)) (3 / 2) μ
  exact hi.mul hi

def squareLp (f : Space (ι := ι) μ 3) : Space (ι := ι) μ (3 / 2) :=
  (memLp_square μ f).toLp (fun x i => (f x i) ^ 2)

theorem coeFn_squareLp (f : Space (ι := ι) μ 3) :
    squareLp μ f =ᵐ[μ] (fun x i => (f x i) ^ 2) := (memLp_square μ f).coeFn_toLp

theorem norm_vec_square (v : ι → ℝ) : ‖fun i => (v i) ^ 2‖ = ‖v‖ ^ 2 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
  · have hnorm : ‖v‖ ≤ Real.sqrt ‖fun i => (v i) ^ 2‖ := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro i
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt (norm_nonneg _)]
      have hi := norm_le_pi_norm (fun j => (v j) ^ 2) i
      change |v i ^ 2| ≤ ‖fun j => (v j) ^ 2‖ at hi
      rw [abs_of_nonneg (sq_nonneg (v i))] at hi
      simpa only [Real.norm_eq_abs, sq_abs] using hi
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans_eq
      (Real.sq_sqrt (norm_nonneg _))

theorem norm_squareLp (f : Space (ι := ι) μ 3) : ‖squareLp μ f‖ = ‖f‖ ^ 2 := by
  rw [squareLp, Lp.norm_toLp]
  have he : eLpNorm (fun x i => (f x i) ^ 2) (3 / 2) μ = eLpNorm f 3 μ ^ 2 := by
    calc
      _ = eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) (3 / 2) μ := by
        apply eLpNorm_congr_norm_ae
        filter_upwards with x
        rw [norm_vec_square, Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ = _ := by
        rw [eLpNorm_norm_rpow _ (by norm_num)]
        norm_num [ENNReal.rpow_two]
        congr 2
        exact ENNReal.div_mul_cancel (by norm_num) (by simp)
  rw [he, ENNReal.toReal_pow, Lp.norm_def]

theorem norm_le_l1Norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    ‖f‖ ≤ l1Norm μ p f := by
  rw [l1Norm_apply]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(toL1 (ι := ι)).coeFn_compLpL f] with x hx
  rw [hx, norm_toL1]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (f x i)))).mpr
  intro i
  exact Finset.single_le_sum (fun j _ => abs_nonneg (f x j)) (Finset.mem_univ i)

theorem Nonnegative.smul {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : Space (ι := ι) μ p}
    (hf : Nonnegative μ f) {c : ℝ} (hc : 0 ≤ c) : Nonnegative μ (c • f) := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hx hsm
  intro i
  rw [hsm]
  exact mul_nonneg hc (hx i)

def positivePartLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    Space (ι := ι) μ p := (2 : ℝ)⁻¹ • (absLp μ f + f)

theorem coeFn_positivePartLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    positivePartLp μ f =ᵐ[μ] (fun x i => (|f x i| + f x i) / 2) := by
  filter_upwards [Lp.coeFn_smul (2 : ℝ)⁻¹ (absLp μ f + f),
    Lp.coeFn_add (absLp μ f) f, coeFn_absLp μ f] with x hs ha habs
  change ((2 : ℝ)⁻¹ • (absLp μ f + f)) x = _
  rw [hs]
  simp only [Pi.smul_apply]
  rw [ha]
  simp only [Pi.add_apply]
  rw [habs]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem nonnegative_positivePartLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    Nonnegative μ (positivePartLp μ f) := by
  filter_upwards [coeFn_positivePartLp μ f] with x hx
  intro i
  rw [hx]
  have hi := neg_abs_le (f x i)
  linarith

theorem l1Norm_positivePartLp_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    l1Norm μ p (positivePartLp μ f) ≤ l1Norm μ p f := by
  rw [positivePartLp, map_smul_eq_mul]
  have hs := map_add_le_add (l1Norm μ p) (absLp μ f) f
  rw [l1Norm_absLp] at hs
  norm_num
  linarith

theorem positivePartLp_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space (ι := ι) μ p) :
    positivePartLp μ f - positivePartLp μ (-f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (positivePartLp μ f) (positivePartLp μ (-f)),
    coeFn_positivePartLp μ f, coeFn_positivePartLp μ (-f), Lp.coeFn_neg f] with x hs hp hn hneg
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hp, hn, hneg]
  ext i
  simp only [Pi.sub_apply, Pi.neg_apply, abs_neg]
  ring

def energy (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    (f : Space (ι := ι) μ 3) : ℝ := weightedSquareIntegral μ f (V f)

/-- Agreement of the actual L² and L³ representatives on their intersection. -/
structure CompatibleRealOperator where
  atTwo : Space (ι := ι) μ 2 →L[ℝ] Space (ι := ι) μ 2
  atThree : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3
  agree : ∀ (f : Space (ι := ι) μ 2) (g : Space (ι := ι) μ 3),
    f =ᵐ[μ] g → atTwo f =ᵐ[μ] atThree g
  skew : ∀ (f g : Space (ι := ι) μ 2),
    (∫ x, ∑ i, atTwo f x i * g x i ∂μ) =
      -(∫ x, ∑ i, f x i * atTwo g x i ∂μ)

theorem weightedSquare_integrable (f g : Space (ι := ι) μ 3) :
    Integrable (fun x => ∑ i, g x i * (f x i) ^ 2) μ :=
  integrable_weighted_square_of_memLp_three μ
    (memLp_pi_iff.mp (Lp.memLp g)) (memLp_pi_iff.mp (Lp.memLp f))

/-- The restriction from arbitrary real norming tests to nonnegative tests is
proved by coordinatewise absolute values, preserving the exact L³(l¹) norm. -/
theorem abs_pair_square_le (f g : Space (ι := ι) μ 3) :
    |∫ x, ∑ i, squareLp μ f x i * g x i ∂μ| ≤
      weightedSquareIntegral μ (absLp μ g) f := by
  have he : (∫ x, ∑ i, squareLp μ f x i * g x i ∂μ) =
      (∫ x, ∑ i, g x i * (f x i) ^ 2 ∂μ) := by
    apply integral_congr_ae
    filter_upwards [coeFn_squareLp μ f] with x hx
    rw [hx]
    simp only [mul_comm]
  rw [he]
  refine abs_integral_le_integral_abs.trans ?_
  apply integral_mono_ae (weightedSquare_integrable μ f g).abs
    (weightedSquare_integrable μ f (absLp μ g))
  filter_upwards [coeFn_absLp μ g] with x hx
  rw [hx]
  calc
    |∑ i, g x i * (f x i) ^ 2| ≤ ∑ i, |g x i * (f x i) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (sq_nonneg (f x i))]

/-- The pointwise energy argument transferred to genuine L³ equivalence
classes; linearity is used only through its valid a.e. representative identity. -/
theorem mixed_integral_le
    (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    (f g : Space (ι := ι) μ 3) (hf : Nonnegative μ f) (hg : Nonnegative μ g) :
    weightedSquareIntegral μ g (V f) ≤ 2 * energy μ V (f + g) + 2 * energy μ V g := by
  have hv := Lp.coeFn_add (V f) (V g)
  rw [← map_add] at hv
  have hp : ∀ᵐ x ∂μ, (∑ i, g x i * (V f x i) ^ 2) ≤
      2 * (∑ i, (f + g) x i * (V (f + g) x i) ^ 2) +
      2 * (∑ i, g x i * (V g x i) ^ 2) := by
    filter_upwards [hf, hg, Lp.coeFn_add f g, hv] with x hf hg hfg hv
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have he : V f x i = V (f + g) x i - V g x i := by rw [hv]; simp
    rw [he, hfg]
    simpa only [Pi.add_apply, mul_assoc] using
      weighted_square_domination (a := V (f + g) x i) (b := V g x i) (hf i) (hg i)
  have hm := integral_mono_ae (weightedSquare_integrable μ (V f) g)
    (((weightedSquare_integrable μ (V (f + g)) (f + g)).const_mul 2).add
      ((weightedSquare_integrable μ (V g) g).const_mul 2)) hp
  simp only [Pi.add_apply] at hm
  rw [integral_add ((weightedSquare_integrable μ (V (f + g)) (f + g)).const_mul 2)
      ((weightedSquare_integrable μ (V g) g).const_mul 2),
    integral_const_mul, integral_const_mul] at hm
  exact hm

/-- Weighted positive testing on the genuine L³(l¹) domain gives 9B. -/
theorem mixed_integral_le_nine
    (V : Space (ι := ι) μ 3 →L[ℝ] Space (ι := ι) μ 3)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ u, Nonnegative μ u → energy μ V u ≤ B * l1Norm μ 3 u ^ 3)
    (f g : Space (ι := ι) μ 3) (hf : Nonnegative μ f) (hg : Nonnegative μ g)
    (hfp : l1Norm μ 3 f ≤ 1) (hgp : l1Norm μ 3 g ≤ 1) :
    weightedSquareIntegral μ g (V f) ≤ 9 * B := by
  let w := f + (1 / 3 : ℝ) • g
  have hw : Nonnegative μ w := hf.add μ (hg.smul μ (by norm_num))
  have hvw : V w = V f + (1 / 3 : ℝ) • V g := by simp [w]
  have hvc := Lp.coeFn_add (V f) ((1 / 3 : ℝ) • V g)
  rw [← hvw] at hvc
  have hpoint : ∀ᵐ x ∂μ, (∑ i, g x i * (V f x i) ^ 2) ≤
      (27 / 8 : ℝ) * (∑ i, w x i * (V w x i) ^ 2) +
        (∑ i, g x i * (V g x i) ^ 2) := by
    filter_upwards [hf, hg, Lp.coeFn_add f ((1 / 3 : ℝ) • g),
      Lp.coeFn_smul (1 / 3 : ℝ) g, hvc, Lp.coeFn_smul (1 / 3 : ℝ) (V g)]
      with x hf hg hwc hgc hvc hvgc
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hwi : w x i = f x i + g x i / 3 := by
      change (f + (1 / 3 : ℝ) • g) x i = _
      rw [hwc]
      simp only [Pi.add_apply]
      rw [hgc]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hvi : V f x i = V w x i - V g x i / 3 := by
      rw [hvc]
      simp only [Pi.add_apply]
      rw [hvgc]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hvi, hwi]
    simpa only [mul_assoc] using weighted_square_domination_nine
      (a := V w x i) (b := V g x i) (hf i) (hg i)
  have hm := integral_mono_ae (weightedSquare_integrable μ (V f) g)
    (((weightedSquare_integrable μ (V w) w).const_mul (27 / 8 : ℝ)).add
      (weightedSquare_integrable μ (V g) g)) hpoint
  simp only [Pi.add_apply] at hm
  rw [integral_add ((weightedSquare_integrable μ (V w) w).const_mul (27 / 8 : ℝ))
    (weightedSquare_integrable μ (V g) g), integral_const_mul] at hm
  have htest : weightedSquareIntegral μ g (V f) ≤
      (27 / 8 : ℝ) * energy μ V w + energy μ V g := hm
  have hfgp : l1Norm μ 3 w ≤ 4 / 3 := by
    have h := map_add_le_add (l1Norm μ 3) f ((1 / 3 : ℝ) • g)
    rw [map_smul_eq_mul] at h
    norm_num at h
    change l1Norm μ 3 (f + (1 / 3 : ℝ) • g) ≤ _
    linarith
  have hfg3 : l1Norm μ 3 w ^ 3 ≤ (4 / 3 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (apply_nonneg _ _) hfgp 3
  have hg3 : l1Norm μ 3 g ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ (apply_nonneg _ _) hgp 3
  have hefg := (hE w hw).trans (mul_le_mul_of_nonneg_left hfg3 hB)
  have heg := (hE g hg).trans (mul_le_mul_of_nonneg_left hg3 hB)
  nlinarith

end HilbertUMD.CubicLp
