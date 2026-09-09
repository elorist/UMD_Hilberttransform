import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-! Actual mixed Lp norms over a measure space and an arbitrary finite
coordinate index. These definitions contain no analytic assumptions. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace HilbertUMD

variable {Ω ι E : Type*} [MeasurableSpace Ω] [Fintype ι] [NormedAddCommGroup E]

/-- Outer exponent p, inner finite-coordinate exponent q, in that order. -/
def mixedNorm (p q : ℝ≥0∞) [Fact (1 ≤ q)] (μ : Measure Ω) (f : Ω → ι → E) : ℝ≥0∞ :=
  eLpNorm (fun s => (WithLp.toLp q (f s) : PiLp q (fun _ : ι => E))) p μ

theorem mixedNorm_eq_eLpNorm_norm (p q : ℝ≥0∞) [Fact (1 ≤ q)]
    (μ : Measure Ω) (f : Ω → ι → E) :
    mixedNorm p q μ f =
      eLpNorm (fun s => ‖(WithLp.toLp q (f s) : PiLp q (fun _ : ι => E))‖) p μ := by
  symm
  exact eLpNorm_norm _

theorem mixedNorm_one (p : ℝ≥0∞) (μ : Measure Ω) (f : Ω → ι → E) :
    mixedNorm p 1 μ f = eLpNorm (fun s => ∑ j, ‖f s j‖) p μ := by
  rw [mixedNorm_eq_eLpNorm_norm]
  simp only [PiLp.norm_eq_of_L1]

theorem mixedNorm_two (p : ℝ≥0∞) (μ : Measure Ω) (f : Ω → ι → E) :
    mixedNorm p 2 μ f = eLpNorm (fun s => Real.sqrt (∑ j, ‖f s j‖ ^ 2)) p μ := by
  rw [mixedNorm_eq_eLpNorm_norm]
  simp only [PiLp.norm_eq_of_L2]

theorem mixedNorm_mono (p q : ℝ≥0∞) [Fact (1 ≤ q)] (μ : Measure Ω)
    (f g : Ω → ι → E)
    (h : ∀ᵐ s ∂μ, ‖(WithLp.toLp q (f s) : PiLp q (fun _ : ι => E))‖ ≤
      ‖(WithLp.toLp q (g s) : PiLp q (fun _ : ι => E))‖) :
    mixedNorm p q μ f ≤ mixedNorm p q μ g := eLpNorm_mono_ae h

theorem mixedNorm_add_le (p q : ℝ≥0∞) [Fact (1 ≤ q)] (μ : Measure Ω)
    (hp : 1 ≤ p) (f g : Ω → ι → E)
    (hf : AEStronglyMeasurable (fun s => (WithLp.toLp q (f s) : PiLp q (fun _ : ι => E))) μ)
    (hg : AEStronglyMeasurable (fun s => (WithLp.toLp q (g s) : PiLp q (fun _ : ι => E))) μ) :
    mixedNorm p q μ (f + g) ≤ mixedNorm p q μ f + mixedNorm p q μ g := by
  let F : Ω → PiLp q (fun _ : ι => E) := fun s => WithLp.toLp q (f s)
  let G : Ω → PiLp q (fun _ : ι => E) := fun s => WithLp.toLp q (g s)
  have h := eLpNorm_add_le (p := p) (f := F) (g := G) hf hg hp
  have heq : F + G = (fun s => (WithLp.toLp q ((f + g) s) : PiLp q (fun _ : ι => E))) := by
    funext s
    exact (WithLp.toLp_add q (f s) (g s)).symm
  rw [heq] at h
  exact h

/-- Finite-coordinate Cauchy-Schwarz, as an l2 times l2 to l1 estimate. -/
theorem norm_toLp_one_mul_le (a b : ι → ℝ) :
    ‖(WithLp.toLp 1 (fun j => a j * b j) : PiLp 1 (fun _ : ι => ℝ))‖ ≤
      ‖(WithLp.toLp 2 a : PiLp 2 (fun _ : ι => ℝ))‖ *
        ‖(WithLp.toLp 2 b : PiLp 2 (fun _ : ι => ℝ))‖ := by
  simpa only [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L2, Real.norm_eq_abs, abs_mul]
    using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => |a j|) (fun j => |b j|)

/-- Hölder in the sample variable combined with Cauchy-Schwarz in the finite
coordinate variable; no dimension-dependent factor occurs. -/
theorem mixedNorm_mul_le (p q r : ℝ≥0∞) [ENNReal.HolderTriple p q r]
    (μ : Measure Ω) (f g : Ω → ι → ℝ)
    (hf : AEStronglyMeasurable (fun s => (WithLp.toLp 2 (f s) : PiLp 2 (fun _ : ι => ℝ))) μ)
    (hg : AEStronglyMeasurable (fun s => (WithLp.toLp 2 (g s) : PiLp 2 (fun _ : ι => ℝ))) μ) :
    mixedNorm r 1 μ (fun s j => f s j * g s j) ≤
      mixedNorm p 2 μ f * mixedNorm q 2 μ g := by
  let b : PiLp 2 (fun _ : ι => ℝ) → PiLp 2 (fun _ : ι => ℝ) → PiLp 1 (fun _ : ι => ℝ) :=
    fun a c => WithLp.toLp 1 (fun j => a j * c j)
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := p) (q := q) (r := r)
    hf hg b 1 (Filter.Eventually.of_forall (fun s => by
      simpa only [NNReal.coe_one, one_mul] using norm_toLp_one_mul_le (f s) (g s)))
  simpa only [mixedNorm, b, ENNReal.coe_one, one_mul] using h

end HilbertUMD
