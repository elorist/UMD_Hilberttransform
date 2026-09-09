import HilbertUMD.Analysis.MixedNorm
import HilbertUMD.UMD.UMD
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! Generic finite-coordinate amplification of actual scalar Lp operators.
All definitions and proofs are independent of the cited analytic results. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Classical
namespace HilbertUMD.ScalarLp

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]

def coordinate (j : ι) : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j

def insertion (j : ι) : ℝ →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) j

theorem coordinate_insertion (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (j k : ι) (g : Lp ℝ p μ) :
    (coordinate k).compLpL p μ ((insertion j).compLpL p μ g) = if k = j then g else 0 := by
  apply Lp.ext
  filter_upwards [(coordinate k).coeFn_compLpL ((insertion j).compLpL p μ g),
    (insertion j).coeFn_compLpL g, Lp.coeFn_zero ℝ p μ] with x hc hi hz
  rw [hc, hi]
  by_cases h : k = j
  · subst k
    simp [insertion, coordinate]
  · rw [if_neg h]
    have hzero : coordinate k (insertion j (g x)) = 0 := by simp [coordinate, insertion, h]
    rw [hzero]
    exact hz.symm

/-- Coordinatewise action of a scalar bounded operator on a finite vector Lp
space, constructed as a finite sum of projections and insertions. -/
def amplification (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (R : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) : Lp (ι → ℝ) p μ →L[ℝ] Lp (ι → ℝ) p μ :=
  ∑ j : ι, ((insertion j).compLpL p μ).comp (R.comp ((coordinate j).compLpL p μ))

theorem coordinate_amplification (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (R : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (f : Lp (ι → ℝ) p μ) (j : ι) :
    (coordinate j).compLpL p μ (amplification μ p R f) = R ((coordinate j).compLpL p μ f) := by
  classical
  simp only [amplification, sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    coordinate_insertion]
  simp

theorem coeFn_amplification (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (R : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (f : Lp (ι → ℝ) p μ) :
    amplification μ p R f =ᵐ[μ] fun x j => R ((coordinate j).compLpL p μ f) x := by
  have hj (j : ι) : (fun x => amplification μ p R f x j) =ᵐ[μ]
      R ((coordinate j).compLpL p μ f) := by
    have h := (coordinate j).coeFn_compLpL (amplification μ p R f)
    rw [coordinate_amplification] at h
    exact h.symm
  filter_upwards [ae_all_iff.mpr hj] with x hx
  funext j
  exact hx j

theorem coordinate_toLp (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : S → ι → ℝ) (hf : MemLp f p μ) (j : ι) :
    (coordinate j).compLpL p μ (hf.toLp f) =
      ((memLp_pi_iff.mp hf) j).toLp (fun x => f x j) := by
  apply Lp.ext
  filter_upwards [(coordinate j).coeFn_compLpL (hf.toLp f), hf.coeFn_toLp,
    ((memLp_pi_iff.mp hf) j).coeFn_toLp] with x hc hf hj
  rw [hc, hf, hj]
  rfl

/-- Scalar compatibility on an exponent intersection lifts to finite families. -/
theorem compatible (μ : Measure S) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (R : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (T : Lp ℝ q μ →L[ℝ] Lp ℝ q μ)
    (hRT : ∀ (f : S → ℝ) (hp : MemLp f p μ) (hq : MemLp f q μ),
      R (hp.toLp f) =ᵐ[μ] T (hq.toLp f))
    (f : S → ι → ℝ) (hp : MemLp f p μ) (hq : MemLp f q μ) :
    amplification μ p R (hp.toLp f) =ᵐ[μ] amplification μ q T (hq.toLp f) := by
  have hj (j : ι) : R ((coordinate j).compLpL p μ (hp.toLp f)) =ᵐ[μ]
      T ((coordinate j).compLpL q μ (hq.toLp f)) := by
    rw [coordinate_toLp, coordinate_toLp]
    exact hRT _ _ _
  filter_upwards [coeFn_amplification μ p R (hp.toLp f),
    coeFn_amplification μ q T (hq.toLp f), ae_all_iff.mpr hj] with x hr ht hx
  rw [hr, ht]
  funext j
  exact hx j

/-- An adjoint or skew-adjoint scalar pairing lifts to finite coordinate sums.
The exponents can differ, as long as they are Hölder conjugates. -/
theorem integral_pair_amplification (μ : Measure S) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderTriple p q 1]
    (R : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (T : Lp ℝ q μ →L[ℝ] Lp ℝ q μ)
    (σ : ℝ) (hRT : ∀ (f : Lp ℝ p μ) (g : Lp ℝ q μ),
      (∫ x, R f x * g x ∂μ) = σ * ∫ x, f x * T g x ∂μ)
    (f : Lp (ι → ℝ) p μ) (g : Lp (ι → ℝ) q μ) :
    (∫ x, ∑ j, amplification μ p R f x j * g x j ∂μ) =
      σ * ∫ x, ∑ j, f x j * amplification μ q T g x j ∂μ := by
  let F : ι → Lp ℝ p μ := fun j => (coordinate j).compLpL p μ f
  let G : ι → Lp ℝ q μ := fun j => (coordinate j).compLpL q μ g
  have hf (j : ι) : F j =ᵐ[μ] fun x => f x j := (coordinate j).coeFn_compLpL f
  have hg (j : ι) : G j =ᵐ[μ] fun x => g x j := (coordinate j).coeFn_compLpL g
  have hleft : (∫ x, ∑ j, amplification μ p R f x j * g x j ∂μ) =
      ∫ x, ∑ j, R (F j) x * G j x ∂μ := by
    apply integral_congr_ae
    filter_upwards [coeFn_amplification μ p R f, ae_all_iff.mpr hg] with x hr hx
    apply Finset.sum_congr rfl
    intro j _
    rw [hr, ← hx j]
  have hright : (∫ x, ∑ j, f x j * amplification μ q T g x j ∂μ) =
      ∫ x, ∑ j, F j x * T (G j) x ∂μ := by
    apply integral_congr_ae
    filter_upwards [coeFn_amplification μ q T g, ae_all_iff.mpr hf] with x ht hx
    apply Finset.sum_congr rfl
    intro j _
    rw [ht, ← hx j]
  rw [hleft, hright, integral_finsetSum, integral_finsetSum, Finset.mul_sum]
  · exact Finset.sum_congr rfl (fun j _ => hRT (F j) (G j))
  · intro j _
    exact (Lp.memLp (F j)).integrable_mul (Lp.memLp (T (G j)))
  · intro j _
    exact (Lp.memLp (R (F j))).integrable_mul (Lp.memLp (G j))

end HilbertUMD.ScalarLp
