import HilbertUMD.Interfaces.CotlarAnalysis
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
The real-line Hilbert part of the manuscript's scalar-product lemma.
The scalar identity and standard scalar L3/Hilbert-extension theorems are
isolated in `Interfaces/CotlarAnalysis`; all finite-family estimates below are
proved locally, together with the scalar analytic interfaces they use.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace HilbertUMD

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

private instance holder_three_three_three_halves :
    ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2) := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by simp)).mp
  norm_num [ENNReal.toReal_add]⟩

section Families

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S)

/-- The finite-family product difference is controlled without a factor
depending on the number of coordinates. -/
theorem cotlar_difference_mixedNorm_le (u v Hu Hv : S → ι → ℝ)
    (hu : ∀ i, MemLp (fun t => u t i) 3 μ)
    (hv : ∀ i, MemLp (fun t => v t i) 3 μ)
    (hHu : ∀ i, MemLp (fun t => Hu t i) 3 μ)
    (hHv : ∀ i, MemLp (fun t => Hv t i) 3 μ) :
    mixedNorm (3 / 2) 1 μ (fun t i => Hu t i * Hv t i - u t i * v t i) ≤
      mixedNorm 3 2 μ Hu * mixedNorm 3 2 μ Hv +
        mixedNorm 3 2 μ u * mixedNorm 3 2 μ v := by
  have hmulH : MemLp (fun t => (WithLp.toLp 1 (fun i => Hu t i * Hv t i) :
      PiLp 1 (fun _ : ι => ℝ))) (3 / 2) μ :=
    MemLp.of_eval_piLp (fun i => (hHv i).mul (hHu i))
  have hmul : MemLp (fun t => (WithLp.toLp 1 (fun i => u t i * v t i) :
      PiLp 1 (fun _ : ι => ℝ))) (3 / 2) μ :=
    MemLp.of_eval_piLp (fun i => (hv i).mul (hu i))
  have hh := eLpNorm_sub_le hmulH.aestronglyMeasurable hmul.aestronglyMeasurable
    (show (1 : ℝ≥0∞) ≤ 3 / 2 by rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num)
  change mixedNorm (3 / 2) 1 μ (fun t i => Hu t i * Hv t i - u t i * v t i) ≤
    mixedNorm (3 / 2) 1 μ (fun t i => Hu t i * Hv t i) +
      mixedNorm (3 / 2) 1 μ (fun t i => u t i * v t i) at hh
  apply hh.trans
  apply add_le_add
  · apply mixedNorm_mul_le 3 3 (3 / 2) μ
    · exact (MemLp.of_eval_piLp hHu).aestronglyMeasurable
    · exact (MemLp.of_eval_piLp hHv).aestronglyMeasurable
  · apply mixedNorm_mul_le 3 3 (3 / 2) μ
    · exact (MemLp.of_eval_piLp hu).aestronglyMeasurable
    · exact (MemLp.of_eval_piLp hv).aestronglyMeasurable

private theorem cotlar_norm_arithmetic {a b c d M : ℝ≥0∞}
    (hc : c ≤ M * a) (hd : d ≤ M * b) :
    c * d + a * b ≤ (M ^ 2 + 1) * a * b := by
  calc
    c * d + a * b ≤ (M * a) * (M * b) + a * b := add_le_add (mul_le_mul' hc hd) le_rfl
    _ = _ := by ring

theorem cotlar_difference_mixedNorm_le_of_bound (u v Hu Hv : S → ι → ℝ)
    (hu : ∀ i, MemLp (fun t => u t i) 3 μ)
    (hv : ∀ i, MemLp (fun t => v t i) 3 μ)
    (hHu : ∀ i, MemLp (fun t => Hu t i) 3 μ)
    (hHv : ∀ i, MemLp (fun t => Hv t i) 3 μ)
    (M : ℝ≥0∞) (hU : mixedNorm 3 2 μ Hu ≤ M * mixedNorm 3 2 μ u)
    (hV : mixedNorm 3 2 μ Hv ≤ M * mixedNorm 3 2 μ v) :
    mixedNorm (3 / 2) 1 μ (fun t i => Hu t i * Hv t i - u t i * v t i) ≤
      (M ^ 2 + 1) * mixedNorm 3 2 μ u * mixedNorm 3 2 μ v := by
  exact (cotlar_difference_mixedNorm_le μ u v Hu Hv hu hv hHu hHv).trans
    (cotlar_norm_arithmetic hU hV)

end Families

section Hilbert

variable {ι : Type*} [Fintype ι]

/-- A chosen scalar L3 realization of the normalized real-line Hilbert
transform. The scalar interface supplies existence, the bound 6, and PV identification. -/
def realHilbertThree : Lp ℝ 3 (volume : Measure ℝ) →L[ℝ] Lp ℝ 3 (volume : Measure ℝ) :=
  Interfaces.exists_real_hilbert_three.choose

theorem realHilbertThree_nnnorm_le : ‖realHilbertThree‖₊ ≤ 6 :=
  Interfaces.exists_real_hilbert_three.choose_spec.1

theorem realHilbertThree_pv (f : ℝ → ℝ) (hf : MemLp f 3 volume) :
    IsHilbertPVAe f (realHilbertThree (hf.toLp f)) :=
  Interfaces.exists_real_hilbert_three.choose_spec.2 f hf

/-- Every PV representative of Hf agrees a.e. with the selected L3 operator. -/
theorem hilbertPVAe_memLp_three {f Hf : ℝ → ℝ} (hf : MemLp f 3 volume)
    (hHf : IsHilbertPVAe f Hf) : MemLp Hf 3 volume := by
  have heq := (realHilbertThree_pv f hf).unique hHf
  exact MemLp.ae_eq heq (Lp.memLp (realHilbertThree (hf.toLp f)))

theorem hilbertPVAe_mixedNorm_three_le_six (u Hu : ℝ → ι → ℝ)
    (hu : ∀ i, MemLp (fun t => u t i) 3 volume)
    (hHu : ∀ i, IsHilbertPVAe (fun t => u t i) (fun t => Hu t i)) :
    mixedNorm 3 2 volume Hu ≤ 6 * mixedNorm 3 2 volume u := by
  let Ru : ℝ → ι → ℝ := fun t i => realHilbertThree ((hu i).toLp (fun s => u s i)) t
  have heq : Hu =ᵐ[volume] Ru := by
    have hc : ∀ i, (fun t => Hu t i) =ᵐ[volume] (fun t => Ru t i) :=
      fun i => (hHu i).unique (realHilbertThree_pv _ (hu i))
    filter_upwards [ae_all_iff.mpr hc] with t ht
    exact funext ht
  have hn : mixedNorm 3 2 volume Hu = mixedNorm 3 2 volume Ru := by
    apply eLpNorm_congr_ae
    filter_upwards [heq] with t ht
    rw [ht]
  rw [hn]
  exact (Interfaces.scalar_operator_hilbert_extension_three realHilbertThree u hu).trans
    (mul_le_mul' (by exact_mod_cast realHilbertThree_nnnorm_le) le_rfl)

/-- The full finite-family Hilbert scalar-product estimate, with explicit
constant 37. All representatives are the actual nonperiodic PV transforms;
the dimension-independent Cauchy–Schwarz/Hölder estimate is checked above. -/
theorem hilbert_product_mixedNorm_le (u v Hu Hv W : ℝ → ι → ℝ)
    (hu : ∀ i, MemLp (fun t => u t i) 3 volume)
    (hv : ∀ i, MemLp (fun t => v t i) 3 volume)
    (hHu : ∀ i, IsHilbertPVAe (fun t => u t i) (fun t => Hu t i))
    (hHv : ∀ i, IsHilbertPVAe (fun t => v t i) (fun t => Hv t i))
    (hW : ∀ i, IsHilbertPVAe (fun t => u t i * Hv t i + v t i * Hu t i)
      (fun t => W t i)) :
    mixedNorm (3 / 2) 1 volume W ≤
      37 * mixedNorm 3 2 volume u * mixedNorm 3 2 volume v := by
  have heq : W =ᵐ[volume] (fun t i => Hu t i * Hv t i - u t i * v t i) := by
    have hc : ∀ i, (fun t => W t i) =ᵐ[volume]
        (fun t => Hu t i * Hv t i - u t i * v t i) :=
      fun i => (hW i).unique (Interfaces.cotlar_real_pv (hu i) (hv i) (hHu i) (hHv i))
    filter_upwards [ae_all_iff.mpr hc] with t ht
    exact funext ht
  have hn : mixedNorm (3 / 2) 1 volume W =
      mixedNorm (3 / 2) 1 volume (fun t i => Hu t i * Hv t i - u t i * v t i) := by
    apply eLpNorm_congr_ae
    filter_upwards [heq] with t ht
    rw [ht]
  rw [hn]
  have h := cotlar_difference_mixedNorm_le_of_bound volume u v Hu Hv hu hv
    (fun i => hilbertPVAe_memLp_three (hu i) (hHu i))
    (fun i => hilbertPVAe_memLp_three (hv i) (hHv i)) 6
    (hilbertPVAe_mixedNorm_three_le_six u Hu hu hHu)
    (hilbertPVAe_mixedNorm_three_le_six v Hv hv hHv)
  norm_num only [show (6 : ℝ≥0∞) ^ 2 + 1 = 37 by norm_num] at h
  exact h

end Hilbert

end HilbertUMD
