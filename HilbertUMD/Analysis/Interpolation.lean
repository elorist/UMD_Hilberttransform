import HilbertUMD.Analysis.InterpolationMidpoint
import HilbertUMD.Analysis.ComplexL2Norming

/-!
# The Riesz--Thorin estimate required by the cubic lemma

Finite l¹ and l∞ coordinates, endpoints 3/2 and 3, midpoint 2, and one
common endpoint bound. The conclusion concerns the given compatible L²
realization. No general interpolation-space or arbitrary-exponent theorem
is required. The proof works for every measure.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace HilbertUMD

open CubicLp InterpolationMidpoint ComplexL2Norming

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]

private theorem from_simple_ae (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ 0) (hp' : p ≠ ⊤)
    (f : SimpleFunc S (PiLp 1 (fun _ : ι => ℂ))) (hf : f.FinMeasSupp μ) :
    (complexFromL1 (ι := ι)).compLpL p μ (simpleLp μ p hp hp' f hf) =ᵐ[μ]
      fun x => complexFromL1 (f x) := by
  filter_upwards [(complexFromL1 (ι := ι)).coeFn_compLpL (simpleLp μ p hp hp' f hf),
    coeFn_simpleLp μ p hp hp' f hf] with x hx hf
  rw [hx, hf]

private theorem pairing_mixed_simple_eq (μ : Measure S) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderTriple p q 1]
    (hp : p ≠ 0) (hp' : p ≠ ⊤) (hq : q ≠ 0) (hq' : q ≠ ⊤)
    (V : ComplexSpace (ι := ι) μ 2 →L[ℂ] ComplexSpace (ι := ι) μ 2)
    (W : ComplexSpace (ι := ι) μ p →L[ℂ] ComplexSpace (ι := ι) μ p)
    (hVW : ∀ (f : ComplexSpace (ι := ι) μ 2) (g : ComplexSpace (ι := ι) μ p),
      f =ᵐ[μ] g → V f =ᵐ[μ] W g)
    (f g : SimpleFunc S (PiLp 1 (fun _ : ι => ℂ)))
    (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ) :
    pairing μ 2 2 (mixedComplexRealization μ V (atTwo μ f hf)) (atTwo μ g hg) =
      pairing μ p q (mixedComplexRealization μ W (simpleLp μ p hp hp' f hf))
        (simpleLp μ q hq hq' g hg) := by
  have hout := hVW _ _ ((from_simple_ae μ 2 (by norm_num) (by norm_num) f hf).trans
    (from_simple_ae μ p hp hp' f hf).symm)
  change mixedComplexRealization μ V (atTwo μ f hf) =ᵐ[μ]
    mixedComplexRealization μ W (simpleLp μ p hp hp' f hf) at hout
  rw [pairing_apply, pairing_apply]
  apply integral_congr_ae
  filter_upwards [hout, coeFn_simpleLp μ 2 (by norm_num) (by norm_num) g hg,
    coeFn_simpleLp μ q hq hq' g hg] with x hx h2 hq
  rw [hx, h2, hq]

private theorem mixed_bound (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (V : ComplexSpace (ι := ι) μ p →L[ℂ] ComplexSpace (ι := ι) μ p)
    (M : ℝ) (hV : ∀ f, ‖V f‖ ≤ M * complexL1Norm μ p f)
    (f : Lp (PiLp 1 (fun _ : ι => ℂ)) p μ) :
    ‖mixedComplexRealization μ V f‖ ≤ M * ‖f‖ := by
  simpa only [mixedComplexRealization, ContinuousLinearMap.comp_apply, complexL1Norm_fromL1]
    using hV ((complexFromL1 (ι := ι)).compLpL p μ f)

/-- Riesz--Thorin only at the exponents and mixed coordinate norms used in
the paper, with exactly the original endpoint constant. -/
theorem riesz_thorin_l1_linf_two (μ : Measure S)
    (Vhalf : ComplexSpace (ι := ι) μ (3 / 2) →L[ℂ] ComplexSpace (ι := ι) μ (3 / 2))
    (Vtwo : ComplexSpace (ι := ι) μ 2 →L[ℂ] ComplexSpace (ι := ι) μ 2)
    (Vthree : ComplexSpace (ι := ι) μ 3 →L[ℂ] ComplexSpace (ι := ι) μ 3)
    (hTwoHalf : ∀ (f : ComplexSpace (ι := ι) μ 2) (g : ComplexSpace (ι := ι) μ (3 / 2)),
      f =ᵐ[μ] g → Vtwo f =ᵐ[μ] Vhalf g)
    (hTwoThree : ∀ (f : ComplexSpace (ι := ι) μ 2) (g : ComplexSpace (ι := ι) μ 3),
      f =ᵐ[μ] g → Vtwo f =ᵐ[μ] Vthree g)
    (M : ℝ) (hM : 0 ≤ M)
    (hHalf : ∀ f, ‖Vhalf f‖ ≤ M * complexL1Norm μ (3 / 2) f)
    (hThree : ∀ f, ‖Vthree f‖ ≤ M * complexL1Norm μ 3 f)
    (f : ComplexSpace (ι := ι) μ 2) :
    ‖Vtwo f‖ ≤ M * complexL1Norm μ 2 f := by
  let W := mixedComplexRealization μ Vtwo
  let B : Lp (PiLp 1 (fun _ : ι => ℂ)) 2 μ →L[ℂ]
      Lp (PiLp 1 (fun _ : ι => ℂ)) 2 μ →L[ℂ] ℂ :=
    (pairing μ 2 2).comp W
  have h0 (u v : SimpleFunc S (PiLp 1 (fun _ : ι => ℂ)))
      (hu : u.FinMeasSupp μ) (hv : v.FinMeasSupp μ) :
      ‖B (atTwo μ u hu) (atTwo μ v hv)‖ ≤ M * ‖atHalf μ u hu‖ * ‖atThree μ v hv‖ := by
    change ‖pairing μ 2 2 (mixedComplexRealization μ Vtwo (atTwo μ u hu)) (atTwo μ v hv)‖ ≤ _
    rw [pairing_mixed_simple_eq μ (3 / 2) 3 (by norm_num) (by finiteness)
      (by norm_num) (by norm_num) Vtwo Vhalf hTwoHalf u v hu hv]
    exact (pairing_bound μ (3 / 2) 3 _ _).trans
      (mul_le_mul_of_nonneg_right (mixed_bound μ (3 / 2) Vhalf M hHalf _) (norm_nonneg _))
  have h1 (u v : SimpleFunc S (PiLp 1 (fun _ : ι => ℂ)))
      (hu : u.FinMeasSupp μ) (hv : v.FinMeasSupp μ) :
      ‖B (atTwo μ u hu) (atTwo μ v hv)‖ ≤ M * ‖atThree μ u hu‖ * ‖atHalf μ v hv‖ := by
    change ‖pairing μ 2 2 (mixedComplexRealization μ Vtwo (atTwo μ u hu)) (atTwo μ v hv)‖ ≤ _
    rw [pairing_mixed_simple_eq μ 3 (3 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by finiteness) Vtwo Vthree hTwoThree u v hu hv]
    exact (pairing_bound μ 3 (3 / 2) _ _).trans
      (mul_le_mul_of_nonneg_right (mixed_bound μ 3 Vthree M hThree _) (norm_nonneg _))
  have hW (u : Lp (PiLp 1 (fun _ : ι => ℂ)) 2 μ) : ‖W u‖ ≤ M * ‖u‖ := by
    apply norm_le_of_pairing_bound μ (W u) (M * ‖u‖) (mul_nonneg hM (norm_nonneg _))
    intro v
    exact bilinear_midpoint μ B M hM h0 h1 u v
  have hback : (complexFromL1 (ι := ι)).compLpL 2 μ
      ((complexToL1 (ι := ι)).compLpL 2 μ f) = f := by
    apply Lp.ext
    filter_upwards [(complexFromL1 (ι := ι)).coeFn_compLpL
        ((complexToL1 (ι := ι)).compLpL 2 μ f),
      (complexToL1 (ι := ι)).coeFn_compLpL f] with x h1 h2
    rw [h1, h2]
    rfl
  have hh := hW ((complexToL1 (ι := ι)).compLpL 2 μ f)
  change ‖Vtwo ((complexFromL1 (ι := ι)).compLpL 2 μ
      ((complexToL1 (ι := ι)).compLpL 2 μ f))‖ ≤ M * complexL1Norm μ 2 f at hh
  rwa [hback] at hh

end HilbertUMD
