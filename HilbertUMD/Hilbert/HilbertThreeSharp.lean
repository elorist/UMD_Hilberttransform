import HilbertUMD.Hilbert.HilbertLpCompatibility
import HilbertUMD.Analysis.CubicEndpoint
import HilbertUMD.Analysis.ScalarLpOperators

/-! Cotlar's identity gives the scalar cubic energy exactly. The cubic
argument then improves the existing scalar realization to norm at most 11/4. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace HilbertUMD

theorem realHilbertThree_cubic_energy (f : Lp ℝ 3 (volume : Measure ℝ)) :
    (∫ t, f t * (realHilbertThree f t) ^ 2) = (1 / 3 : ℝ) * ∫ t, f t ^ 3 := by
  have hf := Lp.memLp f
  have hh := Lp.memLp (realHilbertThree f)
  have hp : IsHilbertPVAe f (realHilbertThree f) := by
    simpa only [Lp.toLp_coeFn] using realHilbertThree_pv f hf
  have hw : MemLp (fun t => f t * realHilbertThree f t + f t * realHilbertThree f t)
      (3 / 2) volume := (hh.mul hf).add (hh.mul hf)
  have hd := Interfaces.real_hilbert_duality hf hw hp (Interfaces.cotlar_real_pv hf hf hp hp)
  have hi : Integrable (fun t => f t * (realHilbertThree f t) ^ 2) volume := by
    have hs : MemLp (fun t => realHilbertThree f t * realHilbertThree f t) (3 / 2) volume := hh.mul hh
    simpa only [pow_two] using (memLp_one_iff_integrable.mp (hs.mul' hf))
  have hj : Integrable (fun t => f t ^ 3) volume := by
    have hs : MemLp (fun t => f t * f t) (3 / 2) volume := hf.mul hf
    convert memLp_one_iff_integrable.mp (hs.mul hf) using 1
    funext t
    simp only [Pi.mul_apply]
    ring
  have hl : (∫ t, realHilbertThree f t *
      (f t * realHilbertThree f t + f t * realHilbertThree f t)) =
        2 * ∫ t, f t * (realHilbertThree f t) ^ 2 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall (fun t => by ring)
  have hr : (∫ t, f t * (realHilbertThree f t * realHilbertThree f t - f t * f t)) =
      (∫ t, f t * (realHilbertThree f t) ^ 2) - ∫ t, f t ^ 3 := by
    rw [← integral_sub hi hj]
    apply integral_congr_ae
    exact .of_forall (fun t => by ring)
  rw [hl, hr] at hd
  linarith

private theorem singleton_l1Norm (f : CubicLp.Space (ι := Fin 1) (volume : Measure ℝ) 3) :
    CubicLp.l1Norm volume 3 f = ‖(ScalarLp.coordinate (0 : Fin 1)).compLpL 3 volume f‖ := by
  rw [CubicLp.l1Norm_apply, Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [CubicLp.toL1.coeFn_compLpL f,
    (ScalarLp.coordinate (0 : Fin 1)).coeFn_compLpL f] with t hl hc
  rw [hl, hc, CubicLp.norm_toL1]
  simp [ScalarLp.coordinate]

private theorem singleton_energy
    (u : CubicLp.Space (ι := Fin 1) (volume : Measure ℝ) 3)
    (hu : CubicLp.Nonnegative volume u) :
    CubicLp.energy volume (ScalarLp.amplification volume 3 realHilbertThree) u ≤
      (1 / 3 : ℝ) * CubicLp.l1Norm volume 3 u ^ 3 := by
  let f := (ScalarLp.coordinate (0 : Fin 1)).compLpL 3 volume u
  have hc := (ScalarLp.coordinate (0 : Fin 1)).coeFn_compLpL u
  have he : CubicLp.energy volume (ScalarLp.amplification volume 3 realHilbertThree) u =
      ∫ t, f t * (realHilbertThree f t) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hc, ScalarLp.coeFn_amplification volume 3 realHilbertThree u] with t hc ha
    simp only [Fin.sum_univ_one, ha]
    change u t 0 * (realHilbertThree f t) ^ 2 = f t * (realHilbertThree f t) ^ 2
    rw [show f t = u t 0 from hc]
  rw [he, realHilbertThree_cubic_energy, singleton_l1Norm, ← CubicLp.integral_norm_cube volume f]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hi : Integrable (fun t => f t ^ 3) volume := by
    have hs : MemLp (fun t => f t * f t) (3 / 2) volume := (Lp.memLp f).mul (Lp.memLp f)
    convert memLp_one_iff_integrable.mp (hs.mul (Lp.memLp f)) using 1
    funext t
    simp only [Pi.mul_apply]
    ring
  apply integral_mono_ae hi (CubicLp.integrable_norm_cube volume f)
  filter_upwards [hc, hu] with t hc hu
  have hn : 0 ≤ f t := by rw [show f t = u t 0 from hc]; exact hu 0
  rw [Real.norm_of_nonneg hn]

theorem realHilbertThree_norm_le_eleven_quarters (f : Lp ℝ 3 (volume : Measure ℝ)) :
    ‖realHilbertThree f‖ ≤ (11 / 4 : ℝ) * ‖f‖ := by
  let g := (ScalarLp.insertion (0 : Fin 1)).compLpL 3 volume f
  have hb := CubicLp.real_endpoint volume
    (ScalarLp.amplification (ι := Fin 1) volume 3 realHilbertThree)
    (1 / 3) (by norm_num) singleton_energy g
  have hl : CubicLp.l1Norm volume 3 g = ‖f‖ := by
    rw [singleton_l1Norm, ScalarLp.coordinate_insertion]
    simp
  have ho : ‖realHilbertThree f‖ ≤ ‖ScalarLp.amplification (ι := Fin 1) volume 3 realHilbertThree g‖ := by
    have hc : (ScalarLp.coordinate (0 : Fin 1)).compLpL 3 volume
        (ScalarLp.amplification volume 3 realHilbertThree g) = realHilbertThree f := by
      rw [ScalarLp.coordinate_amplification]
      simp [g, ScalarLp.coordinate_insertion]
    rw [← hc]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(ScalarLp.coordinate (0 : Fin 1)).coeFn_compLpL
      (ScalarLp.amplification volume 3 realHilbertThree g)] with t ht
    rw [ht]
    exact norm_le_pi_norm _ 0
  rw [hl] at hb
  have hr : (127 / 80 : ℝ) * Real.sqrt (9 * (1 / 3 : ℝ)) ≤ 11 / 4 := by
    have hs : Real.sqrt (3 : ℝ) ≤ 220 / 127 := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> norm_num
    norm_num only [show (9 : ℝ) * (1 / 3) = 3 by norm_num]
    linarith
  exact ho.trans (hb.trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _)))

theorem realHilbertThree_nnnorm_le_eleven_quarters : ‖realHilbertThree‖₊ ≤ 11 / 4 := by
  apply NNReal.coe_le_coe.mp
  change ‖realHilbertThree‖ ≤ ((11 / 4 : ℝ≥0) : ℝ)
  norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
  exact realHilbertThree.opNorm_le_bound (by norm_num) realHilbertThree_norm_le_eleven_quarters

theorem hilbertPVAe_mixedNorm_three_le_eleven_quarters {ι : Type*} [Fintype ι]
    (u Hu : ℝ → ι → ℝ) (hu : ∀ i, MemLp (fun t => u t i) 3 volume)
    (hHu : ∀ i, IsHilbertPVAe (fun t => u t i) (fun t => Hu t i)) :
    mixedNorm 3 2 volume Hu ≤ (11 / 4) * mixedNorm 3 2 volume u := by
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
  have hC := ENNReal.coe_le_coe.mpr realHilbertThree_nnnorm_le_eleven_quarters
  rw [ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
    ENNReal.coe_ofNat] at hC
  exact (Interfaces.scalar_operator_hilbert_extension_three realHilbertThree u hu).trans
    (mul_le_mul' hC le_rfl)

theorem hilbert_product_mixedNorm_le_nine {ι : Type*} [Fintype ι]
    (u v Hu Hv W : ℝ → ι → ℝ)
    (hu : ∀ i, MemLp (fun t => u t i) 3 volume)
    (hv : ∀ i, MemLp (fun t => v t i) 3 volume)
    (hHu : ∀ i, IsHilbertPVAe (fun t => u t i) (fun t => Hu t i))
    (hHv : ∀ i, IsHilbertPVAe (fun t => v t i) (fun t => Hv t i))
    (hW : ∀ i, IsHilbertPVAe (fun t => u t i * Hv t i + v t i * Hu t i)
      (fun t => W t i)) :
    mixedNorm (3 / 2) 1 volume W ≤
      9 * mixedNorm 3 2 volume u * mixedNorm 3 2 volume v := by
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
    (fun i => hilbertPVAe_memLp_three (hv i) (hHv i)) (11 / 4)
    (hilbertPVAe_mixedNorm_three_le_eleven_quarters u Hu hu hHu)
    (hilbertPVAe_mixedNorm_three_le_eleven_quarters v Hv hv hHv)
  have hc : (11 / 4 : ℝ≥0∞) ^ 2 + 1 ≤ 9 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_pow, ENNReal.toReal_div]
  exact h.trans (mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl)

end HilbertUMD
