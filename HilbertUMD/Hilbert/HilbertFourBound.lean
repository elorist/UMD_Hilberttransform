import HilbertUMD.Hilbert.CotlarFourier
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# An independent scalar L4 estimate

The Fourier Cotlar identity and the L2 isometry imply the L4 bound on
Schwartz functions. This module uses no principal-value extension or
scalar L(3/2) realization.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal

namespace HilbertUMD.HilbertFourBound

private instance : ENNReal.HolderTriple 4 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by simp)).mp
  norm_num [ENNReal.toReal_add]⟩

theorem eLpNorm_square (f : ℝ → ℂ) :
    eLpNorm (fun x => f x * f x) 2 volume = (eLpNorm f 4 volume) ^ 2 := by
  calc
    _ = eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) 2 volume := by
      apply eLpNorm_congr_norm_ae
      filter_upwards with x
      simp [norm_mul, pow_two]
    _ = _ := by
      rw [eLpNorm_norm_rpow _ (by norm_num)]
      norm_num [ENNReal.rpow_two]

theorem memLp_four_of_square {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hff : MemLp (fun x => f x * f x) 2 volume) : MemLp f 4 volume := by
  refine ⟨hf, ?_⟩
  have h := hff.2
  rw [eLpNorm_square] at h
  simpa only [ENNReal.pow_lt_top_iff, show (2 : ℕ) ≠ 0 by norm_num, or_false] using h

/-- Cotlar's identity supplies L4 membership before any L4 norm is used. -/
theorem hilbert_schwartz_memLp_four (u : SchwartzMap ℝ ℂ) :
    MemLp (fun x => hilbertL2 (u.toLp 2) x) 4 volume := by
  obtain ⟨W, _, hHW⟩ := CotlarFourier.complex_schwartz u u
  have hu : MemLp (fun x => u x * u x) 2 volume := (u.memLp 4).mul' (u.memLp 4)
  apply memLp_four_of_square (Lp.memLp _).1
  apply ((Lp.memLp (hilbertL2 W)).add hu).ae_eq
  filter_upwards [hHW] with x hx
  simp only [Pi.add_apply]
  rw [hx]
  ring

private theorem le_five_halves_of_square {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞)
    (h : a ^ 2 ≤ 2 * (b * a) + b ^ 2) : a ≤ (5 / 2) * b := by
  have hs : a.toReal ^ 2 ≤ 2 * (b.toReal * a.toReal) + b.toReal ^ 2 := by
    have ht := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top hb ha), ENNReal.pow_ne_top hb⟩) h
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top hb ha)) (ENNReal.pow_ne_top hb)] at ht
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using ht
  apply (ENNReal.toReal_le_toReal ha (ENNReal.mul_ne_top (by finiteness) hb)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  by_contra hn
  have hn' : (5 / 2) * b.toReal < a.toReal := lt_of_not_ge hn
  have hb0 := ENNReal.toReal_nonneg (a := b)
  have hp : 0 < (a.toReal - (5 / 2) * b.toReal) * (a.toReal + b.toReal / 2) :=
    mul_pos (by linarith) (by linarith)
  nlinarith [sq_nonneg b.toReal]

/-- The normalized complex Fourier Hilbert transform has L4 bound 5/2 on Schwartz inputs. -/
theorem hilbert_schwartz_eLpNorm_four_le (u : SchwartzMap ℝ ℂ) :
    eLpNorm (fun x => hilbertL2 (u.toLp 2) x) 4 volume ≤ (5 / 2) * eLpNorm u 4 volume := by
  let h : ℝ → ℂ := hilbertL2 (u.toLp 2)
  have hh : MemLp h 4 volume := hilbert_schwartz_memLp_four u
  have hu : MemLp u 4 volume := u.memLp 4
  have hprod : MemLp (fun x => u x * h x) 2 volume := hh.mul' hu
  have huu : MemLp (fun x => u x * u x) 2 volume := hu.mul' hu
  obtain ⟨W, hW, hHW⟩ := CotlarFourier.complex_schwartz u u
  have hWnorm : eLpNorm (fun x => W x) 2 volume ≤
      2 * (eLpNorm u 4 volume * eLpNorm h 4 volume) := by
    rw [eLpNorm_congr_ae hW]
    change eLpNorm ((fun x => u x * h x) + (fun x => u x * h x)) 2 volume ≤ _
    calc
      _ ≤ eLpNorm (fun x => u x * h x) 2 volume +
          eLpNorm (fun x => u x * h x) 2 volume :=
        eLpNorm_add_le hprod.1 hprod.1 (by norm_num)
      _ ≤ _ := by
        have hp : eLpNorm (fun x => u x * h x) 2 volume ≤
            eLpNorm u 4 volume * eLpNorm h 4 volume :=
          by
            simpa only [ENNReal.coe_one, one_mul] using
              (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 4) (q := 4) (r := 2)
                hu.1 hh.1 (fun a b : ℂ => a * b) 1
                (Eventually.of_forall fun x => by simp only [norm_mul, NNReal.coe_one, one_mul]; rfl))
        simpa only [two_mul] using add_le_add hp hp
  have hsquare : (eLpNorm h 4 volume) ^ 2 ≤
      2 * (eLpNorm u 4 volume * eLpNorm h 4 volume) + (eLpNorm u 4 volume) ^ 2 := by
    rw [← eLpNorm_square]
    have he : (fun x => h x * h x) =ᵐ[volume]
        (fun x => hilbertL2 W x) + (fun x => u x * u x) := by
      filter_upwards [hHW] with x hx
      change h x * h x = hilbertL2 W x + u x * u x
      rw [hx]
      ring
    rw [eLpNorm_congr_ae he]
    calc
      _ ≤ eLpNorm (fun x => hilbertL2 W x) 2 volume +
          eLpNorm (fun x => u x * u x) 2 volume :=
        eLpNorm_add_le (Lp.memLp _).1 huu.1 (by norm_num)
      _ = eLpNorm (fun x => W x) 2 volume + (eLpNorm u 4 volume) ^ 2 := by
        rw [eLpNorm_square, ← Lp.enorm_def, ← Lp.enorm_def, hilbertL2.enorm_map]
      _ ≤ _ := add_le_add hWnorm le_rfl
  exact le_five_halves_of_square hh.eLpNorm_ne_top hu.eLpNorm_ne_top hsquare

private theorem real_schwartz_ae (u : SchwartzMap ℝ ℝ) :
    hilbertL2 ((u.postcompCLM Complex.ofRealCLM).toLp 2) =ᵐ[volume]
      fun x => (realHilbertL2 (u.toLp 2) x : ℂ) := by
  rw [CotlarFourier.ofReal_schwartz_toLp, ← ofReal_realHilbertL2]
  exact l2OfReal_coeFn _

/-- The same L4 membership for the real Fourier realization. -/
theorem realHilbert_schwartz_memLp_four (u : SchwartzMap ℝ ℝ) :
    MemLp (fun x => realHilbertL2 (u.toLp 2) x) 4 volume := by
  apply (hilbert_schwartz_memLp_four (u.postcompCLM Complex.ofRealCLM)).congr_norm
    (Lp.memLp _).1
  filter_upwards [real_schwartz_ae u] with x hx
  rw [hx, Complex.norm_real]

/-- The real L4 estimate has no dependency on an L(3/2) operator or on a.e. PV existence. -/
theorem realHilbert_schwartz_eLpNorm_four_le (u : SchwartzMap ℝ ℝ) :
    eLpNorm (fun x => realHilbertL2 (u.toLp 2) x) 4 volume ≤
      (5 / 2) * eLpNorm u 4 volume := by
  have hout : eLpNorm (fun x => hilbertL2 ((u.postcompCLM Complex.ofRealCLM).toLp 2) x)
      4 volume = eLpNorm (fun x => realHilbertL2 (u.toLp 2) x) 4 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [real_schwartz_ae u] with x hx
    rw [hx, Complex.norm_real]
  have hin : eLpNorm (u.postcompCLM Complex.ofRealCLM) 4 volume = eLpNorm u 4 volume := by
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall fun x => by simp
  simpa only [hout, hin] using hilbert_schwartz_eLpNorm_four_le (u.postcompCLM Complex.ofRealCLM)

local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier action on Schwartz functions, with its values regarded in L4. -/
def realSchwartzMap : SchwartzMap ℝ ℝ →ₗ[ℝ] Lp ℝ 4 (volume : Measure ℝ) where
  toFun u := (realHilbert_schwartz_memLp_four u).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    have he : realHilbertL2 ((u + v).toLp 2) =
        realHilbertL2 (u.toLp 2) + realHilbertL2 (v.toLp 2) := by
      change realHilbertL2 ((SchwartzMap.toLpCLM ℝ ℝ 2 volume) (u + v)) = _
      simp only [map_add, SchwartzMap.toLpCLM_apply]
    rw [he]
    exact Lp.coeFn_add _ _
  map_smul' c u := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    have he : realHilbertL2 ((c • u).toLp 2) = c • realHilbertL2 (u.toLp 2) := by
      change realHilbertL2 ((SchwartzMap.toLpCLM ℝ ℝ 2 volume) (c • u)) = _
      simp only [map_smul, SchwartzMap.toLpCLM_apply]
    rw [he]
    exact Lp.coeFn_smul c _

private theorem toReal_le_five_halves_mul {a b : ℝ≥0∞} (hb : b ≠ ∞)
    (h : a ≤ (5 / 2) * b) : a.toReal ≤ (5 / 2 : ℝ) * b.toReal := by
  have hn := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (show (5 / 2 : ℝ≥0∞) ≠ ∞ by finiteness) hb) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat] using hn

theorem realSchwartzMap_norm_le (u : SchwartzMap ℝ ℝ) :
    ‖realSchwartzMap u‖ ≤ (5 / 2 : ℝ) * ‖u.toLp 4‖ := by
  change ‖(realHilbert_schwartz_memLp_four u).toLp _‖ ≤ _
  rw [Lp.norm_toLp, SchwartzMap.norm_toLp]
  apply toReal_le_five_halves_mul
  · exact (u.memLp 4 volume).eLpNorm_ne_top
  · exact realHilbert_schwartz_eLpNorm_four_le u

/-- An independently constructed real L4 Hilbert operator. -/
def realHilbertFour : Lp ℝ 4 (volume : Measure ℝ) →L[ℝ] Lp ℝ 4 (volume : Measure ℝ) :=
  realSchwartzMap.extendOfNorm (SchwartzMap.toLpCLM ℝ ℝ 4 volume).toLinearMap

theorem realHilbertFour_norm_le : ‖realHilbertFour‖ ≤ (5 / 2 : ℝ) :=
  LinearMap.opNorm_extendOfNorm_le (SchwartzMap.denseRange_toLpCLM (p := 4) (by norm_num))
    (by norm_num) realSchwartzMap_norm_le

/-- The extension retains the actual Fourier values on every Schwartz input. -/
theorem realHilbertFour_schwartz (u : SchwartzMap ℝ ℝ) :
    realHilbertFour (u.toLp 4) =ᵐ[volume] realHilbertL2 (u.toLp 2) := by
  have he : realHilbertFour (u.toLp 4) = realSchwartzMap u :=
    LinearMap.extendOfNorm_eq (SchwartzMap.denseRange_toLpCLM (p := 4) (by norm_num))
      ⟨5 / 2, realSchwartzMap_norm_le⟩ u
  rw [he]
  exact (realHilbert_schwartz_memLp_four u).coeFn_toLp

/-- On Schwartz inputs, the independent L4 extension agrees with the principal value. -/
theorem realHilbertFour_schwartz_pv (u : SchwartzMap ℝ ℝ) :
    IsHilbertPVAe u (realHilbertFour (u.toLp 4)) := by
  let v := u.postcompCLM Complex.ofRealCLM
  have hp : IsHilbertPVAe v (hilbertL2 (v.toLp 2)) :=
    scalar_pv_fourier_ae (v.smooth 1) v.integrable (v.memLp 2)
  have hr := hp.map v.integrable Complex.reCLM
  filter_upwards [hr, real_schwartz_ae u, realHilbertFour_schwartz u] with x hx hC hR
  have hCr : (hilbertL2 (v.toLp 2) x).re = realHilbertL2 (u.toLp 2) x := by
    rw [hC, Complex.ofReal_re]
  simpa only [v, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
    Complex.reCLM_apply, Complex.ofReal_re, hCr, hR] using hx

end HilbertUMD.HilbertFourBound
