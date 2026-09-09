import HilbertUMD.Hilbert.CotlarFourier
import HilbertUMD.Hilbert.HilbertTwoKernel

/-! Extend the Fourier Cotlar identity by Schwartz density and Hölder
continuity. All principal-value realization assumptions are explicit. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal SchwartzMap

namespace HilbertUMD.CotlarExtension

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 3/2) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num⟩
local instance : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3/2) := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by simp)).mp
  norm_num [ENNReal.toReal_add]⟩

abbrev L3 := Lp ℝ 3 (volume : Measure ℝ)
abbrev L32 := Lp ℝ (3/2) (volume : Measure ℝ)

def product : L3 →L[ℝ] L3 →L[ℝ] L32 :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL volume 3 3 (3/2)

theorem product_ae (u v : L3) :
    product u v =ᵐ[volume] fun x => u x * v x :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder u v

theorem sum_ae (R : L3 →L[ℝ] L3) (u v : L3) :
    product u (R v) + product v (R u) =ᵐ[volume]
      fun x => u x * R v x + v x * R u x := by
  filter_upwards [Lp.coeFn_add (product u (R v)) (product v (R u)),
    product_ae u (R v), product_ae v (R u)] with x hx h1 h2
  exact hx.trans (congrArg₂ (· + ·) h1 h2)

theorem difference_ae (R : L3 →L[ℝ] L3) (u v : L3) :
    product (R u) (R v) - product u v =ᵐ[volume]
      fun x => R u x * R v x - u x * v x := by
  filter_upwards [Lp.coeFn_sub (product (R u) (R v)) (product u v),
    product_ae (R u) (R v), product_ae u v] with x hx h1 h2
  exact hx.trans (congrArg₂ (· - ·) h1 h2)

set_option maxHeartbeats 800000 in
/-- The operator identity extends from real Schwartz functions to all L3. -/
theorem identity_of_schwartz (R : L3 →L[ℝ] L3) (T : L32 →L[ℝ] L32)
    (htest : ∀ (u v : SchwartzMap ℝ ℝ),
      T (product (u.toLp 3) (R (v.toLp 3)) + product (v.toLp 3) (R (u.toLp 3))) =
        product (R (u.toLp 3)) (R (v.toLp 3)) - product (u.toLp 3) (v.toLp 3))
    (u v : L3) :
    T (product u (R v) + product v (R u)) = product (R u) (R v) - product u v := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℝ)
    (μ := (volume : Measure ℝ)) (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)
  apply hd.induction_on₂ (p := fun u v =>
    T (product u (R v) + product v (R u)) = product (R u) (R v) - product u v)
    ?_ htest u v
  apply isClosed_eq
  · exact T.continuous.comp
      ((product.continuous₂.comp (continuous_fst.prodMk (R.continuous.comp continuous_snd))).add
        (product.continuous₂.comp (continuous_snd.prodMk (R.continuous.comp continuous_fst))))
  · exact (product.continuous₂.comp
      ((R.continuous.comp continuous_fst).prodMk (R.continuous.comp continuous_snd))).sub
      product.continuous₂

set_option maxHeartbeats 800000 in
theorem schwartz_identity_of_realizations
    (R : L3 →L[ℝ] L3) (T : L32 →L[ℝ] L32)
    (hR : ∀ (f : ℝ → ℝ) (hf : MemLp f 3 volume), IsHilbertPVAe f (R (hf.toLp f)))
    (hT : ∀ (f : ℝ → ℝ) (hf : MemLp f (3/2) volume), IsHilbertPVAe f (T (hf.toLp f)))
    (h2 : ∀ (f : ℝ → ℝ) (hf : MemLp f 2 volume), IsHilbertPVAe f (realHilbertL2 (hf.toLp f)))
    (u v : SchwartzMap ℝ ℝ) :
    T (product (u.toLp 3) (R (v.toLp 3)) + product (v.toLp 3) (R (u.toLp 3))) =
      product (R (u.toLp 3)) (R (v.toLp 3)) - product (u.toLp 3) (v.toLp 3) := by
  have hu : R (u.toLp 3) =ᵐ[volume] realHilbertL2 (u.toLp 2) :=
    (hR u (u.memLp 3)).unique (h2 u (u.memLp 2))
  have hv : R (v.toLp 3) =ᵐ[volume] realHilbertL2 (v.toLp 2) :=
    (hR v (v.memLp 3)).unique (h2 v (v.memLp 2))
  obtain ⟨W, hW, hHW⟩ := CotlarFourier.real_schwartz u v
  let A := product (u.toLp 3) (R (v.toLp 3)) + product (v.toLp 3) (R (u.toLp 3))
  let D := product (R (u.toLp 3)) (R (v.toLp 3)) - product (u.toLp 3) (v.toLp 3)
  have hAW : A =ᵐ[volume] W := by
    filter_upwards [sum_ae R (u.toLp 3) (v.toLp 3), hW, hu, hv,
      u.coeFn_toLp 3, v.coeFn_toLp 3] with x ha hw hu hv hux hvx
    dsimp only [A]
    rw [ha, hw, hu, hv, hux, hvx]
  have hDH : D =ᵐ[volume] realHilbertL2 W := by
    filter_upwards [difference_ae R (u.toLp 3) (v.toLp 3), hHW, hu, hv,
      u.coeFn_toLp 3, v.coeFn_toLp 3] with x hd hw hu hv hux hvx
    dsimp only [D]
    rw [hd, hw, hu, hv, hux, hvx]
  have hpA : IsHilbertPVAe A (T A) := by
    simpa only [Lp.toLp_coeFn] using hT A (Lp.memLp A)
  have hpW : IsHilbertPVAe W (realHilbertL2 W) := by
    simpa only [Lp.toLp_coeFn] using h2 W (Lp.memLp W)
  exact Lp.ext ((hpA.unique (hpW.congr_input hAW.symm)).trans hDH.symm)

/-- Bounded L3 and L(3/2) PV realizations, compatible with Fourier L2,
satisfy the polarized Cotlar identity for every pair of L3 inputs. -/
theorem cotlar_of_realizations
    (R : L3 →L[ℝ] L3) (T : L32 →L[ℝ] L32)
    (hR : ∀ (f : ℝ → ℝ) (hf : MemLp f 3 volume), IsHilbertPVAe f (R (hf.toLp f)))
    (hT : ∀ (f : ℝ → ℝ) (hf : MemLp f (3/2) volume), IsHilbertPVAe f (T (hf.toLp f)))
    (h2 : ∀ (f : ℝ → ℝ) (hf : MemLp f 2 volume), IsHilbertPVAe f (realHilbertL2 (hf.toLp f)))
    {u v Hu Hv : ℝ → ℝ} (hu : MemLp u 3 volume) (hv : MemLp v 3 volume)
    (hHu : IsHilbertPVAe u Hu) (hHv : IsHilbertPVAe v Hv) :
    IsHilbertPVAe (fun x => u x * Hv x + v x * Hu x)
      (fun x => Hu x * Hv x - u x * v x) := by
  let U := hu.toLp u
  let V := hv.toLp v
  let A := product U (R V) + product V (R U)
  have hRu : R U =ᵐ[volume] Hu := (hR u hu).unique hHu
  have hRv : R V =ᵐ[volume] Hv := (hR v hv).unique hHv
  have hA : A =ᵐ[volume] fun x => u x * Hv x + v x * Hu x := by
    filter_upwards [sum_ae R U V, hu.coeFn_toLp, hv.coeFn_toLp, hRu, hRv]
      with x ha hux hvx hru hrv
    exact ha.trans (by rw [hux, hvx, hru, hrv])
  have hD : T A =ᵐ[volume] fun x => Hu x * Hv x - u x * v x := by
    change T (product U (R V) + product V (R U)) =ᵐ[volume] _
    rw [identity_of_schwartz R T (schwartz_identity_of_realizations R T hR hT h2)]
    filter_upwards [difference_ae R U V, hu.coeFn_toLp, hv.coeFn_toLp, hRu, hRv]
      with x hd hux hvx hru hrv
    exact hd.trans (by rw [hux, hvx, hru, hrv])
  have hp : IsHilbertPVAe A (T A) := by
    simpa only [Lp.toLp_coeFn] using hT A (Lp.memLp A)
  exact (hp.congr_input hA).congr_output hD

end HilbertUMD.CotlarExtension
