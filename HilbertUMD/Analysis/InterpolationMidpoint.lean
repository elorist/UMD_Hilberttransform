import Mathlib.Analysis.Complex.Hadamard
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import HilbertUMD.Analysis.CubicLp

/-!
# Bilinear interpolation at the midpoint of 3/2 and 3

Only the equal-bound midpoint estimate used in the cubic lemma is developed.
The analytic families are finite sums of fixed Lp simple functions.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
open scoped Classical

namespace HilbertUMD.InterpolationMidpoint

variable {S E : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The scalar deformation equals one at the midpoint. Using the exponential
also makes the zero-value term an entire function. -/
def weight (r : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.log r : ℂ) * ((1 - 2 * z) / 3))

@[simp] theorem weight_midpoint (r : ℝ) : weight r (1 / 2) = 1 := by
  norm_num [weight]

@[fun_prop] theorem differentiable_weight (r : ℝ) : Differentiable ℂ (weight r) := by
  unfold weight
  fun_prop

theorem norm_weight (r : ℝ) (z : ℂ) :
    ‖weight r z‖ = Real.exp (Real.log r * ((1 - 2 * z.re) / 3)) := by
  simp [weight, Complex.norm_exp, Complex.mul_re, Complex.div_ofNat_re]

theorem norm_weight_smul (v : E) (z : ℂ)
    (hz : 0 ≤ z.re ∧ z.re ≤ 1) :
    ‖weight ‖v‖ z • v‖ = ‖v‖ ^ ((4 - 2 * z.re) / 3) := by
  by_cases hv : v = 0
  · subst v
    simp [Real.zero_rpow (by linarith : (4 - 2 * z.re) / 3 ≠ 0)]
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    rw [norm_smul, norm_weight, ← Real.exp_log hn]
    rw [← Real.exp_add]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring

def atom (f : SimpleFunc S E) (v : E) : SimpleFunc S E :=
  f.map (fun w => if w = v then w else 0)

omit [NormedSpace ℂ E] in
theorem atom_finMeasSupp {μ : Measure S} {f : SimpleFunc S E} (hf : f.FinMeasSupp μ) (v : E) :
    (atom f v).FinMeasSupp μ := hf.map (by simp)

def simpleLp (μ : Measure S) (p : ℝ≥0∞) (hp : p ≠ 0) (hp' : p ≠ ⊤)
    (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) : Lp E p μ :=
  ((SimpleFunc.memLp_iff_finMeasSupp hp hp').mpr hf).toLp f

omit [NormedSpace ℂ E] in
theorem coeFn_simpleLp (μ : Measure S) (p : ℝ≥0∞) (hp : p ≠ 0) (hp' : p ≠ ⊤)
    (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) : simpleLp μ p hp hp' f hf =ᵐ[μ] f :=
  MemLp.coeFn_toLp _

def family (μ : Measure S) (p : ℝ≥0∞) (hp : p ≠ 0) (hp' : p ≠ ⊤)
    (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) (z : ℂ) : Lp E p μ :=
  ∑ v ∈ f.range, weight ‖v‖ z • simpleLp μ p hp hp' (atom f v) (atom_finMeasSupp hf v)

omit [NormedSpace ℂ E] in
theorem coeFn_sum {μ : Measure S} {p : ℝ≥0∞} {κ : Type*}
    (s : Finset κ) (f : κ → Lp E p μ) :
    (∑ i ∈ s, f i : Lp E p μ) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change (0 : Lp E p μ) =ᵐ[μ] fun _ => (0 : E)
    exact Lp.coeFn_zero E p μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hx hs
    change (f i + ∑ j ∈ s, f j) x = _
    rw [hx, Pi.add_apply, hs]

theorem coeFn_family (μ : Measure S) (p : ℝ≥0∞) (hp : p ≠ 0) (hp' : p ≠ ⊤)
    (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) (z : ℂ) :
    family μ p hp hp' f hf z =ᵐ[μ] fun x => weight ‖f x‖ z • f x := by
  classical
  have hs (v : E) :
      (weight ‖v‖ z • simpleLp μ p hp hp' (atom f v) (atom_finMeasSupp hf v) : Lp E p μ)
        =ᵐ[μ] fun x => weight ‖v‖ z • atom f v x := by
    filter_upwards [Lp.coeFn_smul (weight ‖v‖ z)
      (simpleLp μ p hp hp' (atom f v) (atom_finMeasSupp hf v)),
      coeFn_simpleLp μ p hp hp' (atom f v) (atom_finMeasSupp hf v)] with x hx hv
    rw [hx, Pi.smul_apply, hv]
  filter_upwards [coeFn_sum f.range
      (fun v => weight ‖v‖ z • simpleLp μ p hp hp' (atom f v) (atom_finMeasSupp hf v)),
    ae_all_iff.mpr (fun v : f.range => hs v)] with x hx hv
  change (family μ p hp hp' f hf z) x = _ at hx
  rw [hx]
  change (∑ v ∈ f.range, (weight ‖v‖ z • simpleLp μ p hp hp' (atom f v)
    (atom_finMeasSupp hf v)) x) = _
  calc
    _ = ∑ v ∈ f.range, weight ‖v‖ z • atom f v x :=
      Finset.sum_congr rfl (fun v hv' => hv ⟨v, hv'⟩)
    _ = _ := ?_
  rw [Finset.sum_eq_single (f x)]
  · simp [atom]
  · intro v _ hv
    simp [atom, Ne.symm hv]
  · simp

theorem family_midpoint (μ : Measure S) (p : ℝ≥0∞) (hp : p ≠ 0) (hp' : p ≠ ⊤)
    (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) :
    family μ p hp hp' f hf (1 / 2) = simpleLp μ p hp hp' f hf := by
  apply Lp.ext
  filter_upwards [coeFn_family μ p hp hp' f hf (1 / 2),
    coeFn_simpleLp μ p hp hp' f hf] with x h1 h2
  rw [h1, h2, weight_midpoint, one_smul]

theorem differentiable_family (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ 0) (hp' : p ≠ ⊤) (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) :
    Differentiable ℂ (family μ p hp hp' f hf) := by
  unfold family
  fun_prop

def deform (f : SimpleFunc S E) (z : ℂ) : SimpleFunc S E :=
  f.map (fun v => weight ‖v‖ z • v)

theorem deform_finMeasSupp {μ : Measure S} {f : SimpleFunc S E}
    (hf : f.FinMeasSupp μ) (z : ℂ) : (deform f z).FinMeasSupp μ :=
  hf.map (by simp)

theorem family_eq_simpleLp_deform (μ : Measure S) (p : ℝ≥0∞)
    (hp : p ≠ 0) (hp' : p ≠ ⊤) (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) (z : ℂ) :
    family μ p hp hp' f hf z =
      simpleLp μ p hp hp' (deform f z) (deform_finMeasSupp hf z) := by
  apply Lp.ext
  filter_upwards [coeFn_family μ p hp hp' f hf z,
    coeFn_simpleLp μ p hp hp' (deform f z) (deform_finMeasSupp hf z)] with x h1 h2
  exact h1.trans h2.symm

omit [NormedSpace ℂ E] in
theorem norm_simpleLp (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ 0) (hp' : p ≠ ⊤) (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) :
    ‖simpleLp μ p hp hp' f hf‖ = (eLpNorm f p μ).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_simpleLp μ p hp hp' f hf)]

theorem norm_family (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ 0) (hp' : p ≠ ⊤) (f : SimpleFunc S E) (hf : f.FinMeasSupp μ)
    (z : ℂ) (hz : 0 ≤ z.re ∧ z.re ≤ 1) :
    ‖family μ p hp hp' f hf z‖ =
      (eLpNorm f (p * ENNReal.ofReal ((4 - 2 * z.re) / 3)) μ).toReal ^
        ((4 - 2 * z.re) / 3) := by
  have hr : 0 < (4 - 2 * z.re) / 3 := by linarith [hz.2]
  rw [Lp.norm_def]
  have he : eLpNorm (family μ p hp hp' f hf z) p μ =
      eLpNorm (fun x => ‖f x‖ ^ ((4 - 2 * z.re) / 3)) p μ := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [coeFn_family μ p hp hp' f hf z] with x hx
    rw [hx, norm_weight_smul _ _ hz, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [he, eLpNorm_norm_rpow _ hr, ENNReal.toReal_rpow]

theorem norm_family_left (μ : Measure S) (f : SimpleFunc S E) (hf : f.FinMeasSupp μ)
    (z : ℂ) (hz : z.re = 0) :
    ‖family μ (3 / 2) (by norm_num) (by finiteness) f hf z‖ =
      ‖simpleLp μ 2 (by norm_num) (by norm_num) f hf‖ ^ (4 / 3 : ℝ) := by
  rw [norm_family μ _ _ _ f hf z (by rw [hz]; norm_num), norm_simpleLp]
  norm_num [hz, ENNReal.ofReal_div_of_pos]
  have he : (3 / 2 : ℝ≥0∞) * (4 / 3) = 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by norm_num)).mp
    norm_num
  rw [he]

theorem norm_family_right (μ : Measure S) (f : SimpleFunc S E) (hf : f.FinMeasSupp μ)
    (z : ℂ) (hz : z.re = 1) :
    ‖family μ 3 (by norm_num) (by norm_num) f hf z‖ =
      ‖simpleLp μ 2 (by norm_num) (by norm_num) f hf‖ ^ (2 / 3 : ℝ) := by
  rw [norm_family μ _ _ _ f hf z (by rw [hz]; norm_num), norm_simpleLp]
  norm_num [hz, ENNReal.ofReal_div_of_pos]
  have he : (3 : ℝ≥0∞) * (2 / 3) = 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by norm_num)).mp
    norm_num
  rw [he]

theorem norm_weight_le (r : ℝ) (z : ℂ) (hz : 0 ≤ z.re ∧ z.re ≤ 1) :
    ‖weight r z‖ ≤ Real.exp |Real.log r| := by
  rw [norm_weight]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |Real.log r * ((1 - 2 * z.re) / 3)| := le_abs_self _
    _ = |Real.log r| * |(1 - 2 * z.re) / 3| := abs_mul _ _
    _ ≤ |Real.log r| := mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem family_bounded (μ : Measure S) (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      ‖family μ 2 (by norm_num) (by norm_num) f hf z‖ ≤ K := by
  let K := ∑ v ∈ f.range, Real.exp |Real.log ‖v‖| *
    ‖simpleLp μ 2 (by norm_num) (by norm_num) (atom f v) (atom_finMeasSupp hf v)‖
  refine ⟨K, Finset.sum_nonneg (fun _ _ => by positivity), ?_⟩
  intro z hz0 hz1
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (norm_weight_le _ _ ⟨hz0, hz1⟩) (norm_nonneg _)

abbrev atHalf (μ : Measure S) (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) :=
  simpleLp μ (3 / 2) (by norm_num) (by finiteness) f hf

abbrev atTwo (μ : Measure S) (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) :=
  simpleLp μ 2 (by norm_num) (by norm_num) f hf

abbrev atThree (μ : Measure S) (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) :=
  simpleLp μ 3 (by norm_num) (by norm_num) f hf

/-- The only complex-analytic step: midpoint control for two unit simple inputs. -/
theorem bilinear_simple_unit (μ : Measure S)
    (B : Lp E 2 μ →L[ℂ] Lp E 2 μ →L[ℂ] ℂ) (M : ℝ) (hM : 0 ≤ M)
    (h0 : ∀ (f g : SimpleFunc S E) (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ),
      ‖B (atTwo μ f hf) (atTwo μ g hg)‖ ≤ M * ‖atHalf μ f hf‖ * ‖atThree μ g hg‖)
    (h1 : ∀ (f g : SimpleFunc S E) (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ),
      ‖B (atTwo μ f hf) (atTwo μ g hg)‖ ≤ M * ‖atThree μ f hf‖ * ‖atHalf μ g hg‖)
    (f g : SimpleFunc S E) (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ)
    (hfn : ‖atTwo μ f hf‖ = 1) (hgn : ‖atTwo μ g hg‖ = 1) :
    ‖B (atTwo μ f hf) (atTwo μ g hg)‖ ≤ M := by
  let F := family μ 2 (by norm_num) (by norm_num) f hf
  let G := family μ 2 (by norm_num) (by norm_num) g hg
  let A : ℂ → ℂ := fun z => B (F z) (G (1 - z))
  have hAd : Differentiable ℂ A :=
    (B.differentiable.comp (differentiable_family μ 2 _ _ f hf)).clm_apply
      ((differentiable_family μ 2 _ _ g hg).comp ((differentiable_const (1 : ℂ)).sub differentiable_id))
  obtain ⟨Kf, hKf, hF⟩ := family_bounded μ f hf
  obtain ⟨Kg, hKg, hG⟩ := family_bounded μ g hg
  have hAb : BddAbove ((norm ∘ A) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨‖B‖ * Kf * Kg, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact B.le_of_opNorm₂_le_of_le le_rfl (hF z hz.1 hz.2)
      (hG (1 - z) (by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.2])
        (by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.1]))
  have hA0 (z : ℂ) (hz : z.re = 0) : ‖A z‖ ≤ M := by
    have hh := h0 (deform f z) (deform g (1 - z))
      (deform_finMeasSupp hf z) (deform_finMeasSupp hg (1 - z))
    simp only [atTwo, atHalf, atThree] at hh
    rw [← family_eq_simpleLp_deform μ 2 _ _ f hf z,
      ← family_eq_simpleLp_deform μ 2 _ _ g hg (1 - z),
      ← family_eq_simpleLp_deform μ (3 / 2) _ _ f hf z,
      ← family_eq_simpleLp_deform μ 3 _ _ g hg (1 - z)] at hh
    rw [norm_family_left μ f hf z hz,
      norm_family_right μ g hg (1 - z) (by simp [hz]), hfn, hgn] at hh
    simpa only [Real.one_rpow, mul_one] using hh
  have hA1 (z : ℂ) (hz : z.re = 1) : ‖A z‖ ≤ M := by
    have hh := h1 (deform f z) (deform g (1 - z))
      (deform_finMeasSupp hf z) (deform_finMeasSupp hg (1 - z))
    simp only [atTwo, atHalf, atThree] at hh
    rw [← family_eq_simpleLp_deform μ 2 _ _ f hf z,
      ← family_eq_simpleLp_deform μ 2 _ _ g hg (1 - z),
      ← family_eq_simpleLp_deform μ 3 _ _ f hf z,
      ← family_eq_simpleLp_deform μ (3 / 2) _ _ g hg (1 - z)] at hh
    rw [norm_family_right μ f hf z hz,
      norm_family_left μ g hg (1 - z) (by simp [hz]), hfn, hgn] at hh
    simpa only [Real.one_rpow, mul_one] using hh
  have hh := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' A
    (z := (1 / 2 : ℂ)) (a := M) (b := M) (by norm_num [Complex.HadamardThreeLines.verticalClosedStrip])
    hAd.diffContOnCl hAb (fun z hz => hA0 z hz) (fun z hz => hA1 z hz)
  have hpow : M ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) = M := by
    rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hM]
  norm_num only [Complex.div_ofNat_re, Complex.one_re, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hh
  rw [hpow] at hh
  simpa only [A, F, G, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, family_midpoint] using hh

theorem simpleLp_map_smul (μ : Measure S) (p : ℝ≥0∞) (hp : p ≠ 0) (hp' : p ≠ ⊤)
    (f : SimpleFunc S E) (hf : f.FinMeasSupp μ) (c : ℂ) :
    simpleLp μ p hp hp' (f.map (fun v => c • v)) (hf.map (by simp)) =
      c • simpleLp μ p hp hp' f hf := by
  apply Lp.ext
  filter_upwards [coeFn_simpleLp μ p hp hp' (f.map (fun v => c • v)) (hf.map (by simp)),
    coeFn_simpleLp μ p hp hp' f hf, Lp.coeFn_smul c (simpleLp μ p hp hp' f hf)] with x hm hf hs
  rw [hm, hs, Pi.smul_apply, hf]
  rfl

theorem bilinear_simple (μ : Measure S)
    (B : Lp E 2 μ →L[ℂ] Lp E 2 μ →L[ℂ] ℂ) (M : ℝ) (hM : 0 ≤ M)
    (h0 : ∀ (f g : SimpleFunc S E) (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ),
      ‖B (atTwo μ f hf) (atTwo μ g hg)‖ ≤ M * ‖atHalf μ f hf‖ * ‖atThree μ g hg‖)
    (h1 : ∀ (f g : SimpleFunc S E) (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ),
      ‖B (atTwo μ f hf) (atTwo μ g hg)‖ ≤ M * ‖atThree μ f hf‖ * ‖atHalf μ g hg‖)
    (f g : SimpleFunc S E) (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ) :
    ‖B (atTwo μ f hf) (atTwo μ g hg)‖ ≤ M * ‖atTwo μ f hf‖ * ‖atTwo μ g hg‖ := by
  by_cases hf0 : atTwo μ f hf = 0
  · simp [hf0]
  by_cases hg0 : atTwo μ g hg = 0
  · simp [hg0]
  let c : ℂ := (‖atTwo μ f hf‖ : ℂ)⁻¹
  let d : ℂ := (‖atTwo μ g hg‖ : ℂ)⁻¹
  have hc : ‖c‖ = ‖atTwo μ f hf‖⁻¹ := by simp [c]
  have hd : ‖d‖ = ‖atTwo μ g hg‖⁻¹ := by simp [d]
  have hfmap : atTwo μ (f.map (fun v => c • v)) (hf.map (by simp)) = c • atTwo μ f hf :=
    simpleLp_map_smul μ 2 _ _ f hf c
  have hgmap : atTwo μ (g.map (fun v => d • v)) (hg.map (by simp)) = d • atTwo μ g hg :=
    simpleLp_map_smul μ 2 _ _ g hg d
  have hfn : ‖atTwo μ (f.map (fun v => c • v)) (hf.map (by simp))‖ = 1 := by
    rw [hfmap, norm_smul, hc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hf0)]
  have hgn : ‖atTwo μ (g.map (fun v => d • v)) (hg.map (by simp))‖ = 1 := by
    rw [hgmap, norm_smul, hd, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg0)]
  have hu := bilinear_simple_unit μ B M hM h0 h1
    (f.map (fun v => c • v)) (g.map (fun v => d • v))
    (hf.map (by simp)) (hg.map (by simp)) hfn hgn
  rw [hfmap, hgmap] at hu
  simp only [map_smul, smul_apply, norm_smul, hc, hd] at hu
  have hp : 0 < ‖atTwo μ f hf‖ := norm_pos_iff.mpr hf0
  have hq : 0 < ‖atTwo μ g hg‖ := norm_pos_iff.mpr hg0
  calc
    _ = ‖atTwo μ f hf‖ * (‖atTwo μ g hg‖ *
        (‖atTwo μ f hf‖⁻¹ * (‖atTwo μ g hg‖⁻¹ *
          ‖B (atTwo μ f hf) (atTwo μ g hg)‖))) := by field_simp
    _ ≤ ‖atTwo μ f hf‖ * (‖atTwo μ g hg‖ * M) := by
      gcongr
      simpa only [mul_left_comm] using hu
    _ = _ := by ring

/-- Equal endpoint bounds at (3/2,3) and (3,3/2) give the same bilinear L²
bound. Simple-function density identifies the result with the given map. -/
theorem bilinear_midpoint (μ : Measure S)
    (B : Lp E 2 μ →L[ℂ] Lp E 2 μ →L[ℂ] ℂ) (M : ℝ) (hM : 0 ≤ M)
    (h0 : ∀ (f g : SimpleFunc S E) (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ),
      ‖B (atTwo μ f hf) (atTwo μ g hg)‖ ≤ M * ‖atHalf μ f hf‖ * ‖atThree μ g hg‖)
    (h1 : ∀ (f g : SimpleFunc S E) (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ),
      ‖B (atTwo μ f hf) (atTwo μ g hg)‖ ≤ M * ‖atThree μ f hf‖ * ‖atHalf μ g hg‖)
    (f g : Lp E 2 μ) : ‖B f g‖ ≤ M * ‖f‖ * ‖g‖ := by
  refine (Lp.simpleFunc.denseRange (E := E) (p := 2) (μ := μ) (by norm_num)).induction_on
    (p := fun f => ‖B f g‖ ≤ M * ‖f‖ * ‖g‖) f ?_ ?_
  · exact isClosed_le ((B.flip g).continuous.norm) ((continuous_const.mul continuous_norm).mul continuous_const)
  · intro sf
    refine (Lp.simpleFunc.denseRange (E := E) (p := 2) (μ := μ) (by norm_num)).induction_on
      (p := fun g => ‖B sf g‖ ≤ M * ‖(sf : Lp E 2 μ)‖ * ‖g‖) g ?_ ?_
    · exact isClosed_le (B sf).continuous.norm (continuous_const.mul continuous_norm)
    · intro sg
      have hf := (SimpleFunc.memLp_iff_finMeasSupp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp (Lp.simpleFunc.memLp sf)
      have hg := (SimpleFunc.memLp_iff_finMeasSupp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp (Lp.simpleFunc.memLp sg)
      have he (s : Lp.simpleFunc E 2 μ) (hs : (Lp.simpleFunc.toSimpleFunc s).FinMeasSupp μ) :
          atTwo μ (Lp.simpleFunc.toSimpleFunc s) hs = (s : Lp E 2 μ) := by
        apply Lp.ext
        exact (coeFn_simpleLp μ 2 _ _ _ hs).trans (Lp.simpleFunc.toSimpleFunc_eq_toFun s)
      simpa only [he sf hf, he sg hg] using
        bilinear_simple μ B M hM h0 h1 (Lp.simpleFunc.toSimpleFunc sf)
          (Lp.simpleFunc.toSimpleFunc sg) hf hg

end HilbertUMD.InterpolationMidpoint
