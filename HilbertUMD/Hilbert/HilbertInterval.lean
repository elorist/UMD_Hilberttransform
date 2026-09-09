import HilbertUMD.Hilbert.HilbertConstant
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Principal value of an interval indicator

Direct integration of the reciprocal kernel gives the logarithmic formula.
For an interior point, the logarithms at the two symmetric cutoffs cancel.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace HilbertUMD

private theorem interval_kernel_integrable {a b x : ℝ} (hx : x < a ∨ b < x) :
    IntegrableOn (fun y : ℝ => (x - y)⁻¹) (Ioo a b) volume := by
  have hc : ContinuousOn (fun y : ℝ => (x - y)⁻¹) (Icc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro y hy
    rcases hx with hx | hx <;> simp only [mem_Icc] at hy <;> intro h <;> linarith
  exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self

private theorem integral_interval_kernel {a b x : ℝ} (hab : a ≤ b)
    (hx : x < a ∨ b < x) :
    (∫ y in Ioo a b, (x - y)⁻¹) = Real.log (x - a) - Real.log (x - b) := by
  have hxa : x - a ≠ 0 := by rcases hx with hx | hx <;> intro h <;> linarith
  have hxb : x - b ≠ 0 := by rcases hx with hx | hx <;> intro h <;> linarith
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_left]
  rw [integral_inv, Real.log_div hxa hxb]
  rcases hx with hx | hx
  · exact notMem_uIcc_of_gt (by linarith) (by linarith)
  · exact notMem_uIcc_of_lt (by linarith) (by linarith)

private theorem hilbertTrunc_interval_integral (a b x ε : ℝ) :
    hilbertTrunc ε ((Ico a b).indicator (fun _ : ℝ => (1 : ℝ))) x =
      Real.pi⁻¹ * ∫ y in Ioo a b ∩ {y : ℝ | ε < |x - y|}, (x - y)⁻¹ := by
  unfold hilbertTrunc
  simp only [smul_eq_mul]
  congr 1
  have hi : (fun y : ℝ => (x - y)⁻¹ * (Ico a b).indicator (fun _ => (1 : ℝ)) y) =
      (Ico a b).indicator (fun y => (x - y)⁻¹) := by
    funext y
    by_cases hy : y ∈ Ico a b <;> simp [hy]
  rw [hi, integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico]
  apply setIntegral_congr_set
  filter_upwards [Ioo_ae_eq_Ico (μ := volume) (a := a) (b := b)] with y hy
  change (y ∈ Ioo a b) = (y ∈ Ico a b) at hy
  change (y ∈ Ico a b ∧ ε < |x - y|) = (y ∈ Ioo a b ∧ ε < |x - y|)
  rw [hy]

/-- At every nonendpoint, all sufficiently small symmetric truncations already
equal the logarithmic formula. -/
theorem hilbertTrunc_interval_real {a b x ε : ℝ} (hab : a < b)
    (hε : 0 < ε) (ha : ε < |x - a|) (hb : ε < |x - b|) :
    hilbertTrunc ε ((Ico a b).indicator (fun _ : ℝ => (1 : ℝ))) x =
      Real.log |(x - a) / (x - b)| / Real.pi := by
  have hxa : x - a ≠ 0 := by intro h; simp [h] at ha; linarith
  have hxb : x - b ≠ 0 := by intro h; simp [h] at hb; linarith
  rw [hilbertTrunc_interval_integral, Real.log_abs, Real.log_div hxa hxb, div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  rcases lt_trichotomy x a with hxa' | rfl | hax
  · have hs : Ioo a b ∩ {y : ℝ | ε < |x - y|} = Ioo a b := by
      apply inter_eq_left.mpr
      intro y hy
      simp only [mem_ofPred_eq]
      rw [abs_of_neg (by linarith [hy.1] : x - y < 0)]
      rw [abs_of_neg (by linarith : x - a < 0)] at ha
      linarith [hy.1]
    rw [hs]
    exact integral_interval_kernel hab.le (Or.inl hxa')
  · exact (hxa (sub_self _)).elim
  rcases lt_trichotomy x b with hxb' | rfl | hbx
  · have hae : a < x - ε := by rw [abs_of_pos (sub_pos.mpr hax)] at ha; linarith
    have heb : x + ε < b := by rw [abs_of_neg (sub_neg.mpr hxb')] at hb; linarith
    have hs : Ioo a b ∩ {y : ℝ | ε < |x - y|} =
        Ioo a (x - ε) ∪ Ioo (x + ε) b := by
      ext y
      simp only [mem_inter_iff, mem_Ioo, mem_ofPred_eq, mem_union, lt_abs]
      constructor
      · rintro ⟨hy, h | h⟩
        · exact Or.inl ⟨hy.1, by linarith⟩
        · exact Or.inr ⟨by linarith, hy.2⟩
      · rintro (hy | hy)
        · exact ⟨⟨hy.1, by linarith⟩, Or.inl (by linarith)⟩
        · exact ⟨⟨by linarith, hy.2⟩, Or.inr (by linarith)⟩
    have hd : Disjoint (Ioo a (x - ε)) (Ioo (x + ε) b) := by
      apply Set.disjoint_left.mpr
      intro y hy hz
      linarith [hy.2, hz.1]
    rw [hs, setIntegral_union hd measurableSet_Ioo
      (interval_kernel_integrable (Or.inr (by linarith)))
      (interval_kernel_integrable (Or.inl (by linarith))),
      integral_interval_kernel hae.le (Or.inr (by linarith)),
      integral_interval_kernel heb.le (Or.inl (by linarith))]
    have hleft : x - (x - ε) = ε := by ring
    have hright : x - (x + ε) = -ε := by ring
    rw [hleft, hright, Real.log_neg_eq_log]
    ring
  · exact (hxb (sub_self _)).elim
  · have hs : Ioo a b ∩ {y : ℝ | ε < |x - y|} = Ioo a b := by
      apply inter_eq_left.mpr
      intro y hy
      simp only [mem_ofPred_eq]
      rw [abs_of_pos (by linarith [hy.2] : 0 < x - y)]
      rw [abs_of_pos (sub_pos.mpr hbx)] at hb
      linarith [hy.2]
    rw [hs]
    exact integral_interval_kernel hab.le (Or.inr hbx)

/-- The exact small-truncation formula in either scalar field. -/
theorem hilbertTrunc_interval (𝕜 : Type*) [RCLike 𝕜] {a b x ε : ℝ}
    (hab : a < b) (hε : 0 < ε) (ha : ε < |x - a|) (hb : ε < |x - b|) :
    hilbertTrunc ε ((Ico a b).indicator (fun _ : ℝ => (1 : 𝕜))) x =
      ((Real.log |(x - a) / (x - b)| / Real.pi : ℝ) : 𝕜) := by
  have hf : Integrable ((Ico a b).indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const (by simp))
  have hi : (Ico a b).indicator (fun _ : ℝ => (1 : 𝕜)) =
      fun y => (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜)
        ((Ico a b).indicator (fun _ : ℝ => (1 : ℝ)) y) := by
    funext y
    by_cases hy : y ∈ Ico a b <;> simp [hy, RCLike.ofRealCLM_apply]
  rw [hi, hilbertTrunc_map _ hf hε, hilbertTrunc_interval_real hab hε ha hb]
  rfl

/-- The interval-indicator principal value at each point other than the endpoints. -/
theorem tendsto_hilbertTrunc_interval (𝕜 : Type*) [RCLike 𝕜] {a b x : ℝ}
    (hab : a < b) (ha : x ≠ a) (hb : x ≠ b) :
    Tendsto (fun ε : ℝ => hilbertTrunc ε
      ((Ico a b).indicator (fun _ : ℝ => (1 : 𝕜))) x) (𝓝[>] 0)
      (𝓝 (((Real.log |(x - a) / (x - b)| / Real.pi : ℝ) : 𝕜))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT (abs_pos.mpr (sub_ne_zero.mpr ha)),
    Ioo_mem_nhdsGT (abs_pos.mpr (sub_ne_zero.mpr hb))] with ε hεa hεb
  exact (hilbertTrunc_interval 𝕜 hab hεa.1 hεa.2 hεb.2).symm

/-- The logarithmic Hilbert-transform formula for an interval indicator, a.e.
The two excluded endpoints have Lebesgue measure zero. -/
theorem interval_hilbert_pv (𝕜 : Type*) [RCLike 𝕜] (a b : ℝ) (hab : a < b) :
    IsHilbertPVAe ((Ico a b).indicator (fun _ : ℝ => (1 : 𝕜)))
      (fun t => ((Real.log |(t - a) / (t - b)| / Real.pi : ℝ) : 𝕜)) := by
  filter_upwards [volume.ae_ne a, volume.ae_ne b] with x ha hb
  exact tendsto_hilbertTrunc_interval 𝕜 hab ha hb

end HilbertUMD
