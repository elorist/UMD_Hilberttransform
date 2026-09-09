import HilbertUMD.Hilbert.HilbertInterval
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Pointwise existence of smooth Hilbert principal values

Subtract a constant interval indicator centered at the evaluation point.
Its principal value is zero by the proved interval formula. The remaining
kernel is integrable: near the evaluation point it is a divided difference,
and away from that point the reciprocal kernel is bounded.

This argument does not use Fourier analysis or any cited results.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace HilbertUMD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For an absolutely integrable kernel, removing a shrinking interval
converges to the ordinary integral. -/
theorem tendsto_integral_hilbert_cutoff {k : ℝ → E} (hk : Integrable k volume) (x : ℝ) :
    Tendsto (fun ε : ℝ => ∫ y in {y : ℝ | ε < |x - y|}, k y)
      (𝓝[>] 0) (𝓝 (∫ y, k y)) := by
  have hs (ε : ℝ) : MeasurableSet {y : ℝ | ε < |x - y|} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  simp_rw [← integral_indicator (hs _)]
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖k y‖)
  · exact Eventually.of_forall fun ε => hk.aestronglyMeasurable.indicator (hs ε)
  · exact Eventually.of_forall fun ε => Eventually.of_forall fun y => by
      by_cases hy : ε < |x - y| <;> simp [hy]
  · exact hk.norm
  · filter_upwards [volume.ae_ne x] with y hy
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (abs_pos.mpr (sub_ne_zero.mpr hy.symm))] with ε hε
    simp [hε.2]

private theorem hilbertTrunc_sub {f g : ℝ → E} (hf : Integrable f volume)
    (hg : Integrable g volume) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    hilbertTrunc ε (fun y => f y - g y) x =
      hilbertTrunc ε f x - hilbertTrunc ε g x := by
  simp only [hilbertTrunc, smul_sub]
  rw [integral_sub (hilbertTrunc_integrable hf hε x)
    (hilbertTrunc_integrable hg hε x), smul_sub]

/-- Continuity and differentiability at a single point suffice for PV
existence there, provided the input is integrable. -/
theorem exists_hilbertPV_at [CompleteSpace E] {f : ℝ → E} (hf : Continuous f)
    (hi : Integrable f volume) (x : ℝ) (hd : DifferentiableAt ℝ f x) :
    ∃ z : E, Tendsto (fun ε : ℝ => hilbertTrunc ε f x) (𝓝[>] 0) (𝓝 z) := by
  let q : ℝ → ℝ := (Ico (x - 1) (x + 1)).indicator (fun _ => 1)
  let A : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight (f x)
  have hq : Integrable q volume := by
    apply (integrable_indicator_iff measurableSet_Ico).mpr
    exact integrableOn_const (measure_Ico_lt_top.ne)
  have hAq : Integrable (fun y => A (q y)) volume := A.integrable_comp hq
  let r : ℝ → E := fun y => f y - A (q y)
  have hr : Integrable r volume := hi.sub hAq
  have hds : Continuous (dslope f x) := by
    rw [← continuousOn_univ, continuousOn_dslope (univ_mem : univ ∈ 𝓝 x)]
    exact ⟨hf.continuousOn, hd⟩
  have hnear : IntegrableOn (fun y => (x - y)⁻¹ • r y)
      (Icc (x - 1 / 2) (x + 1 / 2)) volume := by
    apply hds.neg.integrableOn_Icc.congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne x),
      ae_restrict_mem measurableSet_Icc] with y hy hymem
    have hyq : y ∈ Ico (x - 1) (x + 1) := by
      constructor <;> linarith [hymem.1, hymem.2]
    simp only [r, A, q, indicator_of_mem hyq, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, one_smul, Pi.neg_apply, dslope_of_ne f hy,
      slope_def_module]
    rw [← neg_sub y x, inv_neg, neg_smul]
  have hfar := hilbertTrunc_integrable hr (show (0 : ℝ) < 1 / 4 by norm_num) x
  have hkernel : Integrable (fun y => (x - y)⁻¹ • r y) volume := by
    have hu : Icc (x - 1 / 2) (x + 1 / 2) ∪ {y : ℝ | 1 / 4 < |x - y|} = univ := by
      apply eq_univ_of_forall
      intro y
      by_cases hy : y ∈ Icc (x - 1 / 2) (x + 1 / 2)
      · exact Or.inl hy
      · right
        simp only [mem_Icc, not_and_or, not_le] at hy
        simp only [mem_ofPred_eq, lt_abs]
        rcases hy with hy | hy
        · left; linarith
        · right; linarith
    have := hnear.union hfar
    rwa [hu, integrableOn_univ] at this
  have hqzero : Tendsto (fun ε : ℝ => hilbertTrunc ε q x) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_hilbertTrunc_interval ℝ (a := x - 1) (b := x + 1) (x := x)
      (by linarith) (by linarith) (by linarith)
    simpa [q] using h
  have hAqzero : Tendsto (fun ε : ℝ => hilbertTrunc ε (fun y => A (q y)) x)
      (𝓝[>] 0) (𝓝 0) := by
    have h := (A.continuous.tendsto 0).comp hqzero
    simp only [map_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hilbertTrunc_map A hq hε x).symm
  refine ⟨Real.pi⁻¹ • ∫ y, (x - y)⁻¹ • r y, ?_⟩
  have hrem : Tendsto (fun ε : ℝ => hilbertTrunc ε r x) (𝓝[>] 0)
      (𝓝 (Real.pi⁻¹ • ∫ y, (x - y)⁻¹ • r y)) :=
    (tendsto_integral_hilbert_cutoff hkernel x).const_smul _
  have h := hrem.add hAqzero
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [r]
  rw [hilbertTrunc_sub hi hAq hε x, sub_add_cancel]

/-- Pointwise PV existence for all of the project's smooth compact tests. -/
theorem exists_isHilbertPV [CompleteSpace E] {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : ∃ g : ℝ → E, IsHilbertPV f g := by
  have h := fun x => exists_hilbertPV_at hf.continuous
    (hf.continuous.integrable_of_hasCompactSupport hc) x
    ((hf.differentiable (by norm_num)).differentiableAt)
  choose g hg using h
  exact ⟨g, hg⟩

/-- An a.e. identification with an `L²` class upgrades to an everywhere PV
representative. Its `MemLp` property follows from a.e. equality. -/
theorem exists_isHilbertPV_toLp_eq [CompleteSpace E] {f : ℝ → E}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (u : Lp E 2 (volume : Measure ℝ)) (hu : IsHilbertPVAe f u) :
    ∃ (g : ℝ → E) (hg : MemLp g 2 volume), IsHilbertPV f g ∧ hg.toLp g = u := by
  obtain ⟨g, hg⟩ := exists_isHilbertPV hf hc
  have heq : g =ᵐ[volume] u := hg.ae.unique hu
  have hgp : MemLp g 2 volume := (Lp.memLp u).ae_eq heq.symm
  exact ⟨g, hgp, hg, Lp.ext (hgp.coeFn_toLp.trans heq)⟩

end HilbertUMD
