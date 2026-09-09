import HilbertUMD.Hilbert.HilbertTwoFromThreeHalves
import HilbertUMD.Interfaces.HilbertThreeHalves

/-! Extension of a smooth-test Hilbert bound to finite-dimensional L2 inputs.
The scalar PV input is the existing L(3/2) realization. All coordinate and
density arguments preserve the originally supplied operator bound. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace HilbertUMD.HilbertL2Extension

theorem scalar_pv (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    IsHilbertPVAe f (realHilbertL2 (hf.toLp f)) := by
  obtain ⟨R, _, hR⟩ := Interfaces.exists_real_hilbert_three_halves
  exact HilbertTwoFromThreeHalves.pv_all R hR f hf

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]

def coord (i : Fin (Module.finrank ℝ F)) : F →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (Module.finBasis ℝ F).equivFunL.toContinuousLinearMap

def insert (i : Fin (Module.finrank ℝ F)) : ℝ →L[ℝ] F :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (Module.finBasis ℝ F i)

omit [CompleteSpace F] in
theorem reconstruct (x : F) : ∑ i, insert F i (coord F i x) = x := by
  exact (Module.finBasis ℝ F).sum_repr x

def operator : Lp F 2 (volume : Measure ℝ) →L[ℝ] Lp F 2 (volume : Measure ℝ) :=
  ∑ i, ((insert F i).compLpL 2 volume).comp
    (realHilbertL2.toContinuousLinearMap.comp ((coord F i).compLpL 2 volume))

omit [CompleteSpace F] in
theorem operator_coeFn (f : Lp F 2 (volume : Measure ℝ)) :
    operator F f =ᵐ[volume]
      fun x => ∑ i, insert F i (realHilbertL2 ((coord F i).compLpL 2 volume f) x) := by
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i =>
    (insert F i).compLpL 2 volume (realHilbertL2 ((coord F i).compLpL 2 volume f)))
  have hi := ae_all_iff.mpr fun i => (insert F i).coeFn_compLpL
    (realHilbertL2 ((coord F i).compLpL 2 volume f))
  filter_upwards [hs, hi] with x hx hi
  simp only [operator, sum_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [hx]
  exact Finset.sum_congr rfl fun i _ => hi i

omit [FiniteDimensional ℝ F] [CompleteSpace F] in
theorem kernel_integrable {f : ℝ → F} (hf : MemLp f 2 volume)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Integrable (fun y => (x-y)⁻¹ • f y)
      (volume.restrict {y : ℝ | ε < |x-y|}) := by
  exact memLp_one_iff_integrable.mp ((hf.mono_measure Measure.restrict_le_self).smul
    (hilbertKernel_memLp_two hε x) (r := 1))

theorem trunc_coord {f : ℝ → F} (hf : MemLp f 2 volume)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) (i : Fin (Module.finrank ℝ F)) :
    hilbertTrunc ε (fun y => coord F i (f y)) x = coord F i (hilbertTrunc ε f x) := by
  rw [hilbertTrunc, hilbertTrunc, map_smul,
    ← (coord F i).integral_comp_comm (kernel_integrable F hf hε x)]
  simp only [map_smul]

theorem operator_pv (f : ℝ → F) (hf : MemLp f 2 volume) :
    IsHilbertPVAe f (operator F (hf.toLp f)) := by
  have hcoord (i) : (coord F i).compLpL 2 volume (hf.toLp f) =
      ((coord F i).comp_memLp' hf).toLp (fun x => coord F i (f x)) := by
    apply Lp.ext
    filter_upwards [(coord F i).coeFn_compLpL (hf.toLp f), hf.coeFn_toLp,
      ((coord F i).comp_memLp' hf).coeFn_toLp] with x hx hfx hix
    simp only [Function.comp_def] at hix
    rw [hx, hfx, hix]
  have hpv : ∀ i, IsHilbertPVAe (fun x => coord F i (f x))
      (realHilbertL2 ((coord F i).compLpL 2 volume (hf.toLp f))) := by
    intro i
    rw [hcoord i]
    exact scalar_pv _ ((coord F i).comp_memLp' hf)
  filter_upwards [ae_all_iff.mpr hpv, operator_coeFn F (hf.toLp f)] with x hx hox
  rw [hox]
  have ht := tendsto_finsetSum Finset.univ fun i _ =>
    ((insert F i).continuous.tendsto _).comp (hx i)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change (∑ i, insert F i (hilbertTrunc ε (fun y => coord F i (f y)) x)) = hilbertTrunc ε f x
  simp_rw [trunc_coord F hf hε x]
  exact reconstruct F _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem comp_pv (T : E →L[ℝ] F) (f : ℝ → E) (hf : MemLp f 2 volume) :
    IsHilbertPVAe (fun x => T (f x))
      (operator F (T.compLpL 2 volume (hf.toLp f))) := by
  have he : T.compLpL 2 volume (hf.toLp f) =
      (T.comp_memLp' hf).toLp (fun x => T (f x)) := by
    apply Lp.ext
    filter_upwards [T.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp,
      (T.comp_memLp' hf).coeFn_toLp] with x hx hfx hTx
    simp only [Function.comp_def] at hTx
    rw [hx, hfx, hTx]
  rw [he]
  exact operator_pv F _ (T.comp_memLp' hf)

variable {𝕜 : Type*} [RCLike 𝕜]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
  [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 F]

theorem bound_on_L2 {T : E →L[𝕜] F} {C : ℝ≥0} (hC : HilbertBound 2 T C)
    (u : Lp E 2 (volume : Measure ℝ)) :
    ‖operator F ((T.restrictScalars ℝ).compLpL 2 volume u)‖ ≤ (C : ℝ) * ‖u‖ := by
  let U := (operator F).comp ((T.restrictScalars ℝ).compLpL 2 volume)
  change ‖U u‖ ≤ (C : ℝ) * ‖u‖
  refine (Lp.dense_hasCompactSupport_contDiff (E := ℝ) (F := E)
    (μ := volume) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction
    (P := fun v => ‖U v‖ ≤ (C : ℝ) * ‖v‖) ?_ ?_ u
  · rintro v ⟨φ, hvφ, hc, hφ⟩
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
    have hφ2 := hilbertTest_memLp hφ1 hc 2
    have hv : v = hφ2.toLp φ := Lp.ext (hvφ.trans hφ2.coeFn_toLp.symm)
    obtain ⟨g, hpv, hg, hb⟩ := hC φ hφ1 hc
    have hUv : IsHilbertPVAe (fun x => T (φ x)) (U v) := by
      rw [hv]
      exact comp_pv F (T.restrictScalars ℝ) φ hφ2
    have he := hUv.unique hpv.ae
    calc
      ‖U v‖ = (eLpNorm g 2 volume).toReal := by
        rw [Lp.norm_def, eLpNorm_congr_ae he]
      _ ≤ ((C : ℝ≥0∞) * eLpNorm φ 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hφ2.eLpNorm_ne_top) hb
      _ = (C : ℝ) * ‖v‖ := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal, hv, Lp.norm_toLp]
  · exact isClosed_le (continuous_norm.comp U.continuous) (continuous_const.mul continuous_norm)

theorem extension {T : E →L[𝕜] F} {C : ℝ≥0} (hC : HilbertBound 2 T C)
    (f : ℝ → E) (hf : MemLp f 2 volume) :
    ∃ g : ℝ → F, IsHilbertPVAe (fun x => T (f x)) g ∧ MemLp g 2 volume ∧
      eLpNorm g 2 volume ≤ (C : ℝ≥0∞) * eLpNorm f 2 volume := by
  let u := operator F ((T.restrictScalars ℝ).compLpL 2 volume (hf.toLp f))
  refine ⟨u, comp_pv F (T.restrictScalars ℝ) f hf, Lp.memLp u, ?_⟩
  have hb := ENNReal.ofReal_le_ofReal (bound_on_L2 F hC (hf.toLp f))
  have hin : eLpNorm (hf.toLp f) 2 volume = eLpNorm f 2 volume :=
    eLpNorm_congr_ae hf.coeFn_toLp
  simpa only [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ofReal_norm, Lp.enorm_def, hin] using hb

end HilbertUMD.HilbertL2Extension
