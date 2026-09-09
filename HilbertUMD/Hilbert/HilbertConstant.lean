import HilbertUMD.Hilbert.HilbertL2

/-!
# Principal-value Hilbert transform constants

These definitions follow the manuscript's `C¹` compactly supported test-function
definition. Bounds include existence of the principal value, so no inequality is
vacuous when a principal value has not yet been constructed. Constants are infima
of finite bounds in `ℝ≥0∞`, with infinity when there is no finite bound.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace HilbertUMD

section PrincipalValue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The symmetrically truncated kernel, with the manuscript's `1/π` normalization. -/
def hilbertTrunc (ε : ℝ) (f : ℝ → E) (x : ℝ) : E :=
  (Real.pi)⁻¹ • ∫ y in {y : ℝ | ε < |x - y|}, (x - y)⁻¹ • f y

/-- The principal value exists at every point and is equal to `g`. -/
def IsHilbertPV (f g : ℝ → E) : Prop :=
  ∀ x : ℝ, Tendsto (fun ε : ℝ => hilbertTrunc ε f x) (𝓝[>] 0) (𝓝 (g x))

/-- The a.e. principal-value relation used for nonsmooth `L²` test functions. -/
def IsHilbertPVAe (f g : ℝ → E) : Prop :=
  ∀ᵐ x : ℝ ∂volume, Tendsto (fun ε : ℝ => hilbertTrunc ε f x) (𝓝[>] 0) (𝓝 (g x))

theorem IsHilbertPV.ae {f g : ℝ → E} (hg : IsHilbertPV f g) : IsHilbertPVAe f g :=
  Eventually.of_forall hg

theorem IsHilbertPVAe.unique {f g h : ℝ → E} (hg : IsHilbertPVAe f g)
    (hh : IsHilbertPVAe f h) : g =ᵐ[volume] h := by
  filter_upwards [hg, hh] with x hg hh
  exact tendsto_nhds_unique hg hh

theorem IsHilbertPV.unique {f g h : ℝ → E} (hg : IsHilbertPV f g)
    (hh : IsHilbertPV f h) : g = h :=
  funext fun x => tendsto_nhds_unique (hg x) (hh x)

@[simp] theorem hilbertTrunc_zero (ε x : ℝ) : hilbertTrunc ε (0 : ℝ → E) x = 0 := by
  simp [hilbertTrunc]

theorem isHilbertPV_zero : IsHilbertPV (0 : ℝ → E) 0 := by
  intro x
  simp only [hilbertTrunc_zero, Pi.zero_apply]
  exact tendsto_const_nhds

/-- Every test function used in the definition belongs to every `Lᵖ`. -/
theorem hilbertTest_memLp {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (p : ℝ≥0∞) : MemLp f p volume :=
  hf.continuous.memLp_of_hasCompactSupport hc

theorem hilbertTrunc_integrable {f : ℝ → E} (hf : Integrable f volume)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Integrable (fun y => (x - y)⁻¹ • f y)
      (volume.restrict {y : ℝ | ε < |x - y|}) := by
  have hs : MeasurableSet {y : ℝ | ε < |x - y|} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  apply hf.integrableOn.bdd_smul ε⁻¹
  · exact (measurable_const.sub measurable_id).inv.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hs] with y hy
    simp only [Real.norm_eq_abs, abs_inv]
    exact (inv_le_inv₀ (lt_trans hε hy) hε).mpr hy.le

theorem hilbertTrunc_map {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace E] [CompleteSpace G] (A : E →L[ℝ] G) {f : ℝ → E} (hf : Integrable f volume)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    hilbertTrunc ε (fun y => A (f y)) x = A (hilbertTrunc ε f x) := by
  rw [hilbertTrunc, hilbertTrunc, map_smul,
    ← A.integral_comp_comm (hilbertTrunc_integrable hf hε x)]
  simp only [map_smul]

theorem IsHilbertPV.map {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace E] [CompleteSpace G] {f g : ℝ → E} (hg : IsHilbertPV f g)
    (hf : Integrable f volume) (A : E →L[ℝ] G) :
    IsHilbertPV (fun x => A (f x)) (fun x => A (g x)) := by
  intro x
  have ht := (A.continuous.tendsto (g x)).comp (hg x)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hilbertTrunc_map A hf hε x).symm

theorem IsHilbertPVAe.map {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace E] [CompleteSpace G] {f g : ℝ → E} (hg : IsHilbertPVAe f g)
    (hf : Integrable f volume) (A : E →L[ℝ] G) :
    IsHilbertPVAe (fun x => A (f x)) (fun x => A (g x)) := by
  filter_upwards [hg] with x hx
  have ht := (A.continuous.tendsto (g x)).comp hx
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hilbertTrunc_map A hf hε x).symm

theorem hilbertTrunc_congr_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} (hfg : f =ᵐ[volume] g) (ε x : ℝ) :
    hilbertTrunc ε f x = hilbertTrunc ε g x := by
  unfold hilbertTrunc
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hfg] with t ht
  rw [ht]

theorem IsHilbertPVAe.congr_input {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g Hf : ℝ → E} (h : IsHilbertPVAe f Hf) (hfg : f =ᵐ[volume] g) :
    IsHilbertPVAe g Hf := by
  filter_upwards [h] with x hx
  simpa only [hilbertTrunc_congr_ae hfg] using hx

end PrincipalValue

section Constants

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

/-- A finite operator Hilbert-transform bound on all `C¹` compactly supported tests. -/
def HilbertBound (p : ℝ≥0∞) (T : E →L[𝕜] F) (C : ℝ≥0) : Prop :=
  ∀ f : ℝ → E, ContDiff ℝ 1 f → HasCompactSupport f →
    ∃ g : ℝ → F, IsHilbertPV (fun x => T (f x)) g ∧ MemLp g p volume ∧
      eLpNorm g p volume ≤ (C : ℝ≥0∞) * eLpNorm f p volume

/-- Least finite principal-value Hilbert-transform bound, or infinity if none exists. -/
def hilbertConstant (p : ℝ≥0∞) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : HilbertBound p T C), (C : ℝ≥0∞)

theorem HilbertBound.mono {p : ℝ≥0∞} {T : E →L[𝕜] F} {C D : ℝ≥0}
    (hC : HilbertBound p T C) (hCD : C ≤ D) : HilbertBound p T D := by
  intro f hf hc
  obtain ⟨g, hg, hgp, hgn⟩ := hC f hf hc
  exact ⟨g, hg, hgp, hgn.trans (mul_le_mul' (by exact_mod_cast hCD) le_rfl)⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem hilbert_eLpNorm_map_le (A : E →L[𝕜] F) (f : ℝ → E) (p : ℝ≥0∞) :
    eLpNorm (fun x => A (f x)) p volume ≤ (‖A‖₊ : ℝ≥0∞) * eLpNorm f p volume :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall fun x => A.le_opNNNorm (f x)) p

theorem HilbertBound.precomp {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedSpace 𝕜 G]
    [IsScalarTower ℝ 𝕜 G] [IsScalarTower ℝ 𝕜 E]
    {p : ℝ≥0∞} {T : E →L[𝕜] F} {C : ℝ≥0}
    (hC : HilbertBound p T C) (A : G →L[𝕜] E) :
    HilbertBound p (T.comp A) (C * ‖A‖₊) := by
  intro f hf hc
  obtain ⟨g, hg, hgp, hgn⟩ := hC (fun x => A (f x))
    ((A.restrictScalars ℝ).contDiff.comp hf) (hc.comp_left A.map_zero)
  refine ⟨g, hg, hgp, ?_⟩
  calc
    eLpNorm g p volume ≤ (C : ℝ≥0∞) * eLpNorm (fun x => A (f x)) p volume := hgn
    _ ≤ (C : ℝ≥0∞) * ((‖A‖₊ : ℝ≥0∞) * eLpNorm f p volume) :=
      mul_le_mul' le_rfl (hilbert_eLpNorm_map_le A f p)
    _ = _ := by simp [mul_assoc]

theorem HilbertBound.postcomp {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedSpace 𝕜 G] [CompleteSpace F] [CompleteSpace G]
    [IsScalarTower ℝ 𝕜 F] [IsScalarTower ℝ 𝕜 G]
    {p : ℝ≥0∞} {T : E →L[𝕜] F} {C : ℝ≥0}
    (hC : HilbertBound p T C) (A : F →L[𝕜] G) :
    HilbertBound p (A.comp T) (‖A‖₊ * C) := by
  intro f hf hc
  obtain ⟨g, hg, hgp, hgn⟩ := hC f hf hc
  refine ⟨fun x => A (g x), ?_, A.comp_memLp' hgp, ?_⟩
  · exact hg.map (T.integrable_comp (hf.continuous.integrable_of_hasCompactSupport hc))
      (A.restrictScalars ℝ)
  · calc
      eLpNorm (fun x => A (g x)) p volume
          ≤ (‖A‖₊ : ℝ≥0∞) * eLpNorm g p volume := hilbert_eLpNorm_map_le A g p
      _ ≤ (‖A‖₊ : ℝ≥0∞) * ((C : ℝ≥0∞) * eLpNorm f p volume) :=
        mul_le_mul' le_rfl hgn
      _ = _ := by simp [mul_assoc]

theorem hilbertConstant_le {p : ℝ≥0∞} {T : E →L[𝕜] F} {C : ℝ≥0}
    (hC : HilbertBound p T C) : hilbertConstant p T ≤ C :=
  iInf_le_of_le C (iInf_le_of_le hC le_rfl)

theorem le_hilbertConstant {p : ℝ≥0∞} {T : E →L[𝕜] F} {a : ℝ≥0∞}
    (ha : ∀ C : ℝ≥0, HilbertBound p T C → a ≤ C) : a ≤ hilbertConstant p T :=
  le_iInf fun C => le_iInf fun hC => ha C hC

theorem hilbertBound_zero (p : ℝ≥0∞) : HilbertBound p (0 : E →L[𝕜] F) 0 := by
  intro f hf hc
  refine ⟨0, ?_, by simp, ?_⟩
  · change IsHilbertPV (0 : ℝ → F) 0
    exact isHilbertPV_zero
  · simp

@[simp] theorem hilbertConstant_zero (p : ℝ≥0∞) :
    hilbertConstant p (0 : E →L[𝕜] F) = 0 :=
  bot_unique (hilbertConstant_le (hilbertBound_zero p))

/-- A proved `L²` isometry yields the manuscript's bound once the principal-value
identification is supplied explicitly. -/
theorem hilbertBound_two_of_isometry (T : E →L[𝕜] F)
    (U : Lp E 2 (volume : Measure ℝ) →ₗᵢ[𝕜] Lp F 2 (volume : Measure ℝ))
    (hU : ∀ (f : ℝ → E) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f),
      ∃ (g : ℝ → F) (hg : MemLp g 2 volume), IsHilbertPV (fun x => T (f x)) g ∧
        hg.toLp g = U ((hilbertTest_memLp hf hc 2).toLp f)) : HilbertBound 2 T 1 := by
  intro f hf hc
  obtain ⟨g, hg, hpv, heq⟩ := hU f hf hc
  refine ⟨g, hpv, hg, ?_⟩
  simp only [ENNReal.coe_one, one_mul]
  apply le_of_eq
  rw [← Lp.enorm_toLp hg, heq]
  rw [U.enorm_map, Lp.enorm_toLp]

end Constants

end HilbertUMD
