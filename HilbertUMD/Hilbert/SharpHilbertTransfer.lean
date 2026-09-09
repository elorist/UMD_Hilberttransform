import HilbertUMD.Analysis.ScalarAmplification
import HilbertUMD.UMD.SharpUMDTransfer
import HilbertUMD.Hilbert.HilbertConstant
import HilbertUMD.Interfaces.HilbertPV
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Sharp principal-value Hilbert transfer

The transfer, finite coordinate reconstruction, and smooth-density steps are
proved locally. Only the final real/complex scalar principal-value/Fourier
identifications are imported from the isolated cited bridge.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
open scoped ContDiff
namespace HilbertUMD
namespace L2Transfer

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem compLpL_toLp {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F) (f : ℝ → E) (hf : MemLp f 2 volume) :
    A.compLpL 2 volume (hf.toLp f) = (A.comp_memLp' hf).toLp (fun t => A (f t)) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp,
    (A.comp_memLp' hf).coeFn_toLp] with t ha hf' hg
  rw [ha, hf']
  exact hg.symm

theorem lp_eq_of_coordinates {f g : Lp (Vec 𝕜 n) 2 (volume : Measure ℝ)}
    (h : ∀ j, (coordinate (𝕜 := 𝕜) (n := n) j).compLpL 2 volume f =
      (coordinate (𝕜 := 𝕜) (n := n) j).compLpL 2 volume g) :
    f = g := by
  have hj : ∀ j : Leaf n, (fun t => f t j) =ᵐ[volume] (fun t => g t j) := by
    intro j
    filter_upwards [(coordinate (𝕜 := 𝕜) j).coeFn_compLpL f,
      (coordinate (𝕜 := 𝕜) j).coeFn_compLpL g] with t hf hg
    change coordinate (𝕜 := 𝕜) j (f t) = coordinate (𝕜 := 𝕜) j (g t)
    rw [← hf, h j, hg]
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hj] with t ht
  exact funext ht

/-- A scalar PV/Fourier identification, with its concrete scalar L² operator. -/
def ScalarPV (U : Lp 𝕜 2 (volume : Measure ℝ) →L[𝕜] Lp 𝕜 2 (volume : Measure ℝ)) : Prop :=
  ∀ (f : ℝ → 𝕜) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f),
    ∃ (g : ℝ → 𝕜) (hg : MemLp g 2 volume), IsHilbertPV f g ∧
      hg.toLp g = U ((hilbertTest_memLp hf hc 2).toLp f)

/-- Finite coordinate reconstruction from the scalar PV identification. -/
theorem ScalarPV.vector
    {U : Lp 𝕜 2 (volume : Measure ℝ) →L[𝕜] Lp 𝕜 2 (volume : Measure ℝ)} (hU : ScalarPV U)
    (f : ℝ → Vec 𝕜 n) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ (g : ℝ → Vec 𝕜 n) (hg : MemLp g 2 volume), IsHilbertPV f g ∧
      hg.toLp g = amplification volume U ((hilbertTest_memLp hf hc 2).toLp f) := by
  classical
  have hcoord (j : Leaf n) : ContDiff ℝ 1 (fun t => f t j) :=
    ((coordinate (𝕜 := 𝕜) j).restrictScalars ℝ).contDiff.comp hf
  have hcompact (j : Leaf n) : HasCompactSupport (fun t => f t j) :=
    hc.comp_left (coordinate (𝕜 := 𝕜) j).map_zero
  choose g hg hpv heq using fun j : Leaf n => hU (fun t => f t j) (hcoord j) (hcompact j)
  have hgVec : MemLp (fun t j => g j t) 2 volume := memLp_pi_iff.mpr hg
  refine ⟨fun t j => g j t, hgVec, ?_, ?_⟩
  · intro t
    apply tendsto_pi_nhds.mpr
    intro j
    apply (hpv j t).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hilbertTrunc_map ((coordinate (𝕜 := 𝕜) j).restrictScalars ℝ)
      (hf.continuous.integrable_of_hasCompactSupport hc) hε t
  · apply lp_eq_of_coordinates
    intro j
    rw [coordinate_amplification, compLpL_toLp, compLpL_toLp]
    exact heq j

/-- On smooth compact tests, a manuscript Hilbert bound controls the actual
coordinatewise Fourier operator in the mixed `l¹` to `l∞` norm. -/
theorem ScalarPV.mixed_smooth
    {U : Lp 𝕜 2 (volume : Measure ℝ) →L[𝕜] Lp 𝕜 2 (volume : Measure ℝ)} (hU : ScalarPV U)
    {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    {C : ℝ≥0} (hC : HilbertBound 2 (asL1Operator n T h) C)
    (f : ℝ → Vec 𝕜 n) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    fibreNorm volume (toImage T)
        (amplification volume U ((hilbertTest_memLp hf hc 2).toLp f)) ≤
      (C : ℝ) * fibreNorm volume (toL1 (𝕜 := 𝕜) (n := n)) ((hilbertTest_memLp hf hc 2).toLp f) := by
  obtain ⟨g, hg, hpv, heq⟩ := hU.vector f hf hc
  have hfL : ContDiff ℝ 1 (fun t => toL1 (f t)) :=
    ((toL1 (𝕜 := 𝕜) (n := n)).restrictScalars ℝ).contDiff.comp hf
  have hcL : HasCompactSupport (fun t => toL1 (f t)) := hc.comp_left (toL1 (𝕜 := 𝕜) (n := n)).map_zero
  obtain ⟨q, hq, hqm, hqn⟩ := hC (fun t => toL1 (f t)) hfL hcL
  have hgpv : IsHilbertPV (fun t => T (f t)) (fun t => T (g t)) :=
    hpv.map (hf.continuous.integrable_of_hasCompactSupport hc) ((toImage T).restrictScalars ℝ)
  have hqeq : q = (fun t => T (g t)) := hq.unique hgpv
  subst q
  rw [← heq, fibreNorm_apply, fibreNorm_apply, compLpL_toLp, compLpL_toLp,
    Lp.norm_toLp, Lp.norm_toLp]
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (hilbertTest_memLp hfL hcL 2).eLpNorm_ne_top) hqn
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, toImage_apply] using hb

set_option maxHeartbeats 800000 in
/-- Smooth compact density extends the mixed bound to every genuine L² input. -/
theorem ScalarPV.mixed
    {U : Lp 𝕜 2 (volume : Measure ℝ) →L[𝕜] Lp 𝕜 2 (volume : Measure ℝ)} (hU : ScalarPV U)
    {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    {C : ℝ≥0} (hC : HilbertBound 2 (asL1Operator n T h) C)
    (f : Lp (Vec 𝕜 n) 2 (volume : Measure ℝ)) :
    fibreNorm volume (toImage T) (amplification volume U f) ≤
      (C : ℝ) * fibreNorm volume (toL1 (𝕜 := 𝕜) (n := n)) f := by
  have hd : Dense {z : Lp (Vec 𝕜 n) 2 (volume : Measure ℝ) |
      ∃ g : ℝ → Vec 𝕜 n, z =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    Lp.dense_hasCompactSupport_contDiff (F := Vec 𝕜 n)
    (μ := (volume : Measure ℝ)) (p := 2) (by norm_num)
  have hs : IsClosed {g : Lp (Vec 𝕜 n) 2 (volume : Measure ℝ) |
      fibreNorm volume (toImage T) (amplification volume U g) ≤
        (C : ℝ) * fibreNorm volume (toL1 (𝕜 := 𝕜) (n := n)) g} :=
    isClosed_le ((continuous_fibreNorm volume (toImage T)).comp (amplification volume U).continuous)
      (continuous_const.mul (continuous_fibreNorm volume (toL1 (𝕜 := 𝕜) (n := n))))
  apply hs.closure_subset_iff.mpr ?_ (hd f)
  rintro z ⟨g, hzg, hc, hg⟩
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hz : z = (hilbertTest_memLp hg1 hc 2).toLp g := by
    apply Lp.ext
    exact hzg.trans (hilbertTest_memLp hg1 hc 2).coeFn_toLp.symm
  rw [hz]
  exact hU.mixed_smooth h hC g hg1 hc

def fromGraph (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : GraphSpace T →L[𝕜] Vec 𝕜 n :=
  LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := GraphSpace T) (F' := Vec 𝕜 n) LinearMap.id

@[simp] theorem toGraph_fromGraph (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) (x : GraphSpace T) :
    toGraph T (fromGraph T x) = x := rfl

set_option maxHeartbeats 800000 in
/-- The sharp Hilbert bound follows from scalar PV identification, scalar L²
contractivity, and the manuscript's mixed operator bound. No density or vector
PV identification is assumed. -/
theorem ScalarPV.sharp_graph
    {U : Lp 𝕜 2 (volume : Measure ℝ) →L[𝕜] Lp 𝕜 2 (volume : Measure ℝ)} (hU : ScalarPV U)
    (hUn : ∀ z, ‖U z‖ ≤ ‖z‖)
    {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ 𝕜 (GraphSpace T)]
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    {C : ℝ≥0} (hC : HilbertBound 2 (asL1Operator n T h) C) :
    HilbertBound 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) (sharpTransferBound n C) := by
  intro f hf hc
  have hfB : ContDiff ℝ 1 (fun t => fromGraph T (f t)) :=
    ((fromGraph T).restrictScalars ℝ).contDiff.comp hf
  have hcB : HasCompactSupport (fun t => fromGraph T (f t)) := hc.comp_left (fromGraph T).map_zero
  obtain ⟨g, hg, hpv, heq⟩ := hU.vector (fun t => fromGraph T (f t)) hfB hcB
  have hpvG := hpv.map (hfB.continuous.integrable_of_hasCompactSupport hcB)
    ((toGraph T).restrictScalars ℝ)
  refine ⟨fun t => toGraph T (g t), hpvG, (toGraph T).comp_memLp' hg, ?_⟩
  have hsq := scalar_transfer volume hT U hUn C (hU.mixed h hC)
    ((hilbertTest_memLp hfB hcB 2).toLp (fun t => fromGraph T (f t)))
  have hn : fibreNorm volume (toGraph T)
        (amplification volume U ((hilbertTest_memLp hfB hcB 2).toLp (fun t => fromGraph T (f t)))) ≤
      (sharpTransferBound n C : ℝ) * fibreNorm volume (toGraph T)
        ((hilbertTest_memLp hfB hcB 2).toLp (fun t => fromGraph T (f t))) := by
    apply (sq_le_sq₀ (apply_nonneg _ _) (by positivity)).mp
    rw [mul_pow]
    have hs : (sharpTransferBound n C : ℝ) ^ 2 = (C : ℝ) ^ 2 + 2 * ((n : ℝ) + 1) := by
      exact_mod_cast sharpTransferBound_sq n C
    rw [hs]
    exact hsq
  rw [← heq, fibreNorm_apply, fibreNorm_apply, compLpL_toLp, compLpL_toLp] at hn
  have hen := ENNReal.ofReal_le_ofReal hn
  simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    ofReal_norm, Lp.enorm_toLp, toGraph_fromGraph] using hen

end L2Transfer

/-- Uses the real scalar PV/Fourier identification. -/
theorem HilbertBound.sharp_graph_real {n : ℕ} {T : Vec ℝ n →ₗ[ℝ] Vec ℝ n}
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    {C : ℝ≥0} (hC : HilbertBound 2 (asL1Operator n T h) C) :
    HilbertBound 2 (ContinuousLinearMap.id ℝ (GraphSpace T)) (sharpTransferBound n C) := by
  have hpv : L2Transfer.ScalarPV realHilbertL2.toContinuousLinearMap :=
    Interfaces.real_scalar_pv_fourier
  exact hpv.sharp_graph (fun z => (realHilbertL2.norm_map z).le) hT h hC

/-- Uses the complex scalar PV/Fourier identification. -/
theorem HilbertBound.sharp_graph_complex {n : ℕ} {T : Vec ℂ n →ₗ[ℂ] Vec ℂ n}
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ ℂ (GraphSpace T)]
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    {C : ℝ≥0} (hC : HilbertBound 2 (asL1Operator n T h) C) :
    HilbertBound 2 (ContinuousLinearMap.id ℂ (GraphSpace T)) (sharpTransferBound n C) := by
  have hpv : L2Transfer.ScalarPV hilbertL2.toContinuousLinearMap :=
    Interfaces.complex_scalar_pv_fourier
  exact hpv.sharp_graph (fun z => (hilbertL2.norm_map z).le) hT h hC

/-- The extended-real infimum argument, independent of the analytic bridge. -/
theorem hilbertConstant_sharp_graph_of_bounds {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n} [NormedSpace ℝ (GraphSpace T)]
    (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x)
    (hTransfer : ∀ C : ℝ≥0, HilbertBound 2 (asL1Operator n T h) C →
      HilbertBound 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) (sharpTransferBound n C)) :
    hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (GraphSpace T)) ^ 2 ≤
      hilbertConstant 2 (asL1Operator n T h) ^ 2 + 2 * ((n : ℝ≥0∞) + 1) := by
  conv_rhs => rw [hilbertConstant]
  simp_rw [ennreal_iInf_sq, ENNReal.iInf_add]
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  calc
    _ ≤ (sharpTransferBound n C : ℝ≥0∞) ^ 2 :=
      pow_le_pow_left₀ bot_le (hilbertConstant_le (hTransfer C hC)) 2
    _ = _ := by
      rw [← ENNReal.coe_pow, sharpTransferBound_sq]
      push_cast
      rfl

/-- Proposition 2.2 for the actual real principal-value Hilbert constants.
Uses the scalar PV/Fourier identification. -/
theorem hilbertConstant_sharp_graph_real {n : ℕ} {T : Vec ℝ n →ₗ[ℝ] Vec ℝ n}
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) :
    hilbertConstant 2 (ContinuousLinearMap.id ℝ (GraphSpace T)) ^ 2 ≤
      hilbertConstant 2 (asL1Operator n T h) ^ 2 + 2 * ((n : ℝ≥0∞) + 1) :=
  hilbertConstant_sharp_graph_of_bounds h (fun _ hC => hC.sharp_graph_real hT h)

/-- Proposition 2.2 for the actual complex principal-value Hilbert constants.
Uses the scalar PV/Fourier identification. -/
theorem hilbertConstant_sharp_graph_complex {n : ℕ} {T : Vec ℂ n →ₗ[ℂ] Vec ℂ n}
    [NormedSpace ℝ (GraphSpace T)] [IsScalarTower ℝ ℂ (GraphSpace T)]
    (hT : TransferAssumptions T) (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) :
    hilbertConstant 2 (ContinuousLinearMap.id ℂ (GraphSpace T)) ^ 2 ≤
      hilbertConstant 2 (asL1Operator n T h) ^ 2 + 2 * ((n : ℝ≥0∞) + 1) :=
  hilbertConstant_sharp_graph_of_bounds h (fun _ hC => hC.sharp_graph_complex hT h)

end HilbertUMD
