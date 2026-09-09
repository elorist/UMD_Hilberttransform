import HilbertUMD.Hilbert.HilbertConstant
import HilbertUMD.Hilbert.HilbertL2Naturality

/-!
# Finite-dimensional complex reconstruction of principal values

The scalar identity is an explicit hypothesis, so the reconstruction itself
has no admitted dependencies.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ComplexInnerProductSpace

namespace HilbertUMD.HilbertValued

/-- A scalar principal-value/Fourier identity reconstructs the identity in every
finite-dimensional complex Hilbert space. -/
theorem pv_fourier_of_scalar
    (hscalar : ∀ (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f),
      ∃ (g : ℝ → ℂ) (hg : MemLp g 2 volume), IsHilbertPV f g ∧
        hg.toLp g = HilbertUMD.hilbertL2 ((hilbertTest_memLp hf hc 2).toLp f))
    (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]
    (f : ℝ → F) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ (g : ℝ → F) (hg : MemLp g 2 volume), IsHilbertPV f g ∧
      hg.toLp g = HilbertValued.hilbertL2 F ((hilbertTest_memLp hf hc 2).toLp f) := by
  classical
  let b := stdOrthonormalBasis ℂ F
  let a (i : Fin (Module.finrank ℂ F)) : F →L[ℂ] ℂ := innerSL ℂ (b i)
  have hfi i : ContDiff ℝ 1 (fun x => a i (f x)) :=
    ((a i).restrictScalars ℝ).contDiff.comp hf
  have hci i : HasCompactSupport (fun x => a i (f x)) := hc.comp_left (a i).map_zero
  choose g hg hpv heq using fun i => hscalar _ (hfi i) (hci i)
  let G : ℝ → F := fun x => ∑ i, g i x • b i
  have hG : MemLp G 2 volume := memLp_finsetSum Finset.univ fun i _ =>
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (b i)).comp_memLp' (hg i)
  have hcoord (i) (x : ℝ) : a i (G x) = g i x := by
    change ⟪b i, ∑ j, g j x • b j⟫ = g i x
    exact b.orthonormal.inner_right_fintype _ _
  refine ⟨G, hG, ?_, ?_⟩
  · intro x
    have ht : Tendsto (fun ε => ∑ i, hilbertTrunc ε (fun y => a i (f y)) x • b i)
        (𝓝[>] 0) (𝓝 (G x)) :=
      tendsto_finsetSum _ fun i _ => (hpv i x).smul tendsto_const_nhds
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hmap i : hilbertTrunc ε (fun y => a i (f y)) x = a i (hilbertTrunc ε f x) :=
      hilbertTrunc_map ((a i).restrictScalars ℝ)
        (hf.continuous.integrable_of_hasCompactSupport hc) hε x
    simp_rw [hmap]
    exact b.sum_repr' _
  · have hinput i : (a i).compLpL 2 volume ((hilbertTest_memLp hf hc 2).toLp f) =
        (hilbertTest_memLp (hfi i) (hci i) 2).toLp (fun x => a i (f x)) := by
      apply Lp.ext
      filter_upwards [(a i).coeFn_compLpL ((hilbertTest_memLp hf hc 2).toLp f),
        (hilbertTest_memLp hf hc 2).coeFn_toLp,
        (hilbertTest_memLp (hfi i) (hci i) 2).coeFn_toLp] with x ha hf hfi
      simp only [ha, hf, hfi]
    have houtput i : (a i).compLpL 2 volume (hG.toLp G) = (hg i).toLp (g i) := by
      apply Lp.ext
      filter_upwards [(a i).coeFn_compLpL (hG.toLp G), hG.coeFn_toLp,
        (hg i).coeFn_toLp] with x ha hG hg
      simp only [ha, hG, hg, hcoord]
    have hequal i : (a i).compLpL 2 volume (hG.toLp G) =
        (a i).compLpL 2 volume
          (HilbertValued.hilbertL2 F ((hilbertTest_memLp hf hc 2).toLp f)) := by
      rw [houtput, ← HilbertValued.hilbertL2_compLp, hinput,
        HilbertValued.hilbertL2_complex, heq]
    apply Lp.ext
    have hcoords : ∀ᵐ x : ℝ ∂volume, ∀ i,
        a i (hG.toLp G x) = a i
          (HilbertValued.hilbertL2 F ((hilbertTest_memLp hf hc 2).toLp f) x) := by
      apply ae_all_iff.mpr
      intro i
      filter_upwards [(a i).coeFn_compLpL (hG.toLp G),
        (a i).coeFn_compLpL
          (HilbertValued.hilbertL2 F ((hilbertTest_memLp hf hc 2).toLp f))] with x h₁ h₂
      rw [hequal] at h₁
      exact h₁.symm.trans h₂
    filter_upwards [hcoords] with x hx
    rw [← b.sum_repr' (hG.toLp G x), ← b.sum_repr'
      (HilbertValued.hilbertL2 F ((hilbertTest_memLp hf hc 2).toLp f) x)]
    exact Finset.sum_congr rfl fun i _ => congrArg (fun c : ℂ => c • b i) (hx i)

end HilbertUMD.HilbertValued
