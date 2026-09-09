import HilbertUMD.Hilbert.HilbertConstant

/-!
# Finite-dimensional real principal-value reconstruction

The scalar PV/Fourier identification is an explicit hypothesis. Reconstruction
along an orthonormal basis gives the already constructed real Hilbert operator.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace HilbertUMD.FiniteRealHilbert

/-- Reconstruct the real Hilbert-valued PV from the scalar PV/Fourier identity. -/
theorem pv_fourier_of_scalar
    (hscalar : ∀ (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u),
      ∃ (v : ℝ → ℝ) (hv : MemLp v 2 volume), IsHilbertPV u v ∧
        hv.toLp v = realHilbertL2 ((hilbertTest_memLp hu huc 2).toLp u))
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (b : OrthonormalBasis ι ℝ F) (f : ℝ → F)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ (g : ℝ → F) (hg : MemLp g 2 volume), IsHilbertPV f g ∧
      hg.toLp g = hilbertL2 b ((hilbertTest_memLp hf hc 2).toLp f) := by
  classical
  have hcoord (i : ι) : ContDiff ℝ 1 (fun x => ⟪b i, f x⟫) :=
    (innerSL ℝ (b i)).contDiff.comp hf
  have hcompact (i : ι) : HasCompactSupport (fun x => ⟪b i, f x⟫) :=
    hc.comp_left (innerSL ℝ (b i)).map_zero
  choose g hg hpv heq using fun i => hscalar _ (hcoord i) (hcompact i)
  let G : ℝ → F := fun x => ∑ i, g i x • b i
  have hG : MemLp G 2 volume :=
    memLp_finsetSum Finset.univ fun i _ =>
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i)).comp_memLp' (hg i)
  have hGcoord (i : ι) (x : ℝ) : ⟪b i, G x⟫ = g i x := by
    simp [G, inner_sum, inner_smul_right, b.inner_eq_ite]
  refine ⟨G, hG, ?_, ?_⟩
  · intro x
    have ht := tendsto_finsetSum Finset.univ (fun i _ => (hpv i x).smul_const (b i))
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    calc
      (∑ i, hilbertTrunc ε (fun y => ⟪b i, f y⟫) x • b i) =
          ∑ i, ⟪b i, hilbertTrunc ε f x⟫ • b i := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun r : ℝ => r • b i)
          (hilbertTrunc_map (innerSL ℝ (b i))
            (hf.continuous.integrable_of_hasCompactSupport hc) hε x)
      _ = hilbertTrunc ε f x := b.sum_repr' _
  · apply coord_ext b
    intro i
    change coord b i (hG.toLp G) =
      coord b i (hilbertCLM b ((hilbertTest_memLp hf hc 2).toLp f))
    rw [coord_hilbert]
    have houtput : coord b i (hG.toLp G) = (hg i).toLp (g i) := by
      apply Lp.ext
      filter_upwards [coord_coeFn b i (hG.toLp G), hG.coeFn_toLp,
        (hg i).coeFn_toLp] with x hcoord hGx hgx
      rw [hcoord, hGx, hgx, hGcoord]
    have hinput : coord b i ((hilbertTest_memLp hf hc 2).toLp f) =
        (hilbertTest_memLp (hcoord i) (hcompact i) 2).toLp (fun x => ⟪b i, f x⟫) := by
      apply Lp.ext
      filter_upwards [coord_coeFn b i ((hilbertTest_memLp hf hc 2).toLp f),
        (hilbertTest_memLp hf hc 2).coeFn_toLp,
        (hilbertTest_memLp (hcoord i) (hcompact i) 2).coeFn_toLp]
        with x hcoord hfx hix
      rw [hcoord, hfx, hix]
    rw [houtput, hinput]
    exact heq i

end HilbertUMD.FiniteRealHilbert
