import HilbertUMD.Hilbert.HilbertConstant
import HilbertUMD.Hilbert.HilbertPVPointwise
import HilbertUMD.Hilbert.HilbertPVFourier
import HilbertUMD.Hilbert.FiniteComplexHilbertPV
import HilbertUMD.Hilbert.FiniteRealHilbertPV

/-!
# Principal-value/Fourier identifications

External source: Tuomas Hytönen, Jan van Neerven, Mark Veraar and Lutz Weis,
*Analysis in Banach Spaces, Volume I: Martingales and Littlewood-Paley Theory*,
Springer, 2016. Section 5.1, p. 374 proves pointwise existence of the principal
value for `C¹` compactly supported Banach-valued functions. Lemma 5.2.1,
pp. 388–389, gives the bounded truncated Fourier multipliers, and Proposition
5.2.2, p. 389 identifies the multiplier as `-i sign`.

The scalar identification is proved in `HilbertPVFourier`: symmetric frequency
cutoffs have inverse kernel `(1 - cos (2πRx)) / (πx)`. Symmetrization cancels
the singularity, Riemann–Lebesgue gives the pointwise PV limit, and Plancherel
plus an a.e. convergent subsequence identifies that limit with the L² operator.
The integral and L² Fourier transforms are compared through tempered distributions.
The everywhere-representative interface follows from the pointwise existence
proved independently in `HilbertPVPointwise` and uniqueness of the PV.
The finite-dimensional complex reconstruction is proved in
`HilbertValued.pv_fourier_of_scalar`, using the checked Fourier naturality lemmas.
The real finite-dimensional reconstruction is proved in
`FiniteRealHilbert.pv_fourier_of_scalar`, with the scalar identity as a hypothesis.

All statements in this file are proved without admitted dependencies.
The Fourier operators and their norm, inverse, and symmetry properties are
proved independently in `HilbertUMD.Hilbert.HilbertL2`.
The real scalar statement is deduced from the complex scalar statement by
embedding the input into `ℂ` and taking real parts, so it has no separate
admission.
-/

noncomputable section

open MeasureTheory

namespace HilbertUMD.Interfaces

/-- Scalar PV/Fourier identification, proved by symmetric frequency cutoffs,
Riemann–Lebesgue and Plancherel convergence. -/
theorem complex_scalar_pv_fourier_ae (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    IsHilbertPVAe f (hilbertL2 ((hilbertTest_memLp hf hc 2).toLp f)) := by
  exact scalar_pv_fourier_ae hf
    (hf.continuous.integrable_of_hasCompactSupport hc) (hilbertTest_memLp hf hc 2)

/-- The original smooth-test interface, deduced from the a.e. Fourier
identification and the independently proved pointwise PV existence. -/
theorem complex_scalar_pv_fourier (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∃ (g : ℝ → ℂ) (hg : MemLp g 2 volume), IsHilbertPV f g ∧
      hg.toLp g = hilbertL2 ((hilbertTest_memLp hf hc 2).toLp f) := by
  exact exists_isHilbertPV_toLp_eq hf hc _ (complex_scalar_pv_fourier_ae f hf hc)

/-- The real scalar specialization of `complex_scalar_pv_fourier`, using the
real restriction constructed here. -/
theorem real_scalar_pv_fourier (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∃ (g : ℝ → ℝ) (hg : MemLp g 2 volume), IsHilbertPV f g ∧
      hg.toLp g = realHilbertL2 ((hilbertTest_memLp hf hc 2).toLp f) := by
  have hfC : ContDiff ℝ 1 (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcC : HasCompactSupport (fun x => (f x : ℂ)) :=
    hc.comp_left Complex.ofRealCLM.map_zero
  obtain ⟨g, hg, hpv, heq⟩ := complex_scalar_pv_fourier _ hfC hcC
  have hgre : MemLp (fun x => (g x).re) 2 volume := Complex.reCLM.comp_memLp' hg
  refine ⟨fun x => (g x).re, hgre, ?_, ?_⟩
  · simpa using hpv.map (hfC.continuous.integrable_of_hasCompactSupport hcC)
      Complex.reCLM
  · have hinput : (hilbertTest_memLp hfC hcC 2).toLp (fun x => (f x : ℂ)) =
        l2OfReal ((hilbertTest_memLp hf hc 2).toLp f) := by
      apply Lp.ext
      filter_upwards [(hilbertTest_memLp hfC hcC 2).coeFn_toLp,
        l2OfReal_coeFn ((hilbertTest_memLp hf hc 2).toLp f),
        (hilbertTest_memLp hf hc 2).coeFn_toLp] with x hC ho hr
      simp only [hC, ho, hr]
    calc
      hgre.toLp (fun x => (g x).re) = l2Re (hg.toLp g) := by
        apply Lp.ext
        filter_upwards [hgre.coeFn_toLp, l2Re_coeFn (hg.toLp g), hg.coeFn_toLp]
          with x hr hRe hgx
        simp only [hr, hRe, hgx]
      _ = l2Re (hilbertL2 (l2OfReal ((hilbertTest_memLp hf hc 2).toLp f))) := by
        rw [heq, hinput]
      _ = realHilbertL2 ((hilbertTest_memLp hf hc 2).toLp f) := rfl

/-- Finite-dimensional complex Hilbert specialization of `complex_scalar_pv_fourier`.
Orthonormal-basis reconstruction and Fourier naturality are checked separately. -/
theorem finite_complex_hilbert_pv_fourier (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]
    (f : ℝ → F) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ (g : ℝ → F) (hg : MemLp g 2 volume), IsHilbertPV f g ∧
      hg.toLp g = HilbertValued.hilbertL2 F ((hilbertTest_memLp hf hc 2).toLp f) := by
  exact HilbertValued.pv_fourier_of_scalar complex_scalar_pv_fourier F f hf hc

/-- Finite-dimensional real Hilbert reconstruction from `real_scalar_pv_fourier`.
The coordinatewise deduction is checked in `FiniteRealHilbert.pv_fourier_of_scalar`. -/
theorem finite_real_hilbert_pv_fourier {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : OrthonormalBasis ι ℝ F) (f : ℝ → F) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∃ (g : ℝ → F) (hg : MemLp g 2 volume), IsHilbertPV f g ∧
      hg.toLp g = FiniteRealHilbert.hilbertL2 b ((hilbertTest_memLp hf hc 2).toLp f) := by
  exact FiniteRealHilbert.pv_fourier_of_scalar real_scalar_pv_fourier b f hf hc

end HilbertUMD.Interfaces
