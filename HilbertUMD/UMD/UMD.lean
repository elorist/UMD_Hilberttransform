import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Finite Lp martingales and operator UMD bounds

The manuscript permits sigma-finite sample spaces. Global Lp membership need
not imply global L1 membership on such spaces. Accordingly `IsLpMartingale`
uses equality of integrals over finite-measure events in the earlier sigma
algebra. Its equivalence with mathlib's `Martingale` is proved when the
process is globally integrable, in particular on finite measure spaces.

`UMDBound` tests all finite processes and all unimodular scalar coefficients.
`umdConstant` takes the infimum of the finite bounds in the extended
nonnegative reals, so an unbounded operator has constant infinity.
The sample-space universe is an explicit universe parameter. Its independence
at p=2 is proved in `UMD/UniverseIndependence` through the finite dyadic reduction.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace HilbertUMD

universe uΩ

section Martingales

variable {Ω ι E F 𝕜 : Type*} [MeasurableSpace Ω] [Preorder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {ℱ : Filtration ι ‹MeasurableSpace Ω›}
  {p : ℝ≥0∞} {f : ι → Ω → E}

/-- The locally integrable characterization of an Lp martingale. -/
structure IsLpMartingale (f : ι → Ω → E)
    (ℱ : Filtration ι ‹MeasurableSpace Ω›) (p : ℝ≥0∞) (μ : Measure Ω) : Prop where
  stronglyAdapted : StronglyAdapted ℱ f
  memLp : ∀ i, MemLp (f i) p μ
  setIntegral_eq : ∀ i j, i ≤ j → ∀ s, MeasurableSet[ℱ i] s → μ s < ∞ →
    ∫ x in s, f i x ∂μ = ∫ x in s, f j x ∂μ

theorem IsLpMartingale.integrableOn (hf : IsLpMartingale f ℱ p μ)
    (hp : 1 ≤ p) (i : ι) {s : Set Ω} (hs : μ s < ∞) : IntegrableOn (f i) s μ := by
  have : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hs⟩
  exact ((hf.memLp i).restrict s).integrable hp

theorem IsLpMartingale.martingale [CompleteSpace E] [SigmaFiniteFiltration μ ℱ]
    (hf : IsLpMartingale f ℱ p μ) (hfi : ∀ i, Integrable (f i) μ) : Martingale f ℱ μ := by
  refine ⟨hf.stronglyAdapted, ?_⟩
  intro i j hij
  exact (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i) (hfi j)
    (fun s _ _ => (hfi i).integrableOn)
    (fun s hs hμs => hf.setIntegral_eq i j hij s hs hμs)
    (hf.stronglyAdapted i).aestronglyMeasurable).symm

theorem IsLpMartingale.map [RCLike 𝕜] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F]
    (hf : IsLpMartingale f ℱ p μ) (hp : 1 ≤ p) (T : E →L[𝕜] F) :
    IsLpMartingale (fun i x => T (f i x)) ℱ p μ := by
  refine ⟨fun i => T.continuous.comp_stronglyMeasurable (hf.stronglyAdapted i),
    fun i => T.comp_memLp' (hf.memLp i), ?_⟩
  intro i j hij s hs hμs
  rw [T.integral_comp_comm (hf.integrableOn hp i hμs),
    T.integral_comp_comm (hf.integrableOn hp j hμs), hf.setIntegral_eq i j hij s hs hμs]

end Martingales

section Transforms

variable {Ω E F 𝕜 : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [RCLike 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {m : ℕ}

/-- The sum of the chronological differences, indexed from zero in Lean. -/
def differenceSum (f : Fin (m + 1) → Ω → E) (x : Ω) : E :=
  ∑ k : Fin m, (f k.succ x - f k.castSucc x)

theorem differenceSum_eq (f : Fin (m + 1) → Ω → E) (x : Ω) :
    differenceSum f x = f (Fin.last m) x - f 0 x := by
  have h₁ := Fin.sum_univ_succ (fun k => f k x)
  have h₂ := Fin.sum_univ_castSucc (fun k => f k x)
  simp only [differenceSum, Finset.sum_sub_distrib]
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa [add_comm] using h₁.symm.trans h₂

/-- A deterministic martingale transform followed by the coefficient operator. -/
def martingaleTransform (T : E →L[𝕜] F) (ε : Fin m → 𝕜)
    (f : Fin (m + 1) → Ω → E) (x : Ω) : F :=
  ∑ k : Fin m, ε k • T (f k.succ x - f k.castSucc x)

theorem martingaleTransform_zero (ε : Fin m → 𝕜) (f : Fin (m + 1) → Ω → E) :
    martingaleTransform (0 : E →L[𝕜] F) ε f = 0 := by
  ext x
  simp [martingaleTransform]

theorem martingaleTransform_eq_map (T : E →L[𝕜] F) (ε : Fin m → 𝕜)
    (f : Fin (m + 1) → Ω → E) (x : Ω) :
    martingaleTransform T ε f x =
      T (martingaleTransform (ContinuousLinearMap.id 𝕜 E) ε f x) := by
  simp [martingaleTransform, map_sum]

theorem martingaleTransform_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (A : F →L[𝕜] G) (T : E →L[𝕜] F) (ε : Fin m → 𝕜)
    (f : Fin (m + 1) → Ω → E) (x : Ω) :
    martingaleTransform (A.comp T) ε f x = A (martingaleTransform T ε f x) := by
  simp [martingaleTransform, map_sum]

theorem differenceSum_map (T : E →L[𝕜] F) (f : Fin (m + 1) → Ω → E) (x : Ω) :
    differenceSum (fun k y => T (f k y)) x = T (differenceSum f x) := by
  simp [differenceSum, map_sum]

theorem martingaleTransform_precomp {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : F →L[𝕜] G) (A : E →L[𝕜] F) (ε : Fin m → 𝕜)
    (f : Fin (m + 1) → Ω → E) (x : Ω) :
    martingaleTransform (T.comp A) ε f x =
      martingaleTransform T ε (fun k y => A (f k y)) x := by
  simp [martingaleTransform]

theorem differenceSum_memLp [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}
    {f : Fin (m + 1) → Ω → E} (hf : ∀ k, MemLp (f k) p μ) :
    MemLp (differenceSum f) p μ := by
  have heq : differenceSum f = f (Fin.last m) - f 0 := funext (differenceSum_eq f)
  rw [heq]
  exact (hf (Fin.last m)).sub (hf 0)

theorem martingaleTransform_memLp [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}
    (T : E →L[𝕜] F) (ε : Fin m → 𝕜) {f : Fin (m + 1) → Ω → E}
    (hf : ∀ k, MemLp (f k) p μ) : MemLp (martingaleTransform T ε f) p μ := by
  exact memLp_finsetSum Finset.univ fun k _ =>
    (T.comp_memLp' ((hf k.succ).sub (hf k.castSucc))).const_smul (ε k)

/-- The pointwise operator norm bound lifted to the extended Lp norm. -/
theorem eLpNorm_map_le [MeasurableSpace Ω] (T : E →L[𝕜] F)
    (f : Ω → E) (p : ℝ≥0∞) (μ : Measure Ω) :
    eLpNorm (fun x => T (f x)) p μ ≤ (‖T‖₊ : ℝ≥0∞) * eLpNorm f p μ := by
  exact eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall fun x => T.le_opNNNorm (f x)) p

end Transforms

section Constants

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The manuscript's operator UMD inequality on all sigma-finite sample spaces
in universe `uΩ`, with all unimodular scalars of the chosen field. -/
def UMDBound (p : ℝ≥0∞) (T : E →L[𝕜] F) (C : ℝ≥0) : Prop :=
  ∀ (Ω : Type uΩ) (mΩ : MeasurableSpace Ω) (μ : Measure Ω), SigmaFinite μ →
  ∀ (m : ℕ), 1 ≤ m →
  ∀ (ℱ : Filtration (Fin (m + 1)) mΩ), SigmaFiniteFiltration μ ℱ →
  ∀ (f : Fin (m + 1) → Ω → E), IsLpMartingale f ℱ p μ →
  ∀ (ε : Fin m → 𝕜), (∀ k, ‖ε k‖ = 1) →
    eLpNorm (martingaleTransform T ε f) p μ ≤ (C : ℝ≥0∞) * eLpNorm (differenceSum f) p μ

/-- Least finite UMD bound, or infinity if no finite bound exists. -/
def umdConstant (p : ℝ≥0∞) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : UMDBound.{uΩ} p T C), (C : ℝ≥0∞)

theorem UMDBound.mono {p : ℝ≥0∞} {T : E →L[𝕜] F} {C D : ℝ≥0}
    (hC : UMDBound.{uΩ} p T C) (hCD : C ≤ D) : UMDBound.{uΩ} p T D := by
  intro Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε
  exact (hC Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε).trans
    (mul_le_mul' (by exact_mod_cast hCD) le_rfl)

theorem umdConstant_le {p : ℝ≥0∞} {T : E →L[𝕜] F} {C : ℝ≥0}
    (hC : UMDBound.{uΩ} p T C) : umdConstant.{uΩ} p T ≤ C :=
  iInf_le_of_le C (iInf_le_of_le hC le_rfl)

theorem le_umdConstant {p : ℝ≥0∞} {T : E →L[𝕜] F} {a : ℝ≥0∞}
    (ha : ∀ C : ℝ≥0, UMDBound.{uΩ} p T C → a ≤ C) : a ≤ umdConstant.{uΩ} p T :=
  le_iInf fun C => le_iInf fun hC => ha C hC

theorem umdBound_zero (p : ℝ≥0∞) : UMDBound.{uΩ} p (0 : E →L[𝕜] F) 0 := by
  intro Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε
  simp [martingaleTransform_zero]

@[simp] theorem umdConstant_zero (p : ℝ≥0∞) :
    umdConstant.{uΩ} p (0 : E →L[𝕜] F) = 0 := by
  exact bot_unique (umdConstant_le (umdBound_zero p))

/-- Postcomposition is bounded by the norm of the outside operator. -/
theorem UMDBound.postcomp {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {p : ℝ≥0∞} {T : E →L[𝕜] F} {C : ℝ≥0}
    (hC : UMDBound.{uΩ} p T C) (A : F →L[𝕜] G) :
    UMDBound.{uΩ} p (A.comp T) (‖A‖₊ * C) := by
  intro Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε
  rw [show martingaleTransform (A.comp T) ε f =
    (fun x => A (martingaleTransform T ε f x)) from funext (martingaleTransform_comp A T ε f)]
  calc
    eLpNorm (fun x => A (martingaleTransform T ε f x)) p μ
        ≤ (‖A‖₊ : ℝ≥0∞) * eLpNorm (martingaleTransform T ε f) p μ :=
      eLpNorm_map_le A _ p μ
    _ ≤ (‖A‖₊ : ℝ≥0∞) * ((C : ℝ≥0∞) * eLpNorm (differenceSum f) p μ) :=
      mul_le_mul' le_rfl (hC Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε)
    _ = _ := by simp [mul_assoc]

/-- Precomposition is bounded by the norm of the inside operator. -/
theorem UMDBound.precomp {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedSpace 𝕜 G] [CompleteSpace G] [CompleteSpace E]
    {p : ℝ≥0∞} {T : E →L[𝕜] F} {C : ℝ≥0}
    (hC : UMDBound.{uΩ} p T C) (hp : 1 ≤ p) (A : G →L[𝕜] E) :
    UMDBound.{uΩ} p (T.comp A) (C * ‖A‖₊) := by
  intro Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε
  rw [show martingaleTransform (T.comp A) ε f =
    martingaleTransform T ε (fun k x => A (f k x)) from
      funext (martingaleTransform_precomp T A ε f)]
  calc
    eLpNorm (martingaleTransform T ε (fun k x => A (f k x))) p μ
        ≤ (C : ℝ≥0∞) * eLpNorm (differenceSum (fun k x => A (f k x))) p μ :=
      hC Ω mΩ μ hμ m hm ℱ hℱ _ (hf.map hp A) ε hε
    _ = (C : ℝ≥0∞) * eLpNorm (fun x => A (differenceSum f x)) p μ := by
      rw [show differenceSum (fun k x => A (f k x)) =
        (fun x => A (differenceSum f x)) from funext (differenceSum_map A f)]
    _ ≤ (C : ℝ≥0∞) * ((‖A‖₊ : ℝ≥0∞) * eLpNorm (differenceSum f) p μ) :=
      mul_le_mul' le_rfl (eLpNorm_map_le A _ p μ)
    _ = _ := by simp [mul_assoc]

end Constants

end HilbertUMD
