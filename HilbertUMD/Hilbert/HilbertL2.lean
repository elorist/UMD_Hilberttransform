import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sign

/-!
# The scalar Hilbert transform on complex L²

The Fourier multiplier construction here uses mathlib's Plancherel equivalence.
Identification with the principal-value integral is a separate analytic obligation.
-/

noncomputable section

open MeasureTheory

namespace HilbertUMD

/-- A representative of `-i sign ξ`, with the harmless value `-i` at zero. -/
def hilbertSymbol (ξ : ℝ) : ℂ := if ξ < 0 then Complex.I else -Complex.I

theorem measurable_hilbertSymbol : Measurable hilbertSymbol := by
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

@[simp] theorem norm_hilbertSymbol (ξ : ℝ) : ‖hilbertSymbol ξ‖ = 1 := by
  simp only [hilbertSymbol]
  split_ifs <;> simp

@[simp] theorem hilbertSymbol_mul_self (ξ : ℝ) : hilbertSymbol ξ * hilbertSymbol ξ = -1 := by
  simp only [hilbertSymbol]
  split_ifs <;> simp

abbrev ComplexL2 := Lp ℂ 2 (volume : Measure ℝ)

private theorem hilbertSymbol_memLp (f : ComplexL2) :
    MemLp (fun ξ => hilbertSymbol ξ * f ξ) 2 volume := by
  apply (Lp.memLp f).congr_norm
  · exact measurable_hilbertSymbol.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · exact Filter.Eventually.of_forall fun ξ => by simp

/-- Multiplication by the Hilbert transform symbol on complex L². -/
def hilbertMultiplier (f : ComplexL2) : ComplexL2 :=
  (hilbertSymbol_memLp f).toLp (fun ξ => hilbertSymbol ξ * f ξ)

theorem hilbertMultiplier_coeFn (f : ComplexL2) :
    hilbertMultiplier f =ᵐ[volume] (fun ξ => hilbertSymbol ξ * f ξ) :=
  MemLp.coeFn_toLp (hilbertSymbol_memLp f)

theorem hilbertMultiplier_add (f g : ComplexL2) :
    hilbertMultiplier (f + g) = hilbertMultiplier f + hilbertMultiplier g := by
  apply Lp.ext
  filter_upwards [hilbertMultiplier_coeFn (f + g), hilbertMultiplier_coeFn f,
    hilbertMultiplier_coeFn g, Lp.coeFn_add f g,
    Lp.coeFn_add (hilbertMultiplier f) (hilbertMultiplier g)] with ξ hfg hf hg hadd hout
  simp only [Pi.add_apply] at hadd hout
  rw [hfg, hout, hf, hg, hadd, mul_add]

theorem hilbertMultiplier_smul (c : ℂ) (f : ComplexL2) :
    hilbertMultiplier (c • f) = c • hilbertMultiplier f := by
  apply Lp.ext
  filter_upwards [hilbertMultiplier_coeFn (c • f), hilbertMultiplier_coeFn f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (hilbertMultiplier f)] with ξ hcf hf hc hout
  simp only [Pi.smul_apply, smul_eq_mul] at hc hout
  rw [hcf, hout, hf, hc]
  ring

@[simp] theorem norm_hilbertMultiplier (f : ComplexL2) : ‖hilbertMultiplier f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [hilbertMultiplier_coeFn f] with ξ hξ
  simp [hξ]

@[simp] theorem hilbertMultiplier_sq (f : ComplexL2) :
    hilbertMultiplier (hilbertMultiplier f) = -f := by
  apply Lp.ext
  filter_upwards [hilbertMultiplier_coeFn (hilbertMultiplier f), hilbertMultiplier_coeFn f,
    Lp.coeFn_neg f] with ξ hh hf hneg
  simp only [Pi.neg_apply] at hneg
  rw [hh, hf, hneg, ← mul_assoc, hilbertSymbol_mul_self, neg_one_mul]

/-- The multiplier as a complex linear isometry. -/
def hilbertMultiplierLI : ComplexL2 →ₗᵢ[ℂ] ComplexL2 where
  toFun := hilbertMultiplier
  map_add' := hilbertMultiplier_add
  map_smul' := hilbertMultiplier_smul
  norm_map' := norm_hilbertMultiplier

/-- The Hilbert transform, defined on all complex L² by the Fourier multiplier. -/
def hilbertL2 : ComplexL2 →ₗᵢ[ℂ] ComplexL2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearIsometry.comp
    (hilbertMultiplierLI.comp (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearIsometry)

@[simp] theorem norm_hilbertL2 (f : ComplexL2) : ‖hilbertL2 f‖ = ‖f‖ :=
  hilbertL2.norm_map f

@[simp] theorem hilbertL2_sq (f : ComplexL2) : hilbertL2 (hilbertL2 f) = -f := by
  simp [hilbertL2, hilbertMultiplierLI, hilbertMultiplier_sq]

/-- The Fourier transform of the constructed operator has the expected symbol. -/
theorem fourier_hilbertL2 (f : ComplexL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ) (hilbertL2 f) =
      hilbertMultiplier ((Lp.fourierTransformₗᵢ ℝ ℂ) f) := by
  simp [hilbertL2, hilbertMultiplierLI]

namespace HilbertValued

variable (F : Type*) [NormedAddCommGroup F]

section Normed

variable [NormedSpace ℂ F]

abbrev L2Space := Lp F 2 (volume : Measure ℝ)

instance [Nontrivial F] : Nontrivial (L2Space F) := by
  obtain ⟨c, hc⟩ := exists_ne (0 : F)
  let f : L2Space F := indicatorConstLp 2
    (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)) (by simp) c
  have hf : ‖f‖ = ‖c‖ := by
    simp [f, norm_indicatorConstLp, measureReal_def]
  exact nontrivial_of_ne f 0 fun h => hc (norm_eq_zero.mp (by simpa [h] using hf.symm))

private theorem symbol_memLp (f : L2Space F) :
    MemLp (fun ξ => hilbertSymbol ξ • f ξ) 2 volume := by
  apply (Lp.memLp f).congr_norm
  · exact measurable_hilbertSymbol.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f)
  · exact Filter.Eventually.of_forall fun ξ => by simp [norm_smul]

/-- The same symbol acts isometrically on L² with any complex normed target. -/
def multiplier (f : L2Space F) : L2Space F :=
  (symbol_memLp F f).toLp (fun ξ => hilbertSymbol ξ • f ξ)

theorem multiplier_coeFn (f : L2Space F) :
    multiplier F f =ᵐ[volume] (fun ξ => hilbertSymbol ξ • f ξ) :=
  MemLp.coeFn_toLp (symbol_memLp F f)

theorem multiplier_add (f g : L2Space F) :
    multiplier F (f + g) = multiplier F f + multiplier F g := by
  apply Lp.ext
  filter_upwards [multiplier_coeFn F (f + g), multiplier_coeFn F f,
    multiplier_coeFn F g, Lp.coeFn_add f g,
    Lp.coeFn_add (multiplier F f) (multiplier F g)] with ξ hfg hf hg hadd hout
  simp only [Pi.add_apply] at hadd hout
  rw [hfg, hout, hf, hg, hadd, smul_add]

theorem multiplier_smul (c : ℂ) (f : L2Space F) :
    multiplier F (c • f) = c • multiplier F f := by
  apply Lp.ext
  filter_upwards [multiplier_coeFn F (c • f), multiplier_coeFn F f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (multiplier F f)] with ξ hcf hf hc hout
  simp only [Pi.smul_apply] at hc hout
  rw [hcf, hout, hf, hc, smul_comm]

@[simp] theorem norm_multiplier (f : L2Space F) : ‖multiplier F f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [multiplier_coeFn F f] with ξ hξ
  simp [hξ, norm_smul]

@[simp] theorem multiplier_sq (f : L2Space F) :
    multiplier F (multiplier F f) = -f := by
  apply Lp.ext
  filter_upwards [multiplier_coeFn F (multiplier F f), multiplier_coeFn F f,
    Lp.coeFn_neg f] with ξ hh hf hneg
  simp only [Pi.neg_apply] at hneg
  rw [hh, hf, hneg, ← mul_smul, hilbertSymbol_mul_self, neg_one_smul]

def multiplierLI : L2Space F →ₗᵢ[ℂ] L2Space F where
  toFun := multiplier F
  map_add' := multiplier_add F
  map_smul' := multiplier_smul F
  norm_map' := norm_multiplier F

end Normed

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The Fourier multiplier Hilbert transform with a complete complex Hilbert target. -/
def hilbertL2 : L2Space F →ₗᵢ[ℂ] L2Space F :=
  (Lp.fourierTransformₗᵢ ℝ F).symm.toLinearIsometry.comp
    ((multiplierLI F).comp (Lp.fourierTransformₗᵢ ℝ F).toLinearIsometry)

@[simp] theorem norm_hilbertL2 (f : L2Space F) : ‖hilbertL2 F f‖ = ‖f‖ :=
  (hilbertL2 F).norm_map f

@[simp] theorem hilbertL2_sq (f : L2Space F) : hilbertL2 F (hilbertL2 F f) = -f := by
  simp [hilbertL2, multiplierLI, multiplier_sq]

theorem fourier_hilbertL2 (f : L2Space F) :
    (Lp.fourierTransformₗᵢ ℝ F) (hilbertL2 F f) =
      multiplier F ((Lp.fourierTransformₗᵢ ℝ F) f) := by
  simp [hilbertL2, multiplierLI]

@[simp] theorem hilbertL2_operatorNorm [Nontrivial F] :
    ‖(hilbertL2 F).toContinuousLinearMap‖ = 1 :=
  (hilbertL2 F).norm_toContinuousLinearMap

end HilbertValued

@[simp] theorem hilbertL2_operatorNorm : ‖hilbertL2.toContinuousLinearMap‖ = 1 :=
  hilbertL2.norm_toContinuousLinearMap

open FourierTransform
open scoped ComplexConjugate

theorem fourier_conj_realLine (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => conj (f x)) ξ = conj (𝓕 f (-ξ)) := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_I,
    Complex.conj_ofReal]
  congr 2
  simp

def schwartzConj (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  f.postcompCLM Complex.conjCLE.toContinuousLinearMap

def l2Conj : ComplexL2 →L[ℝ] ComplexL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume

theorem l2Conj_coeFn (f : ComplexL2) : l2Conj f =ᵐ[volume] (fun x => conj (f x)) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLp f

def l2Reflect : ComplexL2 →ₗᵢ[ℂ] ComplexL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x) (Measure.measurePreserving_neg volume)

theorem l2Reflect_coeFn (f : ComplexL2) : l2Reflect f =ᵐ[volume] (fun x => f (-x)) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg volume)

theorem schwartzConj_toLp (f : SchwartzMap ℝ ℂ) :
    (schwartzConj f).toLp 2 = l2Conj (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(schwartzConj f).coeFn_toLp 2, l2Conj_coeFn (f.toLp 2),
    f.coeFn_toLp 2] with x hs hc hf
  rw [hs, hc, hf]
  rfl

theorem l2Reflect_schwartz_fourier (f : SchwartzMap ℝ ℂ) :
    l2Conj (l2Reflect ((𝓕 f).toLp 2)) = (𝓕 (schwartzConj f)).toLp 2 := by
  apply Lp.ext
  have href : ∀ᵐ x : ℝ ∂volume, ((𝓕 f).toLp 2) (-x) = (𝓕 f) (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      ((𝓕 f).coeFn_toLp 2 volume)
  filter_upwards [l2Conj_coeFn (l2Reflect ((𝓕 f).toLp 2)),
    l2Reflect_coeFn ((𝓕 f).toLp 2), href, (𝓕 (schwartzConj f)).coeFn_toLp 2]
      with x hc hr hf hs
  rw [hc, hr, hf, hs]
  exact (fourier_conj_realLine f x).symm

/-- Complex conjugation becomes conjugation followed by reflection in frequency. -/
theorem fourier_l2Conj (f : ComplexL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ) (l2Conj f) =
      l2Conj (l2Reflect ((Lp.fourierTransformₗᵢ ℝ ℂ) f)) := by
  apply DenseRange.induction_on (p := fun f : ComplexL2 =>
    (Lp.fourierTransformₗᵢ ℝ ℂ) (l2Conj f) =
      l2Conj (l2Reflect ((Lp.fourierTransformₗᵢ ℝ ℂ) f)))
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
      (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp l2Conj.continuous)
      (l2Conj.continuous.comp (l2Reflect.continuous.comp
        (Lp.fourierTransformₗᵢ ℝ ℂ).continuous))
  intro g
  simp only [SchwartzMap.toLpCLM_apply]
  rw [← schwartzConj_toLp]
  change 𝓕 ((schwartzConj g).toLp 2) = l2Conj (l2Reflect (𝓕 (g.toLp 2)))
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
    l2Reflect_schwartz_fourier]

theorem hilbertSymbol_conj_neg {ξ : ℝ} (hξ : ξ ≠ 0) :
    conj (hilbertSymbol (-ξ)) = hilbertSymbol ξ := by
  rcases hξ.lt_or_gt with h | h
  · simp [hilbertSymbol, h, h.not_gt]
  · simp [hilbertSymbol, h, h.not_gt]

theorem l2Conj_reflect_coeFn (f : ComplexL2) :
    l2Conj (l2Reflect f) =ᵐ[volume] (fun ξ => conj (f (-ξ))) := by
  filter_upwards [l2Conj_coeFn (l2Reflect f), l2Reflect_coeFn f] with ξ hc hr
  rw [hc, hr]

theorem l2Conj_reflect_multiplier (f : ComplexL2) :
    l2Conj (l2Reflect (hilbertMultiplier f)) =
      hilbertMultiplier (l2Conj (l2Reflect f)) := by
  apply Lp.ext
  have hm : ∀ᵐ x : ℝ ∂volume,
      hilbertMultiplier f (-x) = hilbertSymbol (-x) * f (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (hilbertMultiplier_coeFn f)
  filter_upwards [l2Conj_reflect_coeFn (hilbertMultiplier f), hm,
    hilbertMultiplier_coeFn (l2Conj (l2Reflect f)), l2Conj_reflect_coeFn f,
    volume.ae_ne (0 : ℝ)] with ξ hleft hm hright hf hξ
  rw [hleft, hm, map_mul, hilbertSymbol_conj_neg hξ, hright, hf]

theorem hilbertL2_conj (f : ComplexL2) : hilbertL2 (l2Conj f) = l2Conj (hilbertL2 f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_hilbertL2, fourier_l2Conj, fourier_l2Conj, fourier_hilbertL2,
    l2Conj_reflect_multiplier]

abbrev RealL2 := Lp ℝ 2 (volume : Measure ℝ)

def l2OfReal : RealL2 →L[ℝ] ComplexL2 := Complex.ofRealCLM.compLpL 2 volume

def l2Re : ComplexL2 →L[ℝ] RealL2 := Complex.reCLM.compLpL 2 volume

theorem l2OfReal_coeFn (f : RealL2) :
    l2OfReal f =ᵐ[volume] (fun x => (f x : ℂ)) :=
  Complex.ofRealCLM.coeFn_compLp f

theorem l2Re_coeFn (f : ComplexL2) : l2Re f =ᵐ[volume] (fun x => (f x).re) :=
  Complex.reCLM.coeFn_compLp f

@[simp] theorem l2Re_ofReal (f : RealL2) : l2Re (l2OfReal f) = f := by
  apply Lp.ext
  filter_upwards [l2Re_coeFn (l2OfReal f), l2OfReal_coeFn f] with x hr hf
  simp [hr, hf]

@[simp] theorem norm_l2OfReal (f : RealL2) : ‖l2OfReal f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [l2OfReal_coeFn f] with x hx
  simp [hx]

@[simp] theorem l2Conj_ofReal (f : RealL2) : l2Conj (l2OfReal f) = l2OfReal f := by
  apply Lp.ext
  filter_upwards [l2Conj_coeFn (l2OfReal f), l2OfReal_coeFn f] with x hc hf
  simp [hc, hf]

theorem l2OfReal_re_of_conj {f : ComplexL2} (hf : l2Conj f = f) : l2OfReal (l2Re f) = f := by
  apply Lp.ext
  have hc := l2Conj_coeFn f
  rw [hf] at hc
  filter_upwards [l2OfReal_coeFn (l2Re f), l2Re_coeFn f, hc] with x ho hr hc
  rw [ho, hr]
  exact Complex.conj_eq_iff_re.mp hc.symm

/-- Restriction of the actual complex Fourier multiplier to real-valued L². -/
def realHilbertL2CLM : RealL2 →L[ℝ] RealL2 :=
  l2Re.comp ((hilbertL2.toContinuousLinearMap.restrictScalars ℝ).comp l2OfReal)

theorem ofReal_realHilbertL2 (f : RealL2) :
    l2OfReal (realHilbertL2CLM f) = hilbertL2 (l2OfReal f) := by
  change l2OfReal (l2Re (hilbertL2 (l2OfReal f))) = hilbertL2 (l2OfReal f)
  apply l2OfReal_re_of_conj
  rw [← hilbertL2_conj, l2Conj_ofReal]

@[simp] theorem norm_realHilbertL2 (f : RealL2) : ‖realHilbertL2CLM f‖ = ‖f‖ := by
  rw [← norm_l2OfReal (realHilbertL2CLM f), ofReal_realHilbertL2,
    norm_hilbertL2, norm_l2OfReal]

def realHilbertL2 : RealL2 →ₗᵢ[ℝ] RealL2 where
  toLinearMap := realHilbertL2CLM.toLinearMap
  norm_map' := norm_realHilbertL2

@[simp] theorem realHilbertL2_sq (f : RealL2) : realHilbertL2 (realHilbertL2 f) = -f := by
  have hinj : Function.Injective l2OfReal := Function.LeftInverse.injective l2Re_ofReal
  apply hinj
  change l2OfReal (realHilbertL2CLM (realHilbertL2CLM f)) = l2OfReal (-f)
  rw [ofReal_realHilbertL2, ofReal_realHilbertL2, hilbertL2_sq, map_neg]

open RealInnerProductSpace in
theorem realHilbertL2_skew (f g : RealL2) :
    ⟪realHilbertL2 f, g⟫ = -⟪f, realHilbertL2 g⟫ := by
  have h := realHilbertL2.inner_map_map f (realHilbertL2 g)
  simpa using congrArg Neg.neg h

@[simp] theorem realHilbertL2_operatorNorm : ‖realHilbertL2.toContinuousLinearMap‖ = 1 :=
  realHilbertL2.norm_toContinuousLinearMap

open scoped RealInnerProductSpace

namespace FiniteRealHilbert

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (b : OrthonormalBasis ι ℝ F)

abbrev Space := Lp F 2 (volume : Measure ℝ)

def coord (i : ι) : Space (F := F) →L[ℝ] RealL2 :=
  (innerSL ℝ (b i)).compLpL 2 volume

theorem coord_coeFn (i : ι) (f : Space (F := F)) :
    coord b i f =ᵐ[volume] (fun x => ⟪b i, f x⟫) :=
  (innerSL ℝ (b i)).coeFn_compLp f

def embed (i : ι) : RealL2 →L[ℝ] Space (F := F) :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i)).compLpL 2 volume

theorem embed_coeFn (i : ι) (f : RealL2) :
    embed b i f =ᵐ[volume] (fun x => f x • b i) :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i)).coeFn_compLp f

theorem coord_embed [DecidableEq ι] (i j : ι) (f : RealL2) :
    coord b i (embed b j f) = if i = j then f else 0 := by
  classical
  apply Lp.ext
  filter_upwards [coord_coeFn b i (embed b j f), embed_coeFn b j f,
    (Lp.coeFn_zero ℝ 2 volume)] with x hc he hzero
  rw [hc, he, inner_smul_right]
  by_cases hij : i = j
  · subst j
    simp [b.orthonormal.1 i]
  · simp [hij, b.orthonormal.2 hij]

theorem norm_sq_eq_sum_coord (f : Space (F := F)) :
    ‖f‖ ^ 2 = ∑ i, ‖coord b i f‖ ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner (coord b i f) (coord b i f))]
  apply integral_congr_ae
  have hc : ∀ᵐ x : ℝ ∂volume, ∀ i, coord b i f x = ⟪b i, f x⟫ :=
    ae_all_iff.mpr (fun i => coord_coeFn b i f)
  filter_upwards [hc] with x hx
  simp_rw [hx, RCLike.inner_apply, conj_trivial]
  simpa only [real_inner_comm] using (b.sum_inner_mul_inner (f x) (f x)).symm

def hilbertCLM : Space (F := F) →L[ℝ] Space (F := F) :=
  ∑ i, (embed b i).comp (realHilbertL2CLM.comp (coord b i))

theorem coord_hilbert (i : ι) (f : Space (F := F)) :
    coord b i (hilbertCLM b f) = realHilbertL2CLM (coord b i f) := by
  classical
  simp [hilbertCLM, map_sum, coord_embed]

@[simp] theorem norm_hilbert (f : Space (F := F)) : ‖hilbertCLM b f‖ = ‖f‖ := by
  have h : ‖hilbertCLM b f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [norm_sq_eq_sum_coord b, norm_sq_eq_sum_coord b]
    simp only [coord_hilbert, norm_realHilbertL2]
  nlinarith [norm_nonneg (hilbertCLM b f), norm_nonneg f]

theorem coord_ext {f g : Space (F := F)} (h : ∀ i, coord b i f = coord b i g) : f = g := by
  have hz : ‖f - g‖ ^ 2 = 0 := by
    rw [norm_sq_eq_sum_coord b]
    simp [map_sub, h]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The real Hilbert transform on a finite-dimensional real Hilbert space,
defined by its action on the coordinates of an orthonormal basis. -/
def hilbertL2 : Space (F := F) →ₗᵢ[ℝ] Space (F := F) where
  toLinearMap := (hilbertCLM b).toLinearMap
  norm_map' := norm_hilbert b

@[simp] theorem hilbertL2_sq (f : Space (F := F)) : hilbertL2 b (hilbertL2 b f) = -f := by
  apply coord_ext b
  intro i
  change coord b i (hilbertCLM b (hilbertCLM b f)) = coord b i (-f)
  rw [coord_hilbert, coord_hilbert, map_neg]
  exact realHilbertL2_sq _

@[simp] theorem hilbertL2_operatorNorm [Nontrivial F] :
    ‖(hilbertL2 b).toContinuousLinearMap‖ = 1 :=
  (hilbertL2 b).norm_toContinuousLinearMap

end FiniteRealHilbert

end HilbertUMD
