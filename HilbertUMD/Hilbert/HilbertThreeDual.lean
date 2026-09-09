import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.Holder
import HilbertUMD.Analysis.ScalarThreeNorming

/-!
# Constructing an L3 operator from its action on L2 intersections

The intersection with L2 is a dense linear subspace of L3. A linear L2
operator whose values on this intersection satisfy an L3 bound therefore
has a bounded L3 extension, with the same constant and exact agreement on
the whole intersection. Skew pairing against a compatible bounded
L(3/2) operator supplies the required L3 bound, by actual truncated power
tests. No abstract dual representation or external analytic fact is used.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace HilbertUMD.HilbertThreeDual

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

/-- The actual L2 intersection, with the norm inherited from L3. -/
def domain : Submodule ℝ (Lp ℝ 3 μ) where
  carrier := {f | MemLp (fun x => f x) 2 μ}
  zero_mem' := (MemLp.zero : MemLp (0 : S → ℝ) 2 μ).ae_eq (Lp.coeFn_zero ℝ 3 μ).symm
  add_mem' {f g} hf hg := (hf.add hg).ae_eq (Lp.coeFn_add f g).symm
  smul_mem' c f hf := (hf.const_smul c).ae_eq (Lp.coeFn_smul c f).symm

theorem dense_domain : DenseRange (domain μ).subtype := by
  have hsimple : (Lp.simpleFunc ℝ 3 μ : Set (Lp ℝ 3 μ)) ⊆ domain μ := by
    intro f hf
    let s : Lp.simpleFunc ℝ 3 μ := ⟨f, hf⟩
    have h2 : MemLp (Lp.simpleFunc.toSimpleFunc s) 2 μ :=
      (SimpleFunc.memLp_iff (by norm_num) (by norm_num)).mpr
        ((SimpleFunc.memLp_iff (by norm_num) (by norm_num)).mp (Lp.simpleFunc.memLp s))
    exact h2.ae_eq (Lp.simpleFunc.toSimpleFunc_eq_toFun s)
  have hd := (Lp.simpleFunc.dense (E := ℝ) (μ := μ)
    (show (3 : ℝ≥0∞) ≠ ⊤ by norm_num)).mono hsimple
  intro f
  exact (show closure (Set.range (domain μ).subtype) = closure (domain μ : Set (Lp ℝ 3 μ)) by
    congr 1
    ext g
    simp).symm ▸ hd f

/-- Regard an element of the intersection as its L2 equivalence class. -/
def toTwo : domain μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := f.property.toLp (f : Lp ℝ 3 μ)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(f + g).property.coeFn_toLp, f.property.coeFn_toLp,
      g.property.coeFn_toLp, Lp.coeFn_add (f : Lp ℝ 3 μ) g,
      Lp.coeFn_add (f.property.toLp _) (g.property.toLp _)] with x hfg hf hg h3 h2
    change (f.property.toLp _ + g.property.toLp _) x = _ at h2
    change (((f : Lp ℝ 3 μ) + g) x) = _ at h3
    simpa only [hfg, h3, Pi.add_apply, h2, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(c • f).property.coeFn_toLp, f.property.coeFn_toLp,
      Lp.coeFn_smul c (f : Lp ℝ 3 μ), Lp.coeFn_smul c (f.property.toLp _)] with x hcf hf h3 h2
    change ((c • (f : Lp ℝ 3 μ)) x) = _ at h3
    simpa only [RingHom.id_apply, hcf, h3, h2, Pi.smul_apply, hf]

theorem coeFn_toTwo (f : domain μ) : toTwo μ f =ᵐ[μ] (f : Lp ℝ 3 μ) :=
  f.property.coeFn_toLp

variable (U : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  (hU : ∀ f : domain μ, MemLp (fun x => U (toTwo μ f) x) 3 μ)

/-- The L2 action, with its output in L3 by the assumed intersection estimate. -/
def intersectionMap : domain μ →ₗ[ℝ] Lp ℝ 3 μ where
  toFun f := (hU f).toLp (U (toTwo μ f))
  map_add' f g := by
    apply Lp.ext
    have hout : U (toTwo μ (f + g)) = U (toTwo μ f) + U (toTwo μ g) := by simp
    filter_upwards [(hU (f + g)).coeFn_toLp, (hU f).coeFn_toLp, (hU g).coeFn_toLp,
      Lp.coeFn_add (U (toTwo μ f)) (U (toTwo μ g)),
      Lp.coeFn_add ((hU f).toLp _) ((hU g).toLp _)] with x hfg hf hg h2 h3
    rw [hfg, hout, h2, h3]
    simp only [Pi.add_apply, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    have hout : U (toTwo μ (c • f)) = c • U (toTwo μ f) := by simp
    filter_upwards [(hU (c • f)).coeFn_toLp, (hU f).coeFn_toLp,
      Lp.coeFn_smul c (U (toTwo μ f)), Lp.coeFn_smul c ((hU f).toLp _)] with x hcf hf h2 h3
    change ((hU (c • f)).toLp _) x = (c • (hU f).toLp _) x
    rw [hcf, hout, h2, h3]
    simp only [Pi.smul_apply, hf]

theorem coeFn_intersectionMap (f : domain μ) :
    intersectionMap μ U hU f =ᵐ[μ] U (toTwo μ f) := (hU f).coeFn_toLp

/-- The actual bounded extension on all of L3. -/
def extension : Lp ℝ 3 μ →L[ℝ] Lp ℝ 3 μ :=
  (intersectionMap μ U hU).extendOfNorm (domain μ).subtype

theorem extension_eq {C : ℝ}
    (hbound : ∀ f : domain μ, ‖intersectionMap μ U hU f‖ ≤ C * ‖(f : Lp ℝ 3 μ)‖)
    (f : domain μ) : extension μ U hU f = intersectionMap μ U hU f :=
  LinearMap.extendOfNorm_eq (dense_domain μ) ⟨C, hbound⟩ f

theorem norm_extension_le {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ f : domain μ, ‖intersectionMap μ U hU f‖ ≤ C * ‖(f : Lp ℝ 3 μ)‖) :
    ‖extension μ U hU‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le (dense_domain μ) hC hbound

theorem extension_agrees_two {C : ℝ}
    (hbound : ∀ f : domain μ, ‖intersectionMap μ U hU f‖ ≤ C * ‖(f : Lp ℝ 3 μ)‖)
    (f : S → ℝ) (h2 : MemLp f 2 μ) (h3 : MemLp f 3 μ) :
    extension μ U hU (h3.toLp f) =ᵐ[μ] U (h2.toLp f) := by
  let g : domain μ := ⟨h3.toLp f, h2.ae_eq h3.coeFn_toLp.symm⟩
  have hg : toTwo μ g = h2.toLp f :=
    Lp.ext ((coeFn_toTwo μ g).trans (h3.coeFn_toLp.trans h2.coeFn_toLp.symm))
  change extension μ U hU g =ᵐ[μ] _
  rw [extension_eq μ U hU hbound g]
  exact (coeFn_intersectionMap μ U hU g).trans (by rw [hg])

/-- Dense extension preserves both the exact bound and all intersection values. -/
theorem exists_extension {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ f : domain μ, ‖intersectionMap μ U hU f‖ ≤ C * ‖(f : Lp ℝ 3 μ)‖) :
    ∃ R : Lp ℝ 3 μ →L[ℝ] Lp ℝ 3 μ, ‖R‖ ≤ C ∧
      ∀ (f : S → ℝ) (h2 : MemLp f 2 μ) (h3 : MemLp f 3 μ),
        R (h3.toLp f) =ᵐ[μ] U (h2.toLp f) :=
  ⟨extension μ U hU, norm_extension_le μ U hU hC hbound,
    extension_agrees_two μ U hU hbound⟩

/-- The dense extension criterion in the unbundled extended-norm form
supplied by dual testing. -/
theorem exists_extension_of_eLpNorm_bound {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ f : domain μ, MemLp (fun x => U (toTwo μ f) x) 3 μ ∧
      eLpNorm (fun x => U (toTwo μ f) x) 3 μ ≤ ENNReal.ofReal (C * ‖(f : Lp ℝ 3 μ)‖)) :
    ∃ R : Lp ℝ 3 μ →L[ℝ] Lp ℝ 3 μ, ‖R‖ ≤ C ∧
      ∀ (f : S → ℝ) (h2 : MemLp f 2 μ) (h3 : MemLp f 3 μ),
        R (h3.toLp f) =ᵐ[μ] U (h2.toLp f) := by
  let hmem := fun f : domain μ => (hbound f).1
  apply exists_extension μ U hmem hC
  intro f
  change ‖(hmem f).toLp _‖ ≤ _
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound f).2).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg hC (norm_nonneg _)))

local instance : Fact ((1 : ℝ≥0∞) ≤ 3 / 2) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num⟩

local instance : ENNReal.HolderConjugate (3 : ℝ≥0∞) (3 / 2) := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]⟩

theorem abs_pairing_le (f : Lp ℝ 3 μ) (g : Lp ℝ (3 / 2) μ) :
    |∫ x, f x * g x ∂μ| ≤ ‖f‖ * ‖g‖ := by
  have heq : (∫ x, f x * g x ∂μ) = L1.integral (f • g : Lp ℝ 1 μ) := by
    rw [L1.integral_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_lpSMul (r := 1) f g] with x hx
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using hx.symm
  rw [heq, ← Real.norm_eq_abs]
  exact (L1.norm_integral_le _).trans (Lp.norm_smul_le f g)

/-- Skew pairing and the compatible conjugate-exponent bound control every
L2∩L(3/2) test of the L2 output. -/
theorem intersection_pairing_bound
    (T : Lp ℝ (3 / 2) μ →L[ℝ] Lp ℝ (3 / 2) μ) {C : ℝ} (hT : ‖T‖ ≤ C)
    (hskew : ∀ f g : Lp ℝ 2 μ,
      (∫ x, U f x * g x ∂μ) = -(∫ x, f x * U g x ∂μ))
    (hagree : ∀ (g : S → ℝ) (h2 : MemLp g 2 μ) (hq : MemLp g (3 / 2) μ),
      U (h2.toLp g) =ᵐ[μ] T (hq.toLp g))
    (f : domain μ) (g : S → ℝ) (h2 : MemLp g 2 μ) (hq : MemLp g (3 / 2) μ) :
    |∫ x, U (toTwo μ f) x * g x ∂μ| ≤
      (C * ‖(f : Lp ℝ 3 μ)‖) * (eLpNorm g (3 / 2) μ).toReal := by
  have hleft : (∫ x, U (toTwo μ f) x * g x ∂μ) =
      ∫ x, U (toTwo μ f) x * h2.toLp g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  have hright : (∫ x, toTwo μ f x * U (h2.toLp g) x ∂μ) =
      ∫ x, (f : Lp ℝ 3 μ) x * T (hq.toLp g) x ∂μ := by
    apply integral_congr_ae
    filter_upwards [coeFn_toTwo μ f, hagree g h2 hq] with x hf hg
    rw [hf, hg]
  rw [hleft, hskew, hright, abs_neg]
  calc
    _ ≤ ‖(f : Lp ℝ 3 μ)‖ * ‖T (hq.toLp g)‖ := abs_pairing_le μ _ _
    _ ≤ ‖(f : Lp ℝ 3 μ)‖ * (C * ‖hq.toLp g‖) :=
      mul_le_mul_of_nonneg_left
        ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by rw [Lp.norm_toLp]; ring

/-- Construct the conjugate-exponent operator directly from its compatible
L2 realization and the L(3/2) bound. Every assumption is explicit; the
power tests, density, linear extension, and exact bound are checked. -/
theorem exists_three_of_two_threeHalves
    (T : Lp ℝ (3 / 2) μ →L[ℝ] Lp ℝ (3 / 2) μ) {C : ℝ} (hT : ‖T‖ ≤ C)
    (hskew : ∀ f g : Lp ℝ 2 μ,
      (∫ x, U f x * g x ∂μ) = -(∫ x, f x * U g x ∂μ))
    (hagree : ∀ (g : S → ℝ) (h2 : MemLp g 2 μ) (hq : MemLp g (3 / 2) μ),
      U (h2.toLp g) =ᵐ[μ] T (hq.toLp g)) :
    ∃ R : Lp ℝ 3 μ →L[ℝ] Lp ℝ 3 μ, ‖R‖ ≤ C ∧
      ∀ (f : S → ℝ) (h2 : MemLp f 2 μ) (h3 : MemLp f 3 μ),
        R (h3.toLp f) =ᵐ[μ] U (h2.toLp f) := by
  have hC : 0 ≤ C := (norm_nonneg T).trans hT
  apply exists_extension_of_eLpNorm_bound μ U hC
  intro f
  exact ScalarThreeNorming.memLp_three_of_pairing μ (Lp.memLp _)
    (mul_nonneg hC (norm_nonneg _)) (intersection_pairing_bound μ U T hT hskew hagree f)

end HilbertUMD.HilbertThreeDual
