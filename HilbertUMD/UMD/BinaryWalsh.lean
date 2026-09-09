import HilbertUMD.LowerBounds.BinaryShift
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! Orthonormal binary sign functions and their finite Bessel inequality. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace HilbertUMD.BinaryLogit

def r (j : ℕ) (t : ℝ) : ℝ := sign ((tau^[j]) t)

theorem measurable_sign : Measurable sign := by
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

theorem measurable_r (j : ℕ) : Measurable (r j) :=
  measurable_sign.comp (measurable_tau.iterate j)

@[simp] theorem r_zero (t : ℝ) : r 0 t = sign t := rfl

theorem r_succ (j : ℕ) (t : ℝ) : r (j + 1) t = r j (tau t) := by
  simp only [r, Function.iterate_succ_apply]

@[simp] theorem norm_sign (t : ℝ) : ‖sign t‖ = 1 := by
  unfold sign
  split <;> norm_num

@[simp] theorem norm_r (j : ℕ) (t : ℝ) : ‖r j t‖ = 1 := norm_sign _

@[simp] theorem r_mul_self (j : ℕ) (t : ℝ) : r j t * r j t = 1 := by
  unfold r sign
  split <;> norm_num

theorem r_memLp (j : ℕ) (p : ℝ≥0∞) : MemLp (r j) p unitMeasure :=
  MemLp.of_bound (measurable_r j).aestronglyMeasurable 1
    (Eventually.of_forall (fun t => (norm_r j t).le))

theorem r_integrable (j : ℕ) : Integrable (r j) unitMeasure :=
  memLp_one_iff_integrable.mp (r_memLp j 1)

theorem integrable_mul_r {h : ℝ → ℝ} (hh : Integrable h unitMeasure) (j : ℕ) :
    Integrable (fun t => h t * r j t) unitMeasure :=
  hh.mul_bdd (measurable_r j).aestronglyMeasurable
    (Eventually.of_forall (fun t => (norm_r j t).le))

theorem integral_comp_tau_mul_sign {h : ℝ → ℝ} (hh : Integrable h unitMeasure) :
    (∫ t, h (tau t) * sign t ∂unitMeasure) = 0 := by
  have hi := integrable_mul_r
    (tau_measurePreserving.integrable_comp_of_integrable hh) 0
  have hl : Integrable (fun t => h (tau t) * sign t)
      (volume.restrict (Ioo (0 : ℝ) (1/2))) := by
    apply hi.mono_measure
    rw [unitMeasure_split]
    exact Measure.le_add_right le_rfl
  have hr : Integrable (fun t => h (tau t) * sign t)
      (volume.restrict (Ioo (1/2 : ℝ) 1)) := by
    apply hi.mono_measure
    rw [unitMeasure_split]
    exact Measure.le_add_left le_rfl
  have hleft : (∫ t in Ioo (0 : ℝ) (1/2), h (tau t) * sign t) =
      -(∫ t in Ioo (0 : ℝ) (1/2), h (2*t)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [tau, sign, if_pos ht.2, mul_neg_one]
  have hright : (∫ t in Ioo (1/2 : ℝ) 1, h (tau t) * sign t) =
      ∫ t in Ioo (1/2 : ℝ) 1, h (2*t-1) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [tau, sign, if_neg (not_lt.mpr ht.1.le), mul_one]
  have heleft := (measurableEmbedding_mulLeft₀ (by norm_num : (2 : ℝ) ≠ 0)).integral_map
    (μ := volume.restrict (Ioo (0 : ℝ) (1/2))) h
  have heright := ((measurableEmbedding_addRight (-1 : ℝ)).comp
    (measurableEmbedding_mulLeft₀ (by norm_num : (2 : ℝ) ≠ 0))).integral_map
    (μ := volume.restrict (Ioo (1/2 : ℝ) 1)) h
  change (∫ t, h t ∂(volume.restrict (Ioo (1/2 : ℝ) 1)).map
    (fun t => 2*t-1)) = ∫ t in Ioo (1/2 : ℝ) 1, h (2*t-1) at heright
  rw [map_double_left, integral_smul_measure] at heleft
  rw [map_double_right, integral_smul_measure] at heright
  rw [unitMeasure_split, integral_add_measure hl hr, hleft, hright,
    ← heleft, ← heright]
  simp

theorem pair_r_shift {h : ℝ → ℝ} (hh : Integrable h unitMeasure) (j : ℕ) :
    (∫ t, h (tau t) * r (j + 1) t ∂unitMeasure) =
      ∫ t, h t * r j t ∂unitMeasure := by
  simp_rw [r_succ]
  exact integral_comp_tau (integrable_mul_r hh j)

theorem pair_r_zero {h : ℝ → ℝ} (hh : Integrable h unitMeasure) :
    (∫ t, h (tau t) * r 0 t ∂unitMeasure) = 0 :=
  integral_comp_tau_mul_sign hh

theorem integral_r_mul_r (i j : ℕ) :
    (∫ t, r i t * r j t ∂unitMeasure) = if i = j then 1 else 0 := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => simp only [r_mul_self]; simp
    | succ j =>
      simpa only [r_succ, mul_comm, Nat.zero_ne_add_one, if_false] using
        pair_r_zero (r_integrable j)
  | succ i ih =>
    cases j with
    | zero =>
      simpa only [r_succ, Nat.add_one_ne_zero, if_false] using
        pair_r_zero (r_integrable i)
    | succ j =>
      simp only [r_succ]
      rw [integral_comp_tau (integrable_mul_r (r_integrable i) j), ih]
      simp

def rLp (j : ℕ) : Lp ℝ 2 unitMeasure := (r_memLp j 2).toLp (r j)

theorem rLp_inner (j : ℕ) {F : ℝ → ℝ} (hF : MemLp F 2 unitMeasure) :
    inner ℝ (rLp j) (hF.toLp F) = ∫ t, F t * r j t ∂unitMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(r_memLp j 2).coeFn_toLp, hF.coeFn_toLp] with t hr hF
  simp [rLp, hr, hF, RCLike.inner_apply]

theorem rLp_orthonormal : Orthonormal ℝ rLp := by
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℝ (rLp i) ((r_memLp j 2).toLp (r j)) = _
  rw [rLp_inner i (r_memLp j 2), integral_r_mul_r]
  simp [eq_comm]

theorem bessel (n : ℕ) {F : ℝ → ℝ} (hF : MemLp F 2 unitMeasure) :
    ∑ j : Fin n, (∫ t, F t * r j.val t ∂unitMeasure) ^ 2 ≤
      (eLpNorm F 2 unitMeasure).toReal ^ 2 := by
  have hb := (rLp_orthonormal.comp (fun j : Fin n => j.val) Fin.val_injective).sum_inner_products_le
    (s := Finset.univ) (hF.toLp F)
  simpa only [Function.comp_apply, rLp_inner, Real.norm_eq_abs, sq_abs,
    Lp.norm_toLp] using hb

end HilbertUMD.BinaryLogit
