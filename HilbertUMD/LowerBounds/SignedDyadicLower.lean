import HilbertUMD.LowerBounds.HilbertLower
import HilbertUMD.Hilbert.HilbertOperatorSpaces
import HilbertUMD.LowerBounds.BinaryLogitDefs
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Direct signed-dyadic Hilbert lower bound from the interval-step witness.
No Hilbert/UMD quadratic comparison is used. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace HilbertUMD
namespace SignedDyadicPV

def intervalLog (a b t : ℝ) : ℝ := Real.log |(t - a) / (t - b)| / Real.pi

def logVec (n : ℕ) (t : ℝ) : Vec ℝ n := fun j =>
  intervalLog ((leafEquivFin n j).val / (2 ^ n : ℝ))
    (((leafEquivFin n j).val + 1) / (2 ^ n : ℝ)) t

theorem intervalLog_scale (a b t : ℝ) :
    intervalLog (a / 2) (b / 2) t = intervalLog a b (2 * t) := by
  unfold intervalLog
  congr 3
  have ha : t - a / 2 = (2 * t - a) / 2 := by ring
  have hb : t - b / 2 = (2 * t - b) / 2 := by ring
  rw [ha, hb, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]

theorem intervalLog_shift_scale (a b t : ℝ) :
    intervalLog ((1 + a) / 2) ((1 + b) / 2) t = intervalLog a b (2 * t - 1) := by
  unfold intervalLog
  congr 3
  have ha : t - (1 + a) / 2 = (2 * t - 1 - a) / 2 := by ring
  have hb : t - (1 + b) / 2 = (2 * t - 1 - b) / 2 := by ring
  rw [ha, hb, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]

theorem logVec_left (n : ℕ) (t : ℝ) : left (logVec (n + 1) t) = logVec n (2 * t) := by
  funext j
  change intervalLog _ _ t = _
  simp only [pow_succ]
  rw [div_mul_eq_div_div, div_mul_eq_div_div, intervalLog_scale]
  rfl

theorem logVec_right (n : ℕ) (t : ℝ) : right (logVec (n + 1) t) = logVec n (2 * t - 1) := by
  funext j
  change intervalLog (((2 ^ n + (leafEquivFin n j).val : ℕ) : ℝ) / (2 ^ (n+1) : ℝ))
    ((((2 ^ n + (leafEquivFin n j).val : ℕ) : ℝ) + 1) / (2 ^ (n+1) : ℝ)) t = _
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  have hp : (2 : ℝ)^n ≠ 0 := by positivity
  have ha : ((2 : ℝ)^n + (leafEquivFin n j).val) / (2^n * 2) =
      (1 + (leafEquivFin n j).val / 2^n) / 2 := by field_simp
  have hb : ((2 : ℝ)^n + (leafEquivFin n j).val + 1) / (2^n * 2) =
      (1 + ((leafEquivFin n j).val + 1) / 2^n) / 2 := by field_simp; ring
  rw [ha, hb, intervalLog_shift_scale]
  rfl

variable {𝕜 : Type*} [RCLike 𝕜]

def fromL1 (n : ℕ) : L1Vec 𝕜 n →L[𝕜] Vec 𝕜 n :=
  (WithLp.linearEquiv 1 𝕜 (Vec 𝕜 n)).toLinearMap.toContinuousLinearMap

@[simp] theorem fromL1_apply (n : ℕ) (x : L1Vec 𝕜 n) : fromL1 n x = WithLp.ofLp x := rfl

theorem uniformRaw_integrable (n : ℕ) :
    Integrable (fun t => fromL1 (𝕜 := 𝕜) n (uniformStep n t)) volume :=
  (fromL1 (𝕜 := 𝕜) n).integrable_comp
    (memLp_one_iff_integrable.mp (uniformStep_memLp (𝕜 := 𝕜) n 1))

def sumCLM (n : ℕ) : Vec 𝕜 n →L[𝕜] 𝕜 :=
  ∑ j : Leaf n, ContinuousLinearMap.proj j

@[simp] theorem sumCLM_apply (n : ℕ) (x : Vec 𝕜 n) : sumCLM n x = total x := by
  simp [sumCLM, total]

theorem isHilbertPVAe_pi {n : ℕ} {f g : ℝ → Vec 𝕜 n}
    (hf : Integrable f volume) (hg : ∀ j, IsHilbertPVAe (fun t => f t j) (fun t => g t j)) :
    IsHilbertPVAe f g := by
  filter_upwards [ae_all_iff.mpr hg] with t ht
  apply tendsto_pi_nhds.mpr
  intro j
  apply (ht j).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hilbertTrunc_map
    ((ContinuousLinearMap.proj j : Vec 𝕜 n →L[𝕜] 𝕜).restrictScalars ℝ) hf hε t

theorem logVec_pv (n : ℕ) :
    IsHilbertPVAe (fun t => fromL1 (𝕜 := 𝕜) n (uniformStep n t))
      (fun t j => ((logVec n t j : ℝ) : 𝕜)) := by
  apply isHilbertPVAe_pi
  · exact uniformRaw_integrable n
  · intro j
    simpa only [fromL1_apply,
      logVec, intervalLog, uniformStep, uniformCell, Nat.cast_pow, Nat.cast_ofNat] using
      interval_hilbert_pv 𝕜 ((leafEquivFin n j).val / (2 ^ n : ℝ))
        (((leafEquivFin n j).val + 1) / (2 ^ n : ℝ))
        ((div_lt_div_iff_of_pos_right (by positivity)).mpr (by linarith))

theorem total_uniformStep (n : ℕ) (t : ℝ) :
    total (fromL1 n (uniformStep (𝕜 := 𝕜) n t)) =
      (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜)) t := by
  by_cases ht : t ∈ Set.Ico (0 : ℝ) 1
  · obtain ⟨j, hj, _⟩ := uniformStep_inside (𝕜 := 𝕜) n t ht
    rw [hj, Set.indicator_of_mem ht]
    exact total_basisVec j
  · rw [uniformStep_outside n t ht, map_zero, total_zero, Set.indicator_of_notMem ht]

theorem total_logVec (n : ℕ) :
    (fun t => total (logVec n t)) =ᵐ[volume] intervalLog 0 1 := by
  change (fun t => total (logVec n t)) =ᵐ[volume] (fun t => intervalLog 0 1 t)
  have hf := uniformRaw_integrable (𝕜 := ℝ) n
  have h := (logVec_pv (𝕜 := ℝ) n).map hf (sumCLM n)
  simp only [sumCLM_apply, RCLike.ofReal_real_eq_id, id_eq] at h
  simp_rw [total_uniformStep] at h
  simpa only [intervalLog, RCLike.ofReal_real_eq_id, id_eq] using
    h.unique (interval_hilbert_pv ℝ 0 1 (by norm_num))

theorem signed_pv_eq (n : ℕ) {g : ℝ → Vec 𝕜 n}
    (hg : IsHilbertPVAe (fun t => signedDyadicOperator n (uniformStep n t)) g) :
    g =ᵐ[volume] (fun t => signedDyadic n (fun j => ((logVec n t j : ℝ) : 𝕜))) := by
  let D : Vec 𝕜 n →L[𝕜] Vec 𝕜 n := (signedDyadicLinear n).toContinuousLinearMap
  have hf := uniformRaw_integrable (𝕜 := 𝕜) n
  exact hg.unique ((logVec_pv n).map hf (D.restrictScalars ℝ))

theorem intervalLog_unit (t : ℝ) : intervalLog 0 1 t = BinaryLogit.g t := by
  unfold intervalLog BinaryLogit.g
  rw [Real.log_abs, sub_zero]
  have ht : t / (t - 1) = -(t / (1 - t)) := by
    rw [show t - 1 = -(1-t) by ring, div_neg]
  rw [ht, Real.log_neg_eq_log, div_eq_mul_inv, mul_comm]

theorem ae_comp_tau {P : ℝ → Prop} (h : ∀ᵐ t : ℝ ∂volume, P t) :
    ∀ᵐ t : ℝ ∂volume, P (BinaryLogit.tau t) := by
  have hmul : Measure.QuasiMeasurePreserving (fun t : ℝ => 2*t) volume volume :=
    Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (by norm_num : (2 : ℝ) ≠ 0)
  have hshift : Measure.QuasiMeasurePreserving (fun t : ℝ => 2*t-1) volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-1)).quasiMeasurePreserving.comp hmul
  filter_upwards [hmul.ae h, hshift.ae h] with t hl hr
  by_cases ht : t < 1/2 <;> simp only [BinaryLogit.tau, ht, if_true, if_false] <;> assumption

def selected : (n : ℕ) → ℝ → Leaf n
  | 0, _ => 0
  | n + 1, t => if t < 1/2 then Sum.inl (selected n (2*t)) else Sum.inr (selected n (2*t-1))

def rowValue (n : ℕ) (t : ℝ) : ℝ := signedDyadic n (logVec n t) (selected n t)

theorem rowValue_zero (t : ℝ) : rowValue 0 t = BinaryLogit.g t := by
  simp only [rowValue, selected, signedDyadic, logVec, leafEquivFin, Equiv.refl_apply,
    Fin.val_zero, Nat.cast_zero, pow_zero, zero_add, div_one]
  exact intervalLog_unit t

theorem rowValue_succ (n : ℕ) (t : ℝ)
    (hp : total (logVec (n+1) t) = BinaryLogit.g t)
    (hc : total (logVec n (BinaryLogit.tau t)) = BinaryLogit.g (BinaryLogit.tau t)) :
    rowValue (n+1) t = rowValue n (BinaryLogit.tau t) +
      (-1 : ℝ)^(n+1) * (BinaryLogit.g t - BinaryLogit.g (BinaryLogit.tau t)) := by
  rw [total_succ, logVec_left, logVec_right] at hp
  by_cases ht : t < 1/2
  · simp only [BinaryLogit.tau, ht, if_true] at hc ⊢
    rw [rowValue, selected, if_pos ht]
    change signedDyadic n (left (logVec (n+1) t)) (selected n (2*t)) +
      (-1 : ℝ)^(n+1) * total (right (logVec (n+1) t)) = _
    rw [logVec_left, logVec_right]
    unfold rowValue
    rw [show total (logVec n (2*t-1)) = BinaryLogit.g t - BinaryLogit.g (2*t) by linarith]
  · simp only [BinaryLogit.tau, ht, if_false] at hc ⊢
    rw [rowValue, selected, if_neg ht]
    change (-1 : ℝ)^(n+1) * total (left (logVec (n+1) t)) +
      signedDyadic n (right (logVec (n+1) t)) (selected n (2*t-1)) = _
    rw [logVec_left, logVec_right]
    unfold rowValue
    rw [show total (logVec n (2*t)) = BinaryLogit.g t - BinaryLogit.g (2*t-1) by linarith]
    ring

theorem rowValue_eq_G (n : ℕ) : rowValue n =ᵐ[volume] BinaryLogit.G n := by
  induction n with
  | zero => exact Eventually.of_forall rowValue_zero
  | succ n ih =>
    have hp : (fun t => total (logVec (n+1) t)) =ᵐ[volume] BinaryLogit.g := by
      exact (total_logVec (n+1)).trans (Eventually.of_forall intervalLog_unit)
    have hc : (fun t => total (logVec n (BinaryLogit.tau t))) =ᵐ[volume]
        (fun t => BinaryLogit.g (BinaryLogit.tau t)) := by
      exact ae_comp_tau (P := fun t => total (logVec n t) = BinaryLogit.g t)
        ((total_logVec n).trans (Eventually.of_forall intervalLog_unit))
    filter_upwards [hp, hc, ae_comp_tau ih] with t hp hc hi
    rw [rowValue_succ n t hp hc, hi, BinaryLogit.G_succ]

theorem signedDyadic_cast (n : ℕ) (x : Vec ℝ n) :
    signedDyadic n (fun j => ((x j : ℝ) : 𝕜)) = fun j => ((signedDyadic (𝕜 := ℝ) n x j : ℝ) : 𝕜) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext j
    rcases j with j | j
    · change signedDyadic n (fun j => (((left x) j : ℝ) : 𝕜)) j +
        (-1 : 𝕜)^(n+1) * total (fun j => (((right x) j : ℝ) : 𝕜)) = _
      rw [ih]
      simp [signedDyadic, total, left, right]
    · change (-1 : 𝕜)^(n+1) * total (fun j => (((left x) j : ℝ) : 𝕜)) +
        signedDyadic n (fun j => (((right x) j : ℝ) : 𝕜)) j = _
      rw [ih]
      simp [signedDyadic, total, left, right]

theorem signed_pv_selected (n : ℕ) {g : ℝ → Vec 𝕜 n}
    (hg : IsHilbertPVAe (fun t => signedDyadicOperator n (uniformStep n t)) g) :
    (fun t => g t (selected n t)) =ᵐ[volume] (fun t => ((BinaryLogit.G n t : ℝ) : 𝕜)) := by
  filter_upwards [signed_pv_eq n hg, rowValue_eq_G n] with t ht hg
  rw [ht, signedDyadic_cast]
  change ((rowValue n t : ℝ) : 𝕜) = _
  rw [hg]

theorem G_norm_le_output (n : ℕ) {g : ℝ → Vec 𝕜 n}
    (hg : IsHilbertPVAe (fun t => signedDyadicOperator n (uniformStep n t)) g) :
    eLpNorm (BinaryLogit.G n) 2 BinaryLogit.unitMeasure ≤ eLpNorm g 2 volume := by
  calc
    _ ≤ eLpNorm g 2 BinaryLogit.unitMeasure := by
      apply eLpNorm_mono_ae
      filter_upwards [ae_restrict_of_ae (signed_pv_selected n hg)] with t ht
      have h := norm_le_pi_norm (g t) (selected n t)
      rw [ht, RCLike.norm_ofReal] at h
      simpa only [Real.norm_eq_abs] using h
    _ ≤ _ := eLpNorm_mono_measure g Measure.restrict_le_self

end SignedDyadicPV

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Every defining smooth-test bound also bounds the actual logarithmic
diagonal of the step witness, with no loss of constant. -/
theorem signedDyadic_G_norm_le_HilbertBound (n : ℕ) {C : ℝ≥0}
    (hC : HilbertBound 2 (signedDyadicOperator (𝕜 := 𝕜) n) C) :
    eLpNorm (BinaryLogit.G n) 2 BinaryLogit.unitMeasure ≤ (C : ℝ≥0∞) := by
  obtain ⟨g, hpv, _, hgn⟩ := Interfaces.HilbertBound.l2_pv_extension hC
    (uniformStep n) (uniformStep_memLp n 2)
  rw [eLpNorm_uniformStep_two, mul_one] at hgn
  exact (SignedDyadicPV.G_norm_le_output n hpv).trans hgn

theorem signedDyadic_G_norm_le_hilbertConstant (n : ℕ) :
    eLpNorm (BinaryLogit.G n) 2 BinaryLogit.unitMeasure ≤
      hilbertConstant 2 (signedDyadicOperator (𝕜 := 𝕜) n) :=
  le_hilbertConstant fun _ hC => signedDyadic_G_norm_le_HilbertBound n hC

theorem ySpace_G_norm_le_hilbertConstant (n : ℕ)
    [NormedSpace ℝ (YSpace 𝕜 n)] [IsScalarTower ℝ 𝕜 (YSpace 𝕜 n)] :
    eLpNorm (BinaryLogit.G n) 2 BinaryLogit.unitMeasure ≤
      hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) := by
  exact (signedDyadic_G_norm_le_hilbertConstant (𝕜 := 𝕜) n).trans
    (hilbertConstant_matrix_le_graphSpace (signedDyadic_transferAssumptions n)
      (signedDyadic_le_l1 n) 2)

end HilbertUMD
