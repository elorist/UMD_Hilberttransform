import HilbertUMD.Interfaces.HilbertInterval
import HilbertUMD.LowerBounds.SummationGeometry
import HilbertUMD.LowerBounds.HilbertLowerGeometry
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! The manuscript's interval-step witness for the summation Hilbert lower bound. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace HilbertUMD

variable {𝕜 : Type*} [RCLike 𝕜]

def uniformCell (n : ℕ) (j : Leaf n) : Set ℝ :=
  Set.Ico (((leafEquivFin n j).val : ℝ) / (2 ^ n : ℕ))
    ((((leafEquivFin n j).val : ℝ) + 1) / (2 ^ n : ℕ))

def uniformStep (n : ℕ) (t : ℝ) : L1Vec 𝕜 n :=
  WithLp.toLp 1 (fun j => (uniformCell n j).indicator (fun _ => (1 : 𝕜)) t)

theorem uniformStep_memLp (n : ℕ) (p : ℝ≥0∞) : MemLp (uniformStep (𝕜 := 𝕜) n) p volume := by
  apply MemLp.of_eval_piLp
  intro j
  exact memLp_indicator_const p measurableSet_Ico 1 (Or.inr (by simp))

theorem uniformCell_subset_unit (n : ℕ) (j : Leaf n) :
    uniformCell n j ⊆ Set.Ico (0 : ℝ) 1 := by
  intro t ht
  have hN : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have hj : ((leafEquivFin n j).val : ℝ) + 1 ≤ (2 ^ n : ℕ) := by
    exact_mod_cast (leafEquivFin n j).isLt
  refine ⟨(div_nonneg (Nat.cast_nonneg _) hN.le).trans ht.1, ?_⟩
  exact ht.2.trans_le ((div_le_one hN).mpr hj)

theorem uniformStep_outside (n : ℕ) (t : ℝ) (ht : t ∉ Set.Ico (0 : ℝ) 1) :
    uniformStep (𝕜 := 𝕜) n t = 0 := by
  apply PiLp.ext
  intro j
  change (uniformCell n j).indicator (fun _ => (1 : 𝕜)) t = 0
  exact Set.indicator_of_notMem (fun hj => ht (uniformCell_subset_unit n j hj)) _

theorem uniformStep_inside (n : ℕ) (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ∃ j : Leaf n, uniformStep (𝕜 := 𝕜) n t = WithLp.toLp 1 (basisVec j) ∧
      (leafEquivFin n j).val = ⌊((2 ^ n : ℕ) : ℝ) * t⌋₊ := by
  let i : Fin (2 ^ n) := ⟨⌊((2 ^ n : ℕ) : ℝ) * t⌋₊,
    floor_mul_lt_of_unit_interval (2 ^ n) (by positivity) t ht⟩
  let j := (leafEquivFin n).symm i
  refine ⟨j, ?_, by simp [j, i]⟩
  apply PiLp.ext
  intro k
  have hk : t ∈ uniformCell n k ↔ k = j := by
    rw [uniformCell, Set.mem_Ico,
      uniform_cell_iff_floor_eq (2 ^ n) (by positivity) _ t ht.1]
    change i.val = (leafEquivFin n k).val ↔ k = (leafEquivFin n).symm i
    rw [← Fin.ext_iff, eq_comm, Equiv.eq_symm_apply]
  change (uniformCell n k).indicator (fun _ => (1 : 𝕜)) t = basisVec j k
  simp [Set.indicator, basisVec, hk]

theorem norm_uniformStep (n : ℕ) (t : ℝ) :
    ‖uniformStep (𝕜 := 𝕜) n t‖ = (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t := by
  by_cases ht : t ∈ Set.Ico (0 : ℝ) 1
  · obtain ⟨j, hj, _⟩ := uniformStep_inside (𝕜 := 𝕜) n t ht
    rw [hj, Set.indicator_of_mem ht]
    rw [PiLp.norm_eq_of_L1]
    change (∑ k, ‖(basisVec j : Vec 𝕜 n) k‖) = 1
    exact l1Norm_basisVec j
  · rw [uniformStep_outside n t ht, norm_zero, Set.indicator_of_notMem ht]

theorem eLpNorm_uniformStep_two (n : ℕ) :
    eLpNorm (uniformStep (𝕜 := 𝕜) n) 2 volume = 1 := by
  rw [eLpNorm_congr_norm_ae (g := (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)))
    (Eventually.of_forall fun t => by
      rw [norm_uniformStep]
      simp only [Set.indicator]
      split_ifs <;> norm_num)]
  simp [eLpNorm_indicator_const, measurableSet_Ico]

theorem summation_uniformStep (n : ℕ) (i : Leaf n) (t : ℝ) :
    summationOperator (𝕜 := 𝕜) n (uniformStep n t) i =
      (Set.Ico (0 : ℝ) ((((leafEquivFin n i).val : ℝ) + 1) / (2 ^ n : ℕ))).indicator
        (fun _ => (1 : 𝕜)) t := by
  have hN : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have hiN : ((leafEquivFin n i).val : ℝ) + 1 ≤ (2 ^ n : ℕ) := by
    exact_mod_cast (leafEquivFin n i).isLt
  by_cases ht : t ∈ Set.Ico (0 : ℝ) 1
  · obtain ⟨j, hj, hjidx⟩ := uniformStep_inside (𝕜 := 𝕜) n t ht
    change summation n (WithLp.ofLp (uniformStep n t)) i = _
    rw [hj]
    change summation n (basisVec j : Vec 𝕜 n) i = _
    rw [summation_basisVec_entry]
    have hiff : (leafEquivFin n j).val ≤ (leafEquivFin n i).val ↔
        t < (((leafEquivFin n i).val : ℝ) + 1) / (2 ^ n : ℕ) := by
      rw [hjidx]
      calc
        ⌊((2 ^ n : ℕ) : ℝ) * t⌋₊ ≤ (leafEquivFin n i).val ↔
            ⌊((2 ^ n : ℕ) : ℝ) * t⌋₊ < (leafEquivFin n i).val + 1 := by omega
        _ ↔ ((2 ^ n : ℕ) : ℝ) * t < (((leafEquivFin n i).val + 1 : ℕ) : ℝ) :=
          Nat.floor_lt (mul_nonneg hN.le ht.1)
        _ ↔ _ := by rw [Nat.cast_add, Nat.cast_one, lt_div_iff₀ hN, mul_comm]
    simp [Set.indicator, ht.1, hiff]
  · rw [uniformStep_outside n t ht, map_zero]
    have hout : t ∉ Set.Ico (0 : ℝ)
        ((((leafEquivFin n i).val : ℝ) + 1) / (2 ^ n : ℕ)) := by
      intro hin
      exact ht ⟨hin.1, hin.2.trans_le ((div_le_one hN).mpr hiN)⟩
    exact (Set.indicator_of_notMem hout _).symm

theorem summation_pv_coordinate (n : ℕ) {g : ℝ → Vec 𝕜 n}
    (hg : IsHilbertPVAe (fun t => summationOperator n (uniformStep n t)) g) (i : Leaf n) :
    (fun t => g t i) =ᵐ[volume]
      (fun t => ((Real.log |t / (t - (((leafEquivFin n i).val : ℝ) + 1) /
        (2 ^ n : ℕ))| / Real.pi : ℝ) : 𝕜)) := by
  let P : Vec 𝕜 n →L[ℝ] 𝕜 :=
    (ContinuousLinearMap.proj i : Vec 𝕜 n →L[𝕜] 𝕜).restrictScalars ℝ
  have hf : Integrable (fun t => summationOperator (𝕜 := 𝕜) n (uniformStep n t)) volume :=
    (summationOperator (𝕜 := 𝕜) n).integrable_comp
      (memLp_one_iff_integrable.mp (uniformStep_memLp (𝕜 := 𝕜) n 1))
  have hpv := hg.map hf P
  change IsHilbertPVAe (fun t => summationOperator n (uniformStep n t) i) (fun t => g t i) at hpv
  have heq := funext (summation_uniformStep (𝕜 := 𝕜) n i)
  rw [heq] at hpv
  have hi : (0 : ℝ) < (((leafEquivFin n i).val : ℝ) + 1) / (2 ^ n : ℕ) := by positivity
  simpa only [sub_zero] using hpv.unique (Interfaces.interval_hilbert_pv 𝕜 0 _ hi)

theorem summation_pv_middle_lower (n : ℕ) (hn : 3 ≤ n) {g : ℝ → Vec 𝕜 n}
    (hg : IsHilbertPVAe (fun t => summationOperator n (uniformStep n t)) g) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) →
      Real.log ((2 ^ n : ℕ) / (4 : ℝ)) / Real.pi ≤ ‖g t‖ := by
  have hN : 8 ≤ 2 ^ n := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hc : ∀ᵐ t : ℝ ∂volume, ∀ i : Leaf n,
      g t i = ((Real.log |t / (t - (((leafEquivFin n i).val : ℝ) + 1) /
        (2 ^ n : ℕ))| / Real.pi : ℝ) : 𝕜) :=
    ae_all_iff.mpr (fun i => summation_pv_coordinate n hg i)
  filter_upwards [hc, ae_ne_uniform_endpoint (2 ^ n)] with t hc hgrid ht
  obtain ⟨i, hi1, hiN, hlog⟩ := exists_logarithmic_row (2 ^ n) hN t ht hgrid
  let k : Leaf n := (leafEquivFin n).symm ⟨i - 1, by omega⟩
  have hk : (leafEquivFin n k).val + 1 = i := by
    simp only [k, Equiv.apply_symm_apply]
    omega
  have he : (((leafEquivFin n k).val : ℝ) + 1) / (2 ^ n : ℕ) =
      (i : ℝ) / (2 ^ n : ℕ) := by
    congr 1
    exact_mod_cast hk
  calc
    Real.log ((2 ^ n : ℕ) / (4 : ℝ)) / Real.pi
        ≤ Real.log (t / (t - (i : ℝ) / (2 ^ n : ℕ))) / Real.pi :=
      div_le_div_of_nonneg_right hlog Real.pi_pos.le
    _ ≤ ‖g t k‖ := by
      rw [hc k, he, RCLike.norm_ofReal, Real.log_abs]
      exact le_abs_self _
    _ ≤ ‖g t‖ := norm_le_pi_norm _ _

/-- Integration over the middle half gives a linear-logarithmic lower bound.
The factor `√2` is the exact L² cost of the middle-half interval used here;
the fixed paper uses a larger interval in its numerical proof. -/
theorem summation_HilbertBound_log_lower (n : ℕ) (hn : 3 ≤ n) {C : ℝ≥0}
    (hC : HilbertBound 2 (summationOperator (𝕜 := 𝕜) n) C) :
    Real.log ((2 : ℝ) ^ n / 4) / (Real.sqrt 2 * Real.pi) ≤ C := by
  obtain ⟨g, hpv, hgp, hgn⟩ := Interfaces.HilbertBound.l2_pv_extension hC
    (uniformStep n) (uniformStep_memLp n 2)
  rw [eLpNorm_uniformStep_two, mul_one] at hgn
  let K : ℝ := Real.log ((2 : ℝ) ^ n / 4) / Real.pi
  have hK : 0 ≤ K := by
    apply div_nonneg _ Real.pi_pos.le
    apply Real.log_nonneg
    have hpow : (4 : ℝ) ≤ 2 ^ n := by
      calc
        4 = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hm := summation_pv_middle_lower n hn hpv
  have hdom : eLpNorm ((Set.Icc (1 / 4 : ℝ) (3 / 4)).indicator (fun _ => K)) 2 volume
      ≤ eLpNorm g 2 volume := by
    apply eLpNorm_mono_ae
    filter_upwards [hm] with t ht
    by_cases hs : t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4)
    · rw [Set.indicator_of_mem hs, Real.norm_eq_abs, abs_of_nonneg hK]
      simpa only [K, Nat.cast_pow, Nat.cast_ofNat] using ht hs
    · rw [Set.indicator_of_notMem hs, norm_zero]
      exact norm_nonneg _
  have hhalf : ENNReal.ofReal (1 / Real.sqrt 2) =
      (1 / 2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
    have hs : (1 / Real.sqrt 2 : ℝ) = (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num), Real.sqrt_one]
    rw [hs, ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
    rw [ENNReal.ofReal_div_of_pos (x := 1) (y := 2) (by norm_num)]
    norm_num
  have hki : ENNReal.ofReal (K / Real.sqrt 2) ≤ (C : ℝ≥0∞) := by
    calc
      ENNReal.ofReal (K / Real.sqrt 2) =
          ENNReal.ofReal K * ENNReal.ofReal (1 / Real.sqrt 2) := by
        rw [← ENNReal.ofReal_mul hK]
        congr 1
        ring
      _ = ENNReal.ofReal K * (1 / 2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by rw [hhalf]
      _ = eLpNorm ((Set.Icc (1 / 4 : ℝ) (3 / 4)).indicator (fun _ => K)) 2 volume := by
        rw [eLpNorm_indicator_const measurableSet_Icc (by norm_num) (by norm_num)]
        norm_num [Real.enorm_eq_ofReal_abs, abs_of_nonneg hK]
        rw [ENNReal.ofReal_div_of_pos (x := 1) (y := 2) (by norm_num)]
        norm_num
      _ ≤ C := hdom.trans hgn
  have hr : K / Real.sqrt 2 ≤ (C : ℝ) := (ENNReal.ofReal_le_coe).mp hki
  simpa [K, div_div, mul_comm] using hr

/-- The final row already gives a fixed positive lower bound at every depth. -/
theorem summation_pv_far_lower (n : ℕ) {g : ℝ → Vec 𝕜 n}
    (hg : IsHilbertPVAe (fun t => summationOperator n (uniformStep n t)) g) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Set.Icc (2 : ℝ) 3 →
      Real.log (3 / 2 : ℝ) / Real.pi ≤ ‖g t‖ := by
  have hN : 0 < 2 ^ n := by positivity
  let k : Leaf n := (leafEquivFin n).symm ⟨2 ^ n - 1, by omega⟩
  have hk : (leafEquivFin n k).val + 1 = 2 ^ n := by
    simp only [k, Equiv.apply_symm_apply]
    omega
  have he : (((leafEquivFin n k).val : ℝ) + 1) / (2 ^ n : ℕ) = 1 := by
    have he' : ((leafEquivFin n k).val : ℝ) + 1 = (2 ^ n : ℕ) := by exact_mod_cast hk
    rw [he', div_self (by positivity)]
  filter_upwards [summation_pv_coordinate n hg k] with t ht hs
  have hd : 0 < t - 1 := by linarith [hs.1]
  have hl : Real.log (3 / 2 : ℝ) ≤ Real.log (t / (t - 1)) := by
    apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ hd).mpr
    linarith [hs.2]
  calc
    Real.log (3 / 2 : ℝ) / Real.pi ≤ Real.log (t / (t - 1)) / Real.pi :=
      div_le_div_of_nonneg_right hl Real.pi_pos.le
    _ ≤ ‖g t k‖ := by
      rw [ht, he, RCLike.norm_ofReal, Real.log_abs]
      exact le_abs_self _
    _ ≤ ‖g t‖ := norm_le_pi_norm _ _

theorem summation_HilbertBound_uniform_lower (n : ℕ) {C : ℝ≥0}
    (hC : HilbertBound 2 (summationOperator (𝕜 := 𝕜) n) C) :
    Real.log (3 / 2 : ℝ) / Real.pi ≤ C := by
  obtain ⟨g, hpv, _, hgn⟩ := Interfaces.HilbertBound.l2_pv_extension hC
    (uniformStep n) (uniformStep_memLp n 2)
  rw [eLpNorm_uniformStep_two, mul_one] at hgn
  let K : ℝ := Real.log (3 / 2 : ℝ) / Real.pi
  have hK : 0 ≤ K := div_nonneg (Real.log_nonneg (by norm_num)) Real.pi_pos.le
  have hm := summation_pv_far_lower n hpv
  have hdom : eLpNorm ((Set.Icc (2 : ℝ) 3).indicator (fun _ => K)) 2 volume
      ≤ eLpNorm g 2 volume := by
    apply eLpNorm_mono_ae
    filter_upwards [hm] with t ht
    by_cases hs : t ∈ Set.Icc (2 : ℝ) 3
    · rw [Set.indicator_of_mem hs, Real.norm_eq_abs, abs_of_nonneg hK]
      exact ht hs
    · rw [Set.indicator_of_notMem hs, norm_zero]
      exact norm_nonneg _
  have hk : eLpNorm ((Set.Icc (2 : ℝ) 3).indicator (fun _ => K)) 2 volume =
      ENNReal.ofReal K := by
    rw [eLpNorm_indicator_const measurableSet_Icc (by norm_num) (by norm_num)]
    norm_num [Real.enorm_eq_ofReal_abs, abs_of_nonneg hK]
  rw [hk] at hdom
  exact ENNReal.ofReal_le_coe.mp (hdom.trans hgn)

/-- An explicit universal coefficient, with the shallow depths covered by the
last row and the remaining depths by the middle-half estimate. -/
def summationHilbertLowerConstant : ℝ :=
  min (Real.log 2 / (4 * Real.sqrt 2 * Real.pi)) (Real.log (3 / 2 : ℝ) / (3 * Real.pi))

theorem summationHilbertLowerConstant_pos : 0 < summationHilbertLowerConstant := by
  apply lt_min
  · exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  · exact div_pos (Real.log_pos (by norm_num)) (by positivity)

theorem summation_HilbertBound_linear_lower (n : ℕ) {C : ℝ≥0}
    (hC : HilbertBound 2 (summationOperator (𝕜 := 𝕜) n) C) :
    summationHilbertLowerConstant * ((n : ℝ) + 1) ≤ C := by
  have hn0 : 0 ≤ (n : ℝ) + 1 := by positivity
  by_cases hn : 3 ≤ n
  · have hlog := log_dyadic_quarter_linear_lower n hn
    have hbound := summation_HilbertBound_log_lower n hn hC
    calc
      summationHilbertLowerConstant * ((n : ℝ) + 1) ≤
          (Real.log 2 / (4 * Real.sqrt 2 * Real.pi)) * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hn0
      _ = ((((n : ℝ) + 1) / 4) * Real.log 2) / (Real.sqrt 2 * Real.pi) := by ring
      _ ≤ Real.log ((2 : ℝ) ^ n / 4) / (Real.sqrt 2 * Real.pi) :=
        div_le_div_of_nonneg_right hlog (by positivity)
      _ ≤ C := hbound
  · have hn3 : (n : ℝ) + 1 ≤ 3 := by exact_mod_cast (show n + 1 ≤ 3 by omega)
    calc
      summationHilbertLowerConstant * ((n : ℝ) + 1) ≤
          (Real.log (3 / 2 : ℝ) / (3 * Real.pi)) * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hn0
      _ ≤ (Real.log (3 / 2 : ℝ) / (3 * Real.pi)) * 3 :=
        mul_le_mul_of_nonneg_left hn3 (by positivity)
      _ = Real.log (3 / 2 : ℝ) / Real.pi := by ring
      _ ≤ C := summation_HilbertBound_uniform_lower n hC

theorem summation_hilbertConstant_lower (n : ℕ) :
    ENNReal.ofReal (summationHilbertLowerConstant * ((n : ℝ) + 1)) ≤
      hilbertConstant 2 (summationOperator (𝕜 := 𝕜) n) := by
  apply le_hilbertConstant
  intro C hC
  exact ENNReal.ofReal_le_coe.mpr (summation_HilbertBound_linear_lower n hC)

end HilbertUMD
