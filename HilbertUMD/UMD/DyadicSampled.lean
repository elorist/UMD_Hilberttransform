import HilbertUMD.UMD.DyadicTerminal

/-! Dyadic terminal bounds with suppressed and grouped levels. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace HilbertUMD

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem leafL2Norm_sum_zero_or_unit {ι : Type*} [Fintype ι]
    (d : ℕ) (v : ι → Leaf d → F) (B : ℝ)
    (h : ∀ ε : ι → 𝕜, (∀ k, ‖ε k‖ = 1) →
      leafL2Norm d (∑ k, ε k • v k) ≤ B)
    (ε : ι → 𝕜) (hε : ∀ k, ε k = 0 ∨ ‖ε k‖ = 1) :
    leafL2Norm d (∑ k, ε k • v k) ≤ B := by
  classical
  have extend (s : Finset ι) : ∀ ε : ι → 𝕜,
      (∀ k, ε k = 0 ∨ ‖ε k‖ = 1) → (∀ k, k ∉ s → ‖ε k‖ = 1) →
      leafL2Norm d (∑ k, ε k • v k) ≤ B := by
    induction s using Finset.induction_on with
    | empty =>
      intro ε _ he
      exact h ε (fun k => he k (by simp))
    | @insert a s ha ih =>
      intro ε he hout
      by_cases hz : ε a = 0
      · let ep := Function.update ε a 1
        let em := Function.update ε a (-1)
        have hep : leafL2Norm d (∑ k, ep k • v k) ≤ B := by
          apply ih ep
          · intro k
            by_cases hk : k = a
            · subst k; simp [ep]
            · simpa [ep, Function.update_of_ne hk] using he k
          · intro k hk
            by_cases hka : k = a
            · subst k; simp [ep]
            · simpa [ep, Function.update_of_ne hka] using hout k (by simp [hka, hk])
        have hem : leafL2Norm d (∑ k, em k • v k) ≤ B := by
          apply ih em
          · intro k
            by_cases hk : k = a
            · subst k; simp [em]
            · simpa [em, Function.update_of_ne hk] using he k
          · intro k hk
            by_cases hka : k = a
            · subst k; simp [em]
            · simpa [em, Function.update_of_ne hka] using hout k (by simp [hka, hk])
        have hid : (∑ k, ep k • v k) + (∑ k, em k • v k) =
            (2 : 𝕜) • (∑ k, ε k • v k) := by
          rw [← Finset.sum_add_distrib, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : k = a
          · subst k; simp [ep, em, hz]
          · simp [ep, em, Function.update_of_ne hk, two_smul]
        have htri := leafL2Norm_add_le (𝕜 := 𝕜) d (∑ k, ep k • v k) (∑ k, em k • v k)
        rw [hid, leafL2Norm_smul] at htri
        norm_num at htri
        linarith
      · apply ih ε he
        intro k hk
        by_cases hka : k = a
        · subst k; exact (he a).resolve_left hz
        · exact hout k (by simp [hka, hk])
  exact extend Finset.univ ε hε (by simp)

/-- Unused binary levels may have coefficient zero, with the original constant. -/
theorem FiniteDyadicTerminalBound.zero_or_unit
    {T : E →L[𝕜] F} {C : ℝ≥0} (h : FiniteDyadicTerminalBound 2 T C)
    (d : ℕ) (f : Leaf d → E) (ε : Fin d → 𝕜)
    (hε : ∀ k, ε k = 0 ∨ ‖ε k‖ = 1) :
    leafL2Norm d (martingaleTransform T ε
      (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val f)) ≤
        (C : ℝ) * leafL2Norm d f := by
  let v : Fin d → Leaf d → F := fun k i =>
    T (leafAverage (𝕜 := 𝕜) d k.succ.val f i -
      leafAverage (𝕜 := 𝕜) d k.castSucc.val f i)
  have he (a : Fin d → 𝕜) : (∑ k, a k • v k) = martingaleTransform T a
      (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val f) := by
    ext i
    simp [martingaleTransform, v]
  rw [← he ε]
  apply leafL2Norm_sum_zero_or_unit d v _ _ ε hε
  intro a ha
  rw [he]
  exact (finiteDyadicTerminalBound_two_iff T C).mp h d f a ha

namespace DyadicSampling

def coefficients {m : ℕ} (r : Fin (m + 1) → ℕ) (ε : Fin m → 𝕜) (j : ℕ) : 𝕜 :=
  ∑ k : Fin m, if r k.castSucc ≤ j ∧ j < r k.succ then ε k else 0

theorem coefficients_zero_or_unit {m : ℕ} (r : Fin (m + 1) → ℕ)
    (hr : Monotone r) (ε : Fin m → 𝕜) (hε : ∀ k, ‖ε k‖ = 1) (j : ℕ) :
    coefficients r ε j = 0 ∨ ‖coefficients r ε j‖ = 1 := by
  classical
  by_cases hx : ∃ k : Fin m, r k.castSucc ≤ j ∧ j < r k.succ
  · obtain ⟨k, hk⟩ := hx
    have hunique : ∀ l : Fin m, r l.castSucc ≤ j ∧ j < r l.succ → l = k := by
      intro l hl
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := hr (show l.succ ≤ k.castSucc by change l.val + 1 ≤ k.val; omega)
        omega
      · have h := hr (show k.succ ≤ l.castSucc by change k.val + 1 ≤ l.val; omega)
        omega
    right
    have heq : coefficients r ε j = ε k := by
      unfold coefficients
      rw [Finset.sum_eq_single k]
      · simp [hk]
      · intro l _ hl
        exact if_neg (fun h => hl (hunique l h))
      · simp
    rw [heq]
    exact hε k
  · left
    apply Finset.sum_eq_zero
    intro k _
    exact if_neg (fun hk => hx ⟨k, hk⟩)

theorem sum_coefficients {m d : ℕ} (r : Fin (m + 1) → ℕ)
    (hr : Monotone r) (hd : ∀ k, r k ≤ d) (ε : Fin m → 𝕜) (v : ℕ → F) :
    (∑ j : Fin d, coefficients r ε j.val • (v (j.val + 1) - v j.val)) =
      ∑ k : Fin m, ε k • (v (r k.succ) - v (r k.castSucc)) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun j => coefficients r ε j • (v (j + 1) - v j)) d]
  simp only [coefficients, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ite_smul, zero_smul]
  rw [← Finset.sum_filter]
  have hset : (Finset.range d).filter (fun j => r k.castSucc ≤ j ∧ j < r k.succ) =
      Finset.Ico (r k.castSucc) (r k.succ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have h := hd k.succ
    omega
  rw [hset, ← Finset.smul_sum, Finset.sum_Ico_sub v (hr (by change k.val ≤ k.val + 1; omega))]

theorem transform_sampled {m d : ℕ} (r : Fin (m + 1) → ℕ)
    (hr : Monotone r) (hd : ∀ k, r k ≤ d) (ε : Fin m → 𝕜)
    (T : E →L[𝕜] F) (f : Leaf d → E) :
    martingaleTransform T (fun j : Fin d => coefficients r ε j.val)
      (fun k : Fin (d + 1) => leafAverage (𝕜 := 𝕜) d k.val f) =
    martingaleTransform T ε (fun k => leafAverage (𝕜 := 𝕜) d (r k) f) := by
  ext i
  simpa only [martingaleTransform, Fin.val_succ, Fin.val_castSucc, map_sub] using
    sum_coefficients r hr hd ε (fun j => T (leafAverage (𝕜 := 𝕜) d j f i))

end DyadicSampling

/-- Test any increasing sequence of levels of a uniform binary tree, allowing
initial and terminal auxiliary levels outside that sequence. -/
def FiniteDyadicSampledTerminalBound (T : E →L[𝕜] F) (C : ℝ≥0) : Prop :=
  ∀ (d m : ℕ) (r : Fin (m + 1) → ℕ), Monotone r → (∀ k, r k ≤ d) →
  ∀ (f : Leaf d → E) (ε : Fin m → 𝕜), (∀ k, ‖ε k‖ = 1) →
    eLpNorm (martingaleTransform T ε (fun k => leafAverage (𝕜 := 𝕜) d (r k) f))
      2 (leafUniform d) ≤ (C : ℝ≥0∞) * eLpNorm f 2 (leafUniform d)

/-- Group consecutive binary levels and suppress levels outside the selected
time range. The original dyadic constant is retained. -/
theorem FiniteDyadicTerminalBound.sampled
    {T : E →L[𝕜] F} {C : ℝ≥0} (h : FiniteDyadicTerminalBound 2 T C) :
    FiniteDyadicSampledTerminalBound T C := by
  intro d m r hr hd f ε hε
  have hb := h.zero_or_unit d f (fun j : Fin d => DyadicSampling.coefficients r ε j.val)
    (fun j => DyadicSampling.coefficients_zero_or_unit r hr ε hε j.val)
  rw [DyadicSampling.transform_sampled r hr hd] at hb
  simpa only [eLpNorm_leafUniform_two, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul C.coe_nonneg] using ENNReal.ofReal_le_ofReal hb

end HilbertUMD
