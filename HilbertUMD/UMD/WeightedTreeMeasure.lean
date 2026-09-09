import HilbertUMD.UMD.WeightedBinaryTree

/-! Representing finite laws by branching probabilities and identifying their
weighted conditional averages. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace HilbertUMD.WeightedTree

def combineBias {n : ℕ} (p : ℝ) (a b : Bias n) : Bias (n + 1) :=
  Sum.elim (fun _ => p) (Sum.elim a b)

theorem exists_bias_scaled (n : ℕ) (w : Leaf n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ b : Bias n, Valid b ∧ ∀ i, (∑ j, w j) * mass n b i = w i := by
  induction n with
  | zero =>
    refine ⟨fun i => PEmpty.elim i, (fun i => PEmpty.elim i), ?_⟩
    intro i
    simp only [mass, mul_one]
    rw [Fin.sum_univ_one]
    exact congrArg w (Subsingleton.elim _ _)
  | succ n ih =>
    obtain ⟨a, ha, hwa⟩ := ih (fun i => w (Sum.inl i)) (fun i => hw (Sum.inl i))
    obtain ⟨b, hb, hwb⟩ := ih (fun i => w (Sum.inr i)) (fun i => hw (Sum.inr i))
    let A : ℝ := ∑ i, w (Sum.inl i)
    let B : ℝ := ∑ i, w (Sum.inr i)
    let S : ℝ := A + B
    have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hw _)
    have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hw _)
    have hAS : A ≤ S := by dsimp [S]; linarith
    have hS : 0 ≤ S := add_nonneg hA hB
    have hp : 0 ≤ A / S ∧ A / S ≤ 1 := by
      refine ⟨div_nonneg hA hS, ?_⟩
      by_cases hz : S = 0
      · simp [hz]
      · exact (div_le_one (lt_of_le_of_ne hS (Ne.symm hz))).mpr hAS
    have he : S * (A / S) = A := by
      by_cases hz : S = 0
      · have hAz : A = 0 := by linarith
        simp [hz, hAz]
      · field_simp
    have he' : S * (1 - A / S) = B := by
      rw [mul_sub, mul_one, he]
      dsimp [S]
      ring
    refine ⟨combineBias (A / S) a b, ?_, ?_⟩
    · intro i
      rcases i with u | i
      · exact hp
      · rcases i with i | i
        · exact ha i
        · exact hb i
    · intro i
      rw [Fintype.sum_sum_type]
      change S * mass (n + 1) (combineBias (A / S) a b) i = w i
      cases i with
      | inl i =>
        change S * (A / S * mass n a i) = _
        rw [← mul_assoc, he]
        exact hwa i
      | inr i =>
        change S * ((1 - A / S) * mass n b i) = _
        rw [← mul_assoc, he']
        exact hwb i

theorem exists_bias_of_weights (n : ℕ) (w : Leaf n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    ∃ b : Bias n, Valid b ∧ ∀ i, mass n b i = w i := by
  obtain ⟨b, hb, h⟩ := exists_bias_scaled n w hw
  exact ⟨b, hb, fun i => by simpa [hs] using h i⟩

section Averages
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem average_const (n k : ℕ) (b : Bias n) (x : E) (i : Leaf n) :
    average n b k (fun _ => x) i = x := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => exact mean_const _ _ _
    | succ k => cases i <;> exact ih k _ _

theorem average_congr_on_block (n k : ℕ) (b : Bias n) (f g : Leaf n → E) (i : Leaf n)
    (h : ∀ j ∈ dyadicBlock n k i, f j = g j) :
    average n b k f i = average n b k g i := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact h 0 (by simp [dyadicBlock])
    | succ k => exact h i (mem_dyadicBlock_self _ _ _)
  | succ n ih =>
    cases k with
    | zero =>
      change mean _ _ _ = mean _ _ _
      simp only [mean_eq_sum]
      exact Finset.sum_congr rfl (fun j _ => congrArg _ (h j (by simp [dyadicBlock])))
    | succ k =>
      cases i with
      | inl i =>
        apply ih k
        intro j hj
        exact h (Sum.inl j) (Finset.mem_map.mpr ⟨j, hj, rfl⟩)
      | inr i =>
        apply ih k
        intro j hj
        exact h (Sum.inr j) (Finset.mem_map.mpr ⟨j, hj, rfl⟩)

theorem average_indicator (n k : ℕ) (b : Bias n) (f : Leaf n → E) (s : Set (Leaf n))
    (hs : MeasurableSet[dyadicMeasurableSpace n k] s) :
    average n b k (s.indicator f) = s.indicator (average n b k f) := by
  classical
  funext i
  by_cases hi : i ∈ s
  · rw [Set.indicator_of_mem hi]
    apply average_congr_on_block
    intro j hj
    exact Set.indicator_of_mem ((hs i j hj).mp hi) f
  · rw [Set.indicator_of_notMem hi]
    calc
      _ = average n b k (fun _ => (0 : E)) i := by
        apply average_congr_on_block
        intro j hj
        exact Set.indicator_of_notMem (fun hjs => hi ((hs i j hj).mpr hjs)) f
      _ = 0 := average_const _ _ _ _ _

theorem mean_indicator_average (n k : ℕ) (b : Bias n) (f : Leaf n → E) (s : Set (Leaf n))
    (hs : MeasurableSet[dyadicMeasurableSpace n k] s) :
    mean n b (s.indicator (average n b k f)) = mean n b (s.indicator f) := by
  rw [← average_indicator n k b f s hs, mean_average]

end Averages

section Transport
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {n : ℕ} (φ : Ω → Leaf n) (hφ : Measurable φ)

include hφ in
omit [CompleteSpace E] [NormedSpace ℝ E] in
theorem comp_memLp (f : Leaf n → E) : MemLp (fun x => f (φ x)) 2 μ :=
  MemLp.of_bound ((SimpleFunc.ofFinite f).stronglyMeasurable.comp_measurable hφ).aestronglyMeasurable
    ‖f‖ (Eventually.of_forall (fun x => norm_le_pi_norm f (φ x)))

include hφ in
theorem exists_bias_map : ∃ b : Bias n, Valid b ∧ ∀ i, mass n b i = (μ.map φ).real {i} := by
  have : IsProbabilityMeasure (μ.map φ) := Measure.isProbabilityMeasure_map hφ.aemeasurable
  apply exists_bias_of_weights n (fun i => (μ.map φ).real {i})
  · intro i
    exact ENNReal.toReal_nonneg
  · have h := integral_fintype (μ := μ.map φ) (integrable_const (1 : ℝ))
    simpa only [smul_eq_mul, mul_one] using h.symm.trans (by simp)

variable (b : Bias n) (hb : ∀ i, mass n b i = (μ.map φ).real {i})

include hφ hb in
theorem integral_comp_eq_mean (f : Leaf n → E) :
    ∫ x, f (φ x) ∂μ = mean n b f := by
  have : IsProbabilityMeasure (μ.map φ) := Measure.isProbabilityMeasure_map hφ.aemeasurable
  have hf : Integrable f (μ.map φ) :=
    ((SimpleFunc.ofFinite f).memLp_of_isFiniteMeasure 2 (μ.map φ)).integrable (by norm_num)
  have hfm : AEStronglyMeasurable f (μ.map φ) := (SimpleFunc.ofFinite f).aestronglyMeasurable
  rw [← integral_map hφ.aemeasurable hfm,
    integral_fintype hf, mean_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hb i])

omit [CompleteSpace E] in
theorem stronglyMeasurable_average (k : ℕ) (f : Leaf n → E) :
    StronglyMeasurable[dyadicMeasurableSpace n k] (average n b k f) := by
  let : MeasurableSpace (Leaf n) := dyadicMeasurableSpace n k
  let sf : SimpleFunc (Leaf n) E := ⟨average n b k f, fun x i j hij => by
    change average n b k f i = x ↔ average n b k f j = x
    rw [average_eq_of_mem n k b f i j hij], Set.finite_range _⟩
  exact sf.stronglyMeasurable

include hφ hb in
theorem average_comp_ae_condExp (k : ℕ) (f : Leaf n → E) :
    (fun x => average n b k f (φ x)) =ᵐ[μ]
      μ[(fun x => f (φ x)) | (dyadicMeasurableSpace n k).comap φ] := by
  let s := (dyadicMeasurableSpace n k).comap φ
  let : MeasurableSpace Ω := mΩ
  have hs : s ≤ mΩ := (MeasurableSpace.comap_mono (show dyadicMeasurableSpace n k ≤
    leafMeasurableSpace n from le_top)).trans hφ.comap_le
  have hφs : Measurable[s, dyadicMeasurableSpace n k] φ := fun t ht => ⟨t, ht, rfl⟩
  apply ae_eq_condExp_of_forall_setIntegral_eq hs ((comp_memLp μ φ hφ f).integrable (by norm_num))
  · intro t _ _
    exact ((comp_memLp μ φ hφ (average n b k f)).integrable (by norm_num)).integrableOn
  · rintro t ⟨u, hu, rfl⟩ _
    have hpre : MeasurableSet (φ ⁻¹' u) := hs _ ⟨u, hu, rfl⟩
    rw [← integral_indicator hpre, ← integral_indicator hpre]
    change (∫ x, (u.indicator (average n b k f)) (φ x) ∂μ) =
      ∫ x, (u.indicator f) (φ x) ∂μ
    rw [integral_comp_eq_mean μ φ hφ b hb, integral_comp_eq_mean μ φ hφ b hb,
      mean_indicator_average n k b f u hu]
  · exact ((stronglyMeasurable_average b k f).comp_measurable hφs).aestronglyMeasurable

end Transport

end HilbertUMD.WeightedTree
