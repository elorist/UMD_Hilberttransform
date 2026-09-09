import HilbertUMD

/-! Check the mathematical meanings of the normed types, dimensions, and
operator constants independently of the public statement structures. -/

noncomputable section
open MeasureTheory Filter HilbertUMD
open scoped ENNReal NNReal Topology BigOperators

universe uΩ vΩ

section Geometry
variable {𝕜 : Type*} [RCLike 𝕜]

example (n : ℕ) (x : HSpace 𝕜 n) :
    ‖x‖ ^ 2 = ∑ a : Node n, ‖∑ j ∈ nodeLeaves n a, x j‖ ^ 2 := by
  change hilbertNorm n (fun j => x j) ^ 2 = _
  simp only [hilbertNorm_sq, blockSum_eq_sum_nodeLeaves]

example (n : ℕ) (x : ESpace 𝕜 n) :
    ‖x‖ = ⨅ u : Vec 𝕜 n, (∑ i, ‖u i‖) +
      Real.sqrt (∑ a : Node n, ‖∑ j ∈ nodeLeaves n a, (x j - u j)‖ ^ 2) := by
  change (⨅ u : Vec 𝕜 n, l1Norm n u + hilbertNorm n (fun j => x j - u j)) = _
  congr 1
  funext u
  rw [l1Norm_eq]
  congr 1
  have h := Real.sqrt_sq (apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (fun j => x j - u j))
  simpa only [hilbertNorm_sq, blockSum_eq_sum_nodeLeaves, Pi.sub_apply] using h.symm

example (n : ℕ) (x : XSpace 𝕜 n) :
    ‖x‖ = max ‖summation n x‖
      (⨅ u : Vec 𝕜 n, l1Norm n u + hilbertNorm n (fun j => x j - u j)) := rfl

example (n : ℕ) (x : YSpace 𝕜 n) :
    ‖x‖ = max ‖signedDyadic n x‖
      (⨅ u : Vec 𝕜 n, l1Norm n u + hilbertNorm n (fun j => x j - u j)) := rfl

example (n : ℕ) : Module.finrank 𝕜 (XSpace 𝕜 n) = 2 ^ n := by
  change Module.finrank 𝕜 (Leaf n → 𝕜) = _
  rw [Module.finrank_pi, card_leaf]

example (n : ℕ) : Module.finrank 𝕜 (YSpace 𝕜 n) = 2 ^ n := by
  change Module.finrank 𝕜 (Leaf n → 𝕜) = _
  rw [Module.finrank_pi, card_leaf]

example (n : ℕ) : Module.finrank 𝕜 (Paper.X 𝕜 n) = 2 ^ n := Paper.finrank_X 𝕜 n
example (n : ℕ) : Module.finrank 𝕜 (Paper.Y 𝕜 n) = 2 ^ n := Paper.finrank_Y 𝕜 n

example (n : ℕ) : CompleteSpace (XSpace 𝕜 n) := inferInstance
example (n : ℕ) : CompleteSpace (YSpace 𝕜 n) := inferInstance

end Geometry

section Constants
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

example (p : ℝ≥0∞) : Paper.hbar 𝕜 p E =
    hilbertConstant p (ContinuousLinearMap.id 𝕜 E) := rfl

example (p : ℝ≥0∞) : Paper.beta.{uΩ} 𝕜 p E =
    umdConstant.{uΩ} p (ContinuousLinearMap.id 𝕜 E) := rfl

example (p : ℝ≥0∞) (T : E →L[𝕜] F) (C : ℝ≥0) :
    HilbertBound p T C ↔
      ∀ f : ℝ → E, ContDiff ℝ 1 f → HasCompactSupport f →
        ∃ g : ℝ → F,
          (∀ x : ℝ, Tendsto (fun ε : ℝ => (Real.pi)⁻¹ •
            ∫ y in {y : ℝ | ε < |x - y|}, (x - y)⁻¹ • T (f y))
              (𝓝[>] 0) (𝓝 (g x))) ∧
          MemLp g p volume ∧ eLpNorm g p volume ≤ (C : ℝ≥0∞) * eLpNorm f p volume := Iff.rfl

example (p : ℝ≥0∞) (T : E →L[𝕜] F) (C : ℝ≥0) :
    UMDBound.{uΩ} p T C ↔
      ∀ (Ω : Type uΩ) (mΩ : MeasurableSpace Ω) (μ : Measure Ω), SigmaFinite μ →
      ∀ m : ℕ, 1 ≤ m →
      ∀ ℱ : Filtration (Fin (m + 1)) mΩ, SigmaFiniteFiltration μ ℱ →
      ∀ f : Fin (m + 1) → Ω → E,
        (StronglyAdapted ℱ f ∧ (∀ k, MemLp (f k) p μ) ∧
          ∀ i j, i ≤ j → ∀ s, MeasurableSet[ℱ i] s → μ s < ∞ →
            ∫ x in s, f i x ∂μ = ∫ x in s, f j x ∂μ) →
        ∀ ε : Fin m → 𝕜, (∀ k, ‖ε k‖ = 1) →
          eLpNorm (fun x => ∑ k : Fin m, ε k • T (f k.succ x - f k.castSucc x)) p μ ≤
            (C : ℝ≥0∞) * eLpNorm (fun x => ∑ k : Fin m, (f k.succ x - f k.castSucc x)) p μ := by
  constructor
  · intro h Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε
    exact h Ω mΩ μ hμ m hm ℱ hℱ f ⟨hf.1, hf.2.1, hf.2.2⟩ ε hε
  · intro h Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε
    exact h Ω mΩ μ hμ m hm ℱ hℱ f ⟨hf.stronglyAdapted, hf.memLp, hf.setIntegral_eq⟩ ε hε

end Constants

section UniverseIndependence
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The characterization has no dimension or finiteness assumption on the
operator spaces and preserves the exact bound. -/
example (T : E →L[𝕜] F) (C : ℝ≥0) :
    UMDBound.{uΩ} 2 T C ↔ FiniteDyadicTerminalBound 2 T C :=
  umdBound_two_iff_finiteDyadicTerminalBound T C

example (T : E →L[𝕜] F) (C : ℝ≥0) :
    UMDBound.{uΩ} 2 T C ↔ UMDBound.{vΩ} 2 T C :=
  ⟨fun h => h.changeUniverse_two, fun h => h.changeUniverse_two⟩

/-- Equality includes the infinite-constant case: no UMD hypothesis is assumed. -/
example (T : E →L[𝕜] F) : umdConstant.{uΩ} 2 T = umdConstant.{vΩ} 2 T :=
  umdConstant_two_universe_eq T

example (T : E →L[𝕜] F) : umdConstant.{0} 2 T = umdConstant.{1} 2 T :=
  umdConstant_two_universe_eq T

end UniverseIndependence

example {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 < ENNReal.ofReal (c * ((n : ℝ) + 1)) ∧
    0 < ENNReal.ofReal (c * Real.sqrt ((n : ℝ) + 1)) := ⟨by positivity, by positivity⟩

#check @HilbertUMD.theorem_1_1
#check @HilbertUMD.umdConstant_two_universe_eq
#check @HilbertUMD.main_theorem_p2
#check @HilbertUMD.main_theorem_p2_quantitative
