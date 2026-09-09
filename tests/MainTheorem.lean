import HilbertUMD

/-! Verify the paper statement, its internal and quantitative companions,
and every transitive proof dependency. -/

open HilbertUMD
open scoped ENNReal

universe uΩ vΩ

example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    Paper.Theorem11Bounds.{uΩ} ℝ n c C ∧ Paper.Theorem11Bounds.{uΩ} ℂ n c C :=
  theorem_1_1.{uΩ}

/-- The same comparison constants work in independent universes and at concrete
levels zero and one, with both fields checked in every universe. -/
example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    (Paper.Theorem11Bounds.{uΩ} ℝ n c C ∧ Paper.Theorem11Bounds.{uΩ} ℂ n c C) ∧
    (Paper.Theorem11Bounds.{vΩ} ℝ n c C ∧ Paper.Theorem11Bounds.{vΩ} ℂ n c C) ∧
    (Paper.Theorem11Bounds.{0} ℝ n c C ∧ Paper.Theorem11Bounds.{0} ℂ n c C) ∧
    (Paper.Theorem11Bounds.{1} ℝ n c C ∧ Paper.Theorem11Bounds.{1} ℂ n c C) := by
  obtain ⟨c, C, hc, hC, h⟩ := theorem_1_1.{uΩ}
  refine ⟨c, C, hc, hC, fun n hn => ?_⟩
  obtain ⟨hr, hz⟩ := h n hn
  exact ⟨⟨hr, hz⟩, ⟨hr.changeUniverse, hz.changeUniverse⟩,
    ⟨hr.changeUniverse, hz.changeUniverse⟩, ⟨hr.changeUniverse, hz.changeUniverse⟩⟩

/-- Check all eight literal n/sqrt(n) inequalities, independently of the
paper abbreviations, as well as both dimensions. -/
example {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {c C : ℝ}
    [NormedSpace ℝ (XSpace 𝕜 n)] [NormedSpace ℝ (YSpace 𝕜 n)]
    (h : Paper.Theorem11Bounds.{uΩ} 𝕜 n c C) :
    Module.finrank 𝕜 (XSpace 𝕜 n) = 2 ^ n ∧
    Module.finrank 𝕜 (YSpace 𝕜 n) = 2 ^ n ∧
    ENNReal.ofReal (c * (n : ℝ)) ≤ hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) ∧
    hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) ≤ ENNReal.ofReal (C * (n : ℝ)) ∧
    ENNReal.ofReal (c * Real.sqrt (n : ℝ)) ≤ umdConstant.{uΩ} 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) ∧
    umdConstant.{uΩ} 2 (ContinuousLinearMap.id 𝕜 (XSpace 𝕜 n)) ≤ ENNReal.ofReal (C * Real.sqrt (n : ℝ)) ∧
    ENNReal.ofReal (c * (n : ℝ)) ≤ umdConstant.{uΩ} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ∧
    umdConstant.{uΩ} 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ≤ ENNReal.ofReal (C * (n : ℝ)) ∧
    ENNReal.ofReal (c * Real.sqrt (n : ℝ)) ≤ hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ∧
    hilbertConstant 2 (ContinuousLinearMap.id 𝕜 (YSpace 𝕜 n)) ≤ ENNReal.ofReal (C * Real.sqrt (n : ℝ)) :=
  ⟨h.x_dimension, h.y_dimension, h.x_hilbert_lower, h.x_hilbert_upper,
    h.x_umd_lower, h.x_umd_upper, h.y_umd_lower, h.y_umd_upper,
    h.y_hilbert_lower, h.y_hilbert_upper⟩

#print axioms HilbertUMD.theorem_1_1
#print axioms HilbertUMD.umdConstant_two_universe_eq

example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    P2MainBounds ℝ n c C ∧ P2MainBounds ℂ n c C := main_theorem_p2

example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    P2MainBounds ℝ n c C := by
  obtain ⟨c, C, hc, hC, h⟩ := main_theorem_p2
  exact ⟨c, C, hc, hC, fun n hn => (h n hn).1⟩

example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    P2MainBounds ℂ n c C := by
  obtain ⟨c, C, hc, hC, h⟩ := main_theorem_p2
  exact ⟨c, C, hc, hC, fun n hn => (h n hn).2⟩

#print axioms HilbertUMD.main_theorem_p2

example (n : ℕ) (hn : 1 ≤ n) :
    P2QuantitativeBounds ℝ n (1 / 7) xUMDLowerConstant
      yHilbertLowerConstant 285 57 ∧
    P2QuantitativeBounds ℂ n (1 / 7) xUMDLowerConstant
      yHilbertLowerConstant 448 57 :=
  main_theorem_p2_quantitative n hn

example (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (((n : ℝ) + 1) / 7) ≤
      hilbertConstant 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) := by
  simpa only [one_div_mul_eq_div] using (main_theorem_p2_quantitative n hn).1.x_hilbert_lower

example (n : ℕ) (hn : 1 ≤ n) :
    umdConstant.{uΩ} 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) ≤
      min ((n : ℝ≥0∞) + 1) (ENNReal.ofReal (285 * Real.sqrt ((n : ℝ) + 1))) := by
  calc
    _ = umdConstant.{0} 2 (ContinuousLinearMap.id ℝ (XSpace ℝ n)) :=
      umdConstant_two_universe_eq _
    _ ≤ _ := (main_theorem_p2_quantitative n hn).1.x_umd_upper

example (n : ℕ) (hn : 1 ≤ n) :
    umdConstant.{uΩ} 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) ≤
      min ((n : ℝ≥0∞) + 1) (ENNReal.ofReal (448 * Real.sqrt ((n : ℝ) + 1))) := by
  calc
    _ = umdConstant.{0} 2 (ContinuousLinearMap.id ℂ (XSpace ℂ n)) :=
      umdConstant_two_universe_eq _
    _ ≤ _ := (main_theorem_p2_quantitative n hn).2.x_umd_upper

/-- Retain the paper's 2n/3 lower bound in the public quantitative theorem,
over both fields and after transport to any sample-space universe. -/
example (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (2 * (n : ℝ) / 3) ≤
      umdConstant.{uΩ} 2 (ContinuousLinearMap.id ℝ (YSpace ℝ n)) := by
  calc
    _ ≤ umdConstant.{0} 2 (ContinuousLinearMap.id ℝ (YSpace ℝ n)) :=
      (main_theorem_p2_quantitative n hn).1.y_umd_lower
    _ = _ := umdConstant_two_universe_eq _

example (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (2 * (n : ℝ) / 3) ≤
      umdConstant.{uΩ} 2 (ContinuousLinearMap.id ℂ (YSpace ℂ n)) := by
  calc
    _ ≤ umdConstant.{0} 2 (ContinuousLinearMap.id ℂ (YSpace ℂ n)) :=
      (main_theorem_p2_quantitative n hn).2.y_umd_lower
    _ = _ := umdConstant_two_universe_eq _

example (n : ℕ) (hn : 1 ≤ n) :
    hilbertConstant 2 (ContinuousLinearMap.id ℂ (YSpace ℂ n)) ≤
      min ((n : ℝ≥0∞) + 1)
        (ENNReal.ofReal (57 * Real.sqrt ((n : ℝ) + 1))) :=
  (main_theorem_p2_quantitative n hn).2.y_hilbert_upper

#print axioms HilbertUMD.main_theorem_p2_quantitative

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  seen := seen.insert `HilbertUMD.theorem_1_1
  seen := seen.insert `HilbertUMD.main_theorem_p2
  seen := seen.insert `HilbertUMD.main_theorem_p2_quantitative
  let mut usedModules : NameSet := {}
  let mut todo : Array Name :=
    #[`HilbertUMD.theorem_1_1, `HilbertUMD.main_theorem_p2, `HilbertUMD.main_theorem_p2_quantitative]
  let mut index := 0
  while index < todo.size do
    let name := todo[index]!
    index := index + 1
    if let some i := env.getModuleIdxFor? name then
      usedModules := usedModules.insert env.header.moduleNames[i]!
    let some info := env.find? name
      | throwError "Missing declaration in the proof dependency graph: {name}"
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
      throwError "Admitted proof in the main theorem's dependencies: {name}"
    if let .axiomInfo _ := info then
      unless name ∈ [`propext, `Classical.choice, `Quot.sound] do
        throwError "Unexpected foundational dependency: {name}"
    for child in info.getUsedConstantsAsSet.toArray do
      unless seen.contains child do
        seen := seen.insert child
        todo := todo.push child
  let mut count : Nat := 0
  for mod in env.header.moduleNames do
    if mod != `HilbertUMD && (`HilbertUMD).isPrefixOf mod then
      unless usedModules.contains mod do
        throwError "Module contributes no declarations to the main theorem: {mod}"
      count := count + 1
  logInfo m!"PASS: full main theorem (Theorem 1.1) in arbitrary sample-space universes, internal formulation, and quantitative companion over R and C; {seen.size} transitive declarations; {count} contributing project modules; no admissions or extra axioms."
