import HilbertUMD

/-! Audit every project declaration, including private helpers and declarations
outside the three main theorems' dependency closures. The statement and module
contribution checks remain in MainTheorem.lean. -/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[]
  let mut projectCount : Nat := 0
  for (name, _) in env.constants.toList do
    let projectModule := match env.getModuleIdxFor? name with
      | some i => (`HilbertUMD).isPrefixOf env.header.moduleNames[i]!
      | none => false
    if projectModule || (`HilbertUMD).isPrefixOf name then
      projectCount := projectCount + 1
      seen := seen.insert name
      todo := todo.push name
  if projectCount == 0 then
    throwError "No project declarations found; refusing an empty audit"
  let mut index := 0
  while index < todo.size do
    let name := todo[index]!
    index := index + 1
    let some info := env.find? name
      | throwError "Missing declaration in the project dependency graph: {name}"
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
      throwError "Admitted proof in the project's dependencies: {name}"
    if let .axiomInfo _ := info then
      unless name ∈ [`propext, `Classical.choice, `Quot.sound] do
        throwError "Unexpected foundational dependency: {name}"
    for child in info.getUsedConstantsAsSet.toArray do
      unless seen.contains child do
        seen := seen.insert child
        todo := todo.push child
  logInfo m!"PASS: whole-project axiom audit; {projectCount} project declarations; {seen.size} transitive declarations; no admissions or extra axioms."
