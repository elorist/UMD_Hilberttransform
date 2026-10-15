module

public import HilbertUMD
public import Solution

@[expose] public section

/-! Audit every library and Solution declaration, including private helpers and
declarations outside the main theorems' dependency closures. The statement and
module contribution checks remain in MainTheorem.lean. -/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  -- The ordinary imported environment omits private helpers and hides proofs.
  -- At the private import level Lean loads every transitive module's complete
  -- constant map. Keep extensions uninitialized so no cached axiom summary
  -- substitutes for the expression traversal below. Missing private object
  -- data is an import error, never an empty or partial successful audit.
  let visibleEnv ← getEnv
  let env ← liftIO <| importModules #[{ module := `HilbertUMD }, { module := `Solution }] {}
    (loadExts := false) (level := .private)
  if env.header.isModule then
    throwError "The whole-project audit requires unrestricted private module data"
  if env.header.moduleNames.contains `Challenge then
    throwError "The admitted Challenge statement must not enter the solution proof audit"
  for imported in env.header.modules do
    unless imported.importAll do
      throwError "Proof bodies were not fully imported for module: {imported.module}"
  for mod in visibleEnv.header.moduleNames do
    if ((`HilbertUMD).isPrefixOf mod || mod == `Solution) &&
        !env.header.moduleNames.contains mod then
      throwError "Project module missing from the whole-project audit: {mod}"
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[]
  let mut projectCount : Nat := 0
  for (name, _) in env.constants.toList do
    let projectModule := match env.getModuleIdxFor? name with
      | some i =>
        let mod := env.header.moduleNames[i]!
        (`HilbertUMD).isPrefixOf mod || mod == `Solution
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
  logInfo m!"PASS: whole-project axiom audit; {projectCount} project declarations including private helpers; {seen.size} transitive declarations checked from full proof bodies; no admissions or extra axioms."
