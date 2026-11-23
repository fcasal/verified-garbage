module

meta import Lean

meta section

open Lean Elab Command Meta

namespace VacuityAudit

/-- Search only the theorem's binders. Its conclusion and its proof are never given to omega. -/
private def inconsistent (type : Expr) : MetaM Bool :=
  forallTelescope type fun xs _ => do
    let facts ← xs.filterM fun x => do isProp (← inferType x)
    if facts.isEmpty then return false
    let goal ← mkFreshExprMVar (mkConst ``False)
    try
      Elab.Tactic.Omega.omega facts.toList goal.mvarId!
    catch e =>
      if (← e.toMessageData.toString).startsWith "omega could not prove the goal" then
        return false
      throw e
    let witness ← instantiateMVars goal
    if witness.hasMVar || witness.hasSorry then throwError "unfinished contradiction proof"
    -- Ascription asks the kernel to check that the witness has type False.
    checkWithKernel (← mkLambdaFVars xs (mkExpectedPropHint witness (mkConst ``False)))
    return true

-- CI supplies the target as the final `import all` in the Lean module setup.
-- Each invocation loads exactly one target, including its private theorems.
run_cmd
  let env ← getEnv
  let some target := env.header.imports.back? | throwError "missing audit target"
  unless target.importAll do throwError "audit target must include private declarations"
  let some idx := env.getModuleIdx? target.module | throwError "unknown audit target {target.module}"
  let mut scanned : Nat := 0
  let fixture := target.module == `VacuityFixture
  let path := "lean/" ++ target.module.toString.replace "." "/" ++ ".lean"
  let report ← IO.getEnv "VG_VACUITY_FINDINGS"
  let mut fixtureFindings : Array Name := #[]
  for n in env.header.moduleData[idx.toNat]!.constNames do
    let name := privateToUserName n
    let ci ← getConstInfo n
    unless ci.isTheorem && !name.isInternal do continue
    let some loc ← findDeclarationRanges? n | continue
    scanned := scanned + 1
    unless ← liftTermElabM <| withCurrHeartbeats <| inconsistent ci.type do continue
    if fixture then
      fixtureFindings := fixtureFindings.push name
    else
      -- Record each finding before starting the next, potentially slow theorem.
      let location := (toJson s!"{path}:{loc.selectionRange.pos.line} {name}").compress
      logInfo m!"Conflicting assumptions in {location}"
      if let some file := report then
        IO.FS.withFile file .append fun f => f.putStrLn ("    " ++ location)
  if fixture && (scanned != 2 || fixtureFindings != #[`VacuityFixture.impossible]) then
    throwError "expected only the impossible theorem, got {repr fixtureFindings} from {scanned} theorems"

end VacuityAudit
