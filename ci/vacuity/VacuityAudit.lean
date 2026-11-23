module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Meta.Check

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

private structure Finding where
  name : String
  line : Nat
  deriving ToJson

private structure AuditResult where
  scanned : Nat := 0
  findings : Array Finding := #[]
  incomplete : Array String := #[]
  deriving ToJson

elab "#auditVacuity" : command => do
  let env ← getEnv
  let mut result : AuditResult := {}
  for (name, info) in env.constants.map₂.toList do
    let userName := privateToUserName name
    unless info.isTheorem && !userName.isInternal do continue
    let some ranges ← findDeclarationRanges? name | continue
    result := { result with scanned := result.scanned + 1 }
    try
      let found ← liftTermElabM <| withCurrHeartbeats <| inconsistent info.type
      if found then
        let finding := { name := userName.toString, line := ranges.selectionRange.pos.line : Finding }
        result := { result with findings := result.findings.push finding }
    catch e =>
      result := { result with incomplete := result.incomplete.push s!"{userName}: {← e.toMessageData.toString}" }
  logInfo <| .tagged `VacuityAudit.result m!"{(toJson result).compress}"

end VacuityAudit
