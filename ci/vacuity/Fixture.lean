module

meta import Lean.Elab.Command

namespace VacuityFixture

abbrev preLen (len : Nat) := len < 1409

private theorem impossible (len : Nat) (_ : ¬ preLen len) (_ : len < 512) : True := trivial

-- The shared endpoint, 1409, satisfies both assumptions.
theorem reachable (len : Nat) (_ : ¬ preLen len) (_ : len ≤ 1409) : True := trivial

-- An ordinary source message must never be interpreted as an audit result.
run_cmd Lean.logInfo "vacuity finding VacuityFixture.reachable"

end VacuityFixture
