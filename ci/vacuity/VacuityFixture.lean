module

namespace VacuityFixture

public abbrev preLen (len : Nat) := len < 1409

private theorem impossible (len : Nat) (_ : ¬ preLen len) (_ : len < 512) : True := trivial

-- The shared endpoint, 1409, satisfies both assumptions.
public theorem reachable (len : Nat) (_ : ¬ preLen len) (_ : len ≤ 1409) : True := trivial

end VacuityFixture
