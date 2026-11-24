module

import VerifiedGarbage.Proof.Zeroize.Export
import VerifiedGarbage.TCB.Axioms

/-! # Regressions that must fail the public contract check -/

namespace VG.Test.ExportGuarantee

#assert_standard_axioms VG.Proof.Zeroize.exportGuarantee

open VG.Spec.Zeroize

-- A legal one-byte buffer whose byte is still set.
private def oneByte (M : ISA) : Abi M where
  ptrBits := 64
  args := fun _ => some (fun _ => [0, 1])
  argArea := fun _ _ => []
  reserved := fun _ _ => []
  wf := fun _ _ _ => True
  pub := fun _ _ => True
  mem := fun _ _ => 1
  rd := fun _ => []
  wr := fun _ => [⟨0, 1⟩]
  ret := fun _ => 0
  retExt := fun _ => none

private theorem admitted {M : ISA} (s : M.State) :
    (exportGuarantee.contract (oneByte M) 0).pre s := by
  simp [exportGuarantee, exportSig, oneByte, Sig.contract, Sig.bufs, Sig.lists,
    Sig.words, Param.words]
  exact ⟨rfl, by decide, True.intro⟩

private def anyOutput : Contracts := fun A stack =>
  zeroizeSig.contract A (stack := stack) (post := fun _ _ _ _ _ => True)

example {M : ISA} (s : M.State) :
    ¬ exportGuarantee.Holds zeroizeSig false (some @anyOutput) := by
  intro h
  have wrong := (h.2.2 (oneByte M) 0).2.1 s s (admitted s)
    (show (anyOutput (oneByte M) 0).post s s from True.intro)
  exact (by decide : ([1] : List Byte) ≠ [0]) wrong

private def emptyOnly : Contracts := fun A stack =>
  zeroizeSig.contract A (stack := stack) (pre := fun _ len _ => len.toNat = 0)
    (post := fun p len _ after _ => bytesAt after p len.toNat = zeros len.toNat)

example {M : ISA} (s : M.State) :
    ¬ exportGuarantee.Holds zeroizeSig false (some @emptyOnly) := by
  intro h
  have pre := (h.2.2 (oneByte M) 0).1 s (admitted s)
  have empty : (1 : Nat) = 0 := pre.2.2.2.2.2.2
  exact Nat.noConfusion empty

-- A candidate that declares every pair of calls distinguishable could leak
-- secret inputs while satisfying its own constant-time contract.
private def allDistinguishable : Contracts := fun A stack =>
  { zeroizeContract A stack with pub := fun _ _ => False }

example {M : ISA} (s : M.State) :
    ¬ exportGuarantee.Holds zeroizeSig false (some @allDistinguishable) := by
  intro h
  apply (h.2.2 (oneByte M) 0).2.2.1 s s (admitted s) (admitted s)
  simp [exportGuarantee, exportSig, oneByte, Sig.contract, Sig.descs]

example : ¬ exportGuarantee.Holds zeroizeSig false none := fun h => h.2.2

end VG.Test.ExportGuarantee
