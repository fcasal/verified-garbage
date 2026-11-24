module

public import VerifiedGarbage.TCB.Artifact

/-!
# Checking a public API against an independent contract

A guarantee fixes the signature and behavior promised to callers. The candidate
contract must admit every promised call, preserve its result and respect its
public-input boundary on every ABI. An ABI can have no states satisfying the
reference precondition, so this comparison does not require a witness for it.
-/

@[expose] public section

namespace VG.Spec

structure ExportGuarantee where
  sig : Sig
  writeArgs : Bool
  contract : Contracts

/-- A missing contract fails. A stronger output guarantee or acceptance of more
inputs is compatible. The ABI's requirement on the return register is preserved. -/
def ExportGuarantee.Holds (g : ExportGuarantee) (sig : Sig) (writeArgs : Bool)
    (contracts : Option Contracts) : Prop :=
  sig = g.sig ∧ writeArgs = g.writeArgs ∧
    match contracts with
    | none => False
    | some candidate => ∀ {M : ISA} (A : Abi M) (stack : Nat),
        let ref := g.contract A stack
        let impl := candidate A stack
        (∀ s, ref.pre s → impl.pre s) ∧
        (∀ s t, ref.pre s → impl.post s t → ref.post s t) ∧
        (∀ s t, ref.pre s → ref.pre t → ref.pub s t → impl.pub s t) ∧
        impl.retExt = ref.retExt

end VG.Spec
