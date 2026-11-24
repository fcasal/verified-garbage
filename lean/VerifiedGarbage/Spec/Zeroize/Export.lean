module

public import VerifiedGarbage.Spec.ExportGuarantee

/-! # The public guarantee of `vg_zeroize` -/

@[expose] public section

namespace VG.Spec.Zeroize

def exportSig : Sig := { params := [("p", .slice true .u8 "len")] }

/-- Any writable byte slice can be wiped. Every byte in it must be zero on return.
This reference is independent of the API's candidate signature and contract. -/
def exportGuarantee : ExportGuarantee where
  sig := exportSig
  writeArgs := false
  contract A stack := exportSig.contract A (stack := stack)
    (post := fun p len _ after _ =>
      (List.range len.toNat).map (fun i => after (p + BitVec.ofNat 64 i)) =
        List.replicate len.toNat 0)

end VG.Spec.Zeroize
