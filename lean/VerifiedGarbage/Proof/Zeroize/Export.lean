module

public import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.Spec.Zeroize.Export

/-! # The exported zeroization API meets its public guarantee on every target -/

public section

namespace VG.Proof.Zeroize

theorem exportGuarantee : Spec.Zeroize.exportGuarantee.Holds
    Spec.Zeroize.zeroizeApi.sig Spec.Zeroize.zeroizeApi.writeArgs Spec.Zeroize.zeroizeApi.contracts :=
  ⟨rfl, rfl, fun _ _ => ⟨fun _ h => h, fun _ _ _ h => h, fun _ _ _ _ h => h, rfl⟩⟩

end VG.Proof.Zeroize
