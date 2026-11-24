module

public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA signed polynomial packing

For any polynomial whose coefficients lie in `[-a, b]`, FIPS 204 Algorithm 19
(`BitUnpack`) recovers the polynomial encoded by Algorithm 17 (`BitPack`).
-/

@[expose] public section

namespace VG.Spec.MlDsa

/-- Indexing a concatenation of fixed-width fields at field `i`, bit `j`. -/
private theorem getElem?_field {α β : Type} (f : α → List β) {d : Nat}
    (hlen : ∀ x, (f x).length = d) (xs : List α) {i j : Nat} (hi : i < xs.length) (hj : j < d) :
    (xs.flatMap f)[i * d + j]? = (f xs[i])[j]? := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons, List.getElem_cons_zero]
      exact List.getElem?_append_left (by simpa only [hlen] using hj)
    | succ i =>
      rw [List.flatMap_cons, Nat.succ_mul, List.getElem?_append_right (by rw [hlen]; omega),
        hlen, show i * d + d + j - d = i * d + j by omega]
      exact ih (by simpa using hi)

/-- The weighted sum used to assemble a byte has exactly the supplied low bits. -/
private theorem weightedBits (f : Nat → Bool) (d : Nat) :
    let x := ((List.range d).map fun j => (f j).toNat * 2 ^ j).sum
    x < 2 ^ d ∧ ∀ j < d, x.testBit j = f j := by
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨hlt, hbits⟩ := ih
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    constructor
    · cases f d <;> simp [Nat.pow_succ] <;> omega
    · intro j hj
      rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hlt]
      by_cases h : j < d
      · simpa [h] using hbits j h
      · have : j = d := by omega
        subst j
        cases f d <;> simp

private theorem bytesToBits_bitsToBytes_getD (y : Array Bool) {k : Nat} (hk : k < y.size) :
    (bytesToBits (bitsToBytes y)).getD k false = y.getD k false := by
  have hb : k / 8 < (y.size + 7) / 8 := by omega
  have hj : k % 8 < 8 := Nat.mod_lt _ (by decide)
  have hpos : k / 8 * 8 + k % 8 = k := by omega
  unfold bytesToBits
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← hpos]
  rw [getElem?_field _ (d := 8) (by simp) _ (by simpa [bitsToBytes] using hb) hj, hpos]
  simp only [bitsToBytes, List.getElem_map, List.getElem_range, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some, ← Nat.testBit_eq_decide_div_mod_eq,
    BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
  rw [(weightedBits _ 8).2 _ hj, Nat.mul_comm 8, hpos]

private theorem bitsToInteger_integerToBits (x d : Nat) (hx : x < 2 ^ d) :
    bitsToInteger (integerToBits x d) = x := by
  induction d generalizing x with
  | zero => simp [integerToBits, bitsToInteger] at *; omega
  | succ d ih =>
    have hh : x / 2 < 2 ^ d := by rw [Nat.pow_succ] at hx; omega
    have hbits : integerToBits x (d + 1) = x.testBit 0 :: integerToBits (x / 2) d := by
      simp only [integerToBits, ← Nat.testBit_eq_decide_div_mod_eq, List.range_succ_eq_map,
        List.map_cons, List.map_map, Function.comp_def, Nat.testBit_add_one]
    rw [hbits]
    change 2 * bitsToInteger (integerToBits (x / 2) d) + (x.testBit 0).toNat = x
    rw [ih _ hh, Nat.toNat_testBit, Nat.pow_zero, Nat.div_one]
    omega

/-- Algorithms 17 and 19: unpacking a packed polynomial recovers it when its
coefficients lie in the encoding range `[-a, b]`. -/
theorem bitUnpack_bitPack (w : IPoly) (a b : Nat)
    (hw : ∀ c ∈ w.toList, -(a : Int) ≤ c ∧ c ≤ b) :
    bitUnpack (bitPack w a b) a b = w := by
  let d := bitlen (a + b)
  let field := fun c : Int => integerToBits ((b : Int) - c).toNat d
  have hlen (c : Int) : (field c).length = d := by simp [field, integerToBits]
  let y := (w.toList.flatMap field).toArray
  have hsize : y.size = n * d := by
    simp [y, List.length_flatMap, hlen, List.map_const', List.sum_replicate_nat]
  apply Vector.ext
  intro i hi
  have hc := hw w[i] (List.getElem_mem (l := w.toList) (by simpa using hi))
  have hfits : ((b : Int) - w[i]).toNat < 2 ^ d :=
    Nat.lt_of_le_of_lt (by omega : ((b : Int) - w[i]).toNat ≤ a + b) Nat.lt_log2_self
  simp only [bitUnpack, Vector.getElem_ofFn]
  change (b : Int) - bitsToInteger ((List.range d).map fun j =>
    (bytesToBits (bitsToBytes y)).getD (i * d + j) false) = w[i]
  have hfield : ((List.range d).map fun j =>
      (bytesToBits (bitsToBytes y)).getD (i * d + j) false) = field w[i] := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    have hk : i * d + j < y.size := calc
      i * d + j < (i + 1) * d := by rw [Nat.succ_mul]; omega
      _ ≤ y.size := hsize ▸ Nat.mul_le_mul_right d hi
    rw [bytesToBits_bitsToBytes_getD _ hk, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      getElem?_field field hlen _ (by simpa using hi) hj]
    simp [field, integerToBits, List.getElem?_range hj]
  rw [hfield, bitsToInteger_integerToBits _ _ hfits]
  omega

end VG.Spec.MlDsa
