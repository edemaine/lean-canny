/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanCanny.Encoding.NatBits

/-!
Adapted from Complexitylib at add0aca8ee0d71e68969f2cb45cf91554a50f787.
The definitions preserve the existing wire format and use no machine model.

# Canonical variable-width binary natural-number codes

This module packages `Nat.bits` as a canonical binary code for natural
numbers. Bits are ordered least-significant first, and redundant high zeroes
are rejected. In particular, zero has the unique empty code.

Unlike a prefix code, this representation relies on an enclosing framing
layer to determine the field boundary. `Complexitylib.Encoding.Pairing`
provides that framing for variable-length machine inputs.
-/


@[expose] public section

namespace LeanCanny

namespace BinaryNatCode

/-- Encode a natural by its minimal little-endian binary expansion. -/
def encode (value : ℕ) : List Bool :=
  value.bits

/-- Decode a natural only when the supplied bits are its minimal expansion.

This rejects every redundant high-zero representation, making `encode` and
`decode?` an exact codec rather than merely a value interpretation. -/
def decode? (bits : List Bool) : Option ℕ :=
  let value := Nat.fromBitsLE bits
  if value.bits = bits then some value else none

/-- Canonical binary codes have exactly the standard binary digit width. -/
@[simp] theorem length_encode (value : ℕ) :
    (encode value).length = value.size := by
  exact Nat.size_eq_bits_len value

/-- Decoding a canonical binary code recovers its value. -/
@[simp] theorem decode?_encode (value : ℕ) :
    decode? (encode value) = some value := by
  simp [decode?, encode, Nat.fromBitsLE_bits]

/-- Exact decoding succeeds precisely on the canonical code of the result. -/
theorem decode?_eq_some_iff (bits : List Bool) (value : ℕ) :
    decode? bits = some value ↔ bits = encode value := by
  constructor
  · intro h
    simp only [decode?] at h
    split at h
    next hcanonical =>
      cases h
      exact hcanonical.symm
    next => simp at h
  · rintro rfl
    exact decode?_encode value

/-- The canonical binary natural-number encoding is injective. -/
theorem encode_injective : Function.Injective encode := by
  intro first second h
  have hfirst := decode?_encode first
  rw [h, decode?_encode second] at hfirst
  exact Option.some.inj hfirst.symm

end BinaryNatCode

end LeanCanny
