/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularPowFP

/-! # Native residues of powers supplied by binary exponents

The output is a canonical residue. The integer power is never written out;
only its base, exponent, and modulus predecessor need FP binary writers.
-/

@[expose] public section
namespace LeanCanny.Algebra.ImplicitPowerResidue
open LeanCanny.Encoding MatrixPower

variable (base exponent modulus : List Bool → List Bool)

def value (c : List Bool) : List Bool :=
  BinaryNat.powMod (pair (base c) (pair (exponent c) (modulus c)))

theorem value_mem_FP (hb : base ∈ FP) (he : exponent ∈ FP) (hm : modulus ∈ FP) :
    value base exponent modulus ∈ FP :=
  mem_FP_comp (mem_FP_pair hb (mem_FP_pair he hm)) BinaryNat.powMod_mem_FP

theorem value_eq (c : List Bool) : value base exponent modulus c =
    residueBits ((Nat.fromBitsLE (base c) : ZMod (Nat.fromBitsLE (modulus c) + 1)) ^
      Nat.fromBitsLE (exponent c)) := by
  let : NeZero (Nat.fromBitsLE (modulus c) + 1) := ⟨by omega⟩
  rw [value, BinaryNat.powMod_eq_bits]
  simp only [pairFst_pair, pairSnd_pair, ← Nat.cast_pow, residueBits,
    ZMod.val_natCast, BinaryNatCode.encode]

/-- This includes modulus one and arbitrary composite moduli. -/
theorem power_two_mem_FP (he : exponent ∈ FP) (hm : modulus ∈ FP) :
    (fun c => residueBits (((2 : ℤ) ^ Nat.fromBitsLE (exponent c) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c) + 1))) ∈ FP := by
  have h := value_mem_FP (fun _ => BinaryNatCode.encode 2) exponent modulus
    (constFn_mem_FP _) he hm
  apply mem_FP_of_eq h
  intro c
  rw [value_eq]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Int.cast_pow, Int.cast_ofNat,
    Nat.cast_ofNat]

end LeanCanny.Algebra.ImplicitPowerResidue
