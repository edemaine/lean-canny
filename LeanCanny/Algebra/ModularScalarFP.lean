/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralScaledCharacteristicSpace

/-! # Native FP operations on canonical modular scalar readers

Binary metadata supplies a positive modulus and exponent. Multiplication,
natural casts, and powering compose FP residue readers without constructing
an unbounded integer value or using division modulo the caller modulus.
-/

@[expose] public section
namespace LeanCanny.Algebra.ModularScalarFP
open LeanCanny.Encoding MatrixPower
set_option backward.isDefEq.respectTransparency false

variable {m : List Bool → ℕ}

attribute [local irreducible] BinaryNat.mulMod BinaryNat.powMod BinaryNat.mod

theorem mul (hm : BinaryFn m) (x y : (c : List Bool) → ZMod (m c))
    (hx : (fun c => residueBits (x c)) ∈ FP) (hy : (fun c => residueBits (y c)) ∈ FP) :
    (fun c => residueBits (x c * y c)) ∈ FP := by
  have H := mem_FP_comp (mem_FP_pair hm.bits_mem_FP (mem_FP_pair hx hy)) BinaryNat.mulMod_mem_FP
  exact mem_FP_of_eq H (fun c => ArithmeticBits.mulMod_residueBits (m c) (x c) (y c))

theorem natCast (hm : BinaryFn m) (n : List Bool → ℕ) (hn : BinaryFn n) :
    (fun c => residueBits (n c : ZMod (m c))) ∈ FP := by
  have H := mem_FP_comp (mem_FP_pair hn.bits_mem_FP hm.bits_mem_FP) BinaryNat.mod_mem_FP
  refine mem_FP_of_eq H (fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.mod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, residueBits, ZMod.val_natCast]

theorem pow (hm : BinaryFn m) (hm0 : ∀ c, m c ≠ 0) (e : List Bool → ℕ) (he : BinaryFn e)
    (x : (c : List Bool) → ZMod (m c)) (hx : (fun c => residueBits (x c)) ∈ FP) :
    (fun c => residueBits (x c ^ e c)) ∈ FP := by
  have H := mem_FP_comp (mem_FP_pair hx (mem_FP_pair he.bits_mem_FP
    (hm.sub (BinaryFn.const 1)).bits_mem_FP)) BinaryNat.powMod_mem_FP
  exact mem_FP_of_eq H (fun c => IntegralScaledCharacteristicBits.pow_residue _ _ (hm0 c) (x c))

end LeanCanny.Algebra.ModularScalarFP
