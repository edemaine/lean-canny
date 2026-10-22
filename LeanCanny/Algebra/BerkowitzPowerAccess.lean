/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzFactorChildCorrect

/-! # Binary dimensions and indices for the layered Berkowitz power -/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.PowerAccessBits
open LeanCanny.Encoding MatrixPower

def dimension (a : FactorChild.Access) (c : List Bool) : List Bool :=
  let w := BinaryNat.succ (a.dimension c)
  BinaryNat.mul (pair w w)

def target (a : FactorChild.Access) (c : List Bool) : List Bool :=
  BinaryNat.mul (pair (a.dimension c) (BinaryNat.succ (a.dimension c)))

theorem dimension_mem_FP (a : FactorChild.Access) (ha : a.PolyTime) : dimension a ∈ FP := by
  have hw := mem_FP_comp ha.dimension BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair hw hw) BinaryNat.mul_mem_FP
  refine mem_FP_of_eq (g := dimension a) h ?_
  intro c
  simp only [Function.comp_apply, dimension]

theorem target_mem_FP (a : FactorChild.Access) (ha : a.PolyTime) : target a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.dimension
    (mem_FP_comp ha.dimension BinaryNat.succ_mem_FP)) BinaryNat.mul_mem_FP
  refine mem_FP_of_eq (g := target a) h ?_
  intro c
  simp only [Function.comp_apply, target]

theorem dimension_code (a : FactorChild.Access) (c : List Bool) (n : ℕ)
    (hd : a.dimension c = BinaryNatCode.encode n) :
    dimension a c = BinaryNatCode.encode ((n + 1) * (n + 1)) := by
  simp only [dimension, hd, BinaryNat.succ_eq_bits, BinaryNat.mul_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem target_code (a : FactorChild.Access) (c : List Bool) (n : ℕ)
    (hd : a.dimension c = BinaryNatCode.encode n) :
    target a c = BinaryNatCode.encode (n * (n + 1)) := by
  simp only [target, hd, BinaryNat.succ_eq_bits, BinaryNat.mul_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]


end LeanCanny.Algebra.Berkowitz.PowerAccessBits
