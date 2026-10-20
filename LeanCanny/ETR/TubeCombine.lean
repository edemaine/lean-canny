/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularAddFP
public import LeanCanny.Computation.SpaceFunctionPair

/-! # FP combination of the four tube coefficient responses

Responses are `pair (pair sourceSquare lowerShift) (pair upperShift sparse)`.
The original context supplies the active mask and positive-modulus predecessor.
Only reduced residues and the saved input are retained.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCombine
open Complexity
open LeanCanny.Encoding
open Algebra.MatrixPower

-- Use the proved scalar specifications without unfolding their machines.
attribute [local irreducible] ArithmeticBits.addMod ArithmeticBits.negate BinaryNat.succ

def squareWord (z : List Bool) : List Bool := pairFst (pairFst (pairSnd z))
def lowerWord (z : List Bool) : List Bool := pairSnd (pairFst (pairSnd z))
def upperWord (z : List Bool) : List Bool := pairFst (pairSnd (pairSnd z))
def sparseWord (z : List Bool) : List Bool := pairSnd (pairSnd (pairSnd z))
def modulus (field : List Bool → List Bool) (z : List Bool) : List Bool := BinaryNat.succ (field (pairFst z))

def lowerTerm (active field : List Bool → List Bool) (z : List Bool) : List Bool :=
  if (active (pairFst z))[0]?.getD false then ArithmeticBits.addMod (pair (modulus field z)
    (pair (squareWord z) (ArithmeticBits.addMod (pair (modulus field z) (pair (lowerWord z) (lowerWord z)))))) else []

def upperTerm (active field : List Bool → List Bool) (z : List Bool) : List Bool :=
  if (active (pairFst z))[1]?.getD false then ArithmeticBits.addMod (pair (modulus field z)
    (pair (squareWord z) (ArithmeticBits.negate (pair (modulus field z)
      (ArithmeticBits.addMod (pair (modulus field z) (pair (upperWord z) (upperWord z)))))))) else []

def finish (active field : List Bool → List Bool) (z : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (modulus field z) (pair
    (ArithmeticBits.addMod (pair (modulus field z) (pair (lowerTerm active field z) (upperTerm active field z)))) (sparseWord z)))

theorem squareWord_mem_FP : squareWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) pairFst_mem_FP
theorem lowerWord_mem_FP : lowerWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) pairSnd_mem_FP
theorem upperWord_mem_FP : upperWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem sparseWord_mem_FP : sparseWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

theorem modulus_mem_FP {field : List Bool → List Bool} (hm : field ∈ FP) : modulus field ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

private theorem add_fields {m a b : List Bool → List Bool} (hm : m ∈ FP) (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => ArithmeticBits.addMod (pair (m z) (pair (a z) (b z)))) ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair hm (mem_FP_pair ha hb)) ArithmeticBits.addMod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem lowerTerm_mem_FP {active field : List Bool → List Bool} (ha : active ∈ FP) (hm : field ∈ FP) : lowerTerm active field ∈ FP := by
  have hmod := modulus_mem_FP hm
  have hd := add_fields hmod lowerWord_mem_FP lowerWord_mem_FP
  have hv := add_fields hmod squareWord_mem_FP hd
  have h := (FPPred.getBit (mem_FP_comp pairFst_mem_FP ha) (UnaryFn.const 0)).ite_mem_FP hv (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun _ => rfl)

theorem upperTerm_mem_FP {active field : List Bool → List Bool} (ha : active ∈ FP) (hm : field ∈ FP) : upperTerm active field ∈ FP := by
  have hmod := modulus_mem_FP hm
  have hd := add_fields hmod upperWord_mem_FP upperWord_mem_FP
  have hn := mem_FP_comp (mem_FP_pair hmod hd) ArithmeticBits.negate_mem_FP
  have hv := add_fields hmod squareWord_mem_FP hn
  have h := (FPPred.getBit (mem_FP_comp pairFst_mem_FP ha) (UnaryFn.const 1)).ite_mem_FP hv (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun _ => rfl)

theorem finish_mem_FP {active field : List Bool → List Bool} (ha : active ∈ FP) (hm : field ∈ FP) : finish active field ∈ FP := by
  have hmod := modulus_mem_FP hm
  have hsum := add_fields hmod (lowerTerm_mem_FP ha hm) (upperTerm_mem_FP ha hm)
  exact add_fields hmod hsum sparseWord_mem_FP

theorem finish_residueBits (active field : List Bool → List Bool) (c : List Bool)
    (A F T Z : ZMod (Nat.fromBitsLE (field c) + 1)) :
    finish active field (pair c (pair (pair (residueBits A) (residueBits F)) (pair (residueBits T) (residueBits Z)))) =
      residueBits ((if (active c)[0]?.getD false then A + (F + F) else 0) +
        (if (active c)[1]?.getD false then A - (T + T) else 0) + Z) := by
  let : NeZero (Nat.fromBitsLE (field c) + 1) := ⟨by omega⟩
  have hm : BinaryNat.succ (field c) = BinaryNatCode.encode (Nat.fromBitsLE (field c) + 1) := by
    rw [BinaryNat.succ_eq_bits]
    rfl
  have hz : ([] : List Bool) = residueBits (0 : ZMod (Nat.fromBitsLE (field c) + 1)) := by simp [residueBits, BinaryNatCode.encode]
  simp only [finish, lowerTerm, upperTerm, modulus, squareWord, lowerWord, upperWord, sparseWord, pairFst_pair, pairSnd_pair, hm]
  split_ifs <;> simp only [hz, ArithmeticBits.addMod_residueBits, ArithmeticBits.negate_residueBits, sub_eq_add_neg]

end LeanCanny.ETR.TubeCombine
