/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayAffineDeformation
public import LeanCanny.Algebra.MacaulayPSPACE
public import LeanCanny.Algebra.BerkowitzPolynomialSpace

/-! # Streamed coefficients of the actual Macaulay deformation determinant

An entry has coefficients A at degree zero, I-A at degree one, and zero above.
The original integer source residue routine therefore suffices, including its
space-bounded states. No oracle for deformed source coefficients is assumed.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayDeformationBits

open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open MatrixPower

/-- Polynomial-entry query: context, row, column, parameter degree. -/
def packet (q : List Bool) (r s D : ℕ) : List Bool :=
  pair q (pair (BinaryNatCode.encode r) (pair (BinaryNatCode.encode s) (BinaryNatCode.encode D)))

def originalQuery (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (pairFst (pairSnd p)) (pairFst (pairSnd (pairSnd p))))

def target (p : List Bool) : List Bool := pairSnd (pairSnd (pairSnd p))
def modulus (p : List Bool) : List Bool := BinaryNat.succ (pairSnd (pairFst p))

theorem originalQuery_mem_FP : originalQuery ∈ FP := by
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hj := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair hi hj)

theorem target_mem_FP : target ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

theorem modulus_mem_FP : modulus ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP

def diagonal (p : List Bool) : List Bool := MacaulayBits.identityEntry (originalQuery p)

theorem diagonal_mem_FP : diagonal ∈ FP := mem_FP_comp originalQuery_mem_FP MacaulayBits.identityEntry_mem_FP

def negative (z : List Bool) : List Bool := ArithmeticBits.negate (pair (modulus (pairFst z)) (pairSnd z))

theorem negative_mem_FP : negative ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP modulus_mem_FP
  have hq := mem_FP_pair hm pairSnd_mem_FP
  have hn := mem_FP_comp hq ArithmeticBits.negate_mem_FP
  refine mem_FP_of_eq (g := negative) hn ?_
  intro z
  simp only [Function.comp_apply, negative]

def linearCoefficient (z : List Bool) : List Bool := ArithmeticBits.combine
  (pair (modulus (pairFst z)) (pair (diagonal (pairFst z))
    (pair (negative z) (ArithmeticBits.one (modulus (pairFst z))))))

theorem linearCoefficient_mem_FP : linearCoefficient ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP modulus_mem_FP
  have hd := mem_FP_comp pairFst_mem_FP diagonal_mem_FP
  have ho := mem_FP_comp hm ArithmeticBits.one_mem_FP
  have hq := mem_FP_pair hm (mem_FP_pair hd (mem_FP_pair negative_mem_FP ho))
  have hf := mem_FP_comp hq ArithmeticBits.combine_mem_FP
  refine mem_FP_of_eq (g := linearCoefficient) hf ?_
  intro z
  simp only [Function.comp_apply, linearCoefficient]

def finish (z : List Bool) : List Bool :=
  if BinaryNat.normalize (target (pairFst z)) = [] then pairSnd z
  else if BinaryNat.normalize (target (pairFst z)) = [true] then linearCoefficient z else []

theorem finish_mem_FP : finish ∈ FP := by
  have ht := mem_FP_comp (mem_FP_comp pairFst_mem_FP target_mem_FP) BinaryNat.normalize_mem_FP
  have h1 := (stringEq_fppred ht (constFn_mem_FP [true])).ite_mem_FP linearCoefficient_mem_FP (constFn_mem_FP [])
  have hf := (stringEq_fppred ht (constFn_mem_FP [])).ite_mem_FP pairSnd_mem_FP h1
  exact mem_FP_of_eq (g := finish) hf (fun _ => rfl)

theorem originalQuery_packet (q : List Bool) (r s D : ℕ) :
    originalQuery (packet q r s D) = MacaulayBits.packet q r s := by
  simp only [originalQuery, packet, pairFst_pair, pairSnd_pair, MacaulayBits.packet]

theorem modulus_packet (q : List Bool) (r s D : ℕ) :
    modulus (packet q r s D) = BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) + 1) := by
  simp only [modulus, packet, pairFst_pair, BinaryNat.succ_eq_bits]
  rfl

theorem finish_packet (q : List Bool) (r s D : ℕ) (x : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) :
    finish (pair (packet q r s D) (residueBits x)) = residueBits
      (if D = 0 then x else if D = 1 then (if r = s then 1 else 0) - x else 0) := by
  let m := Nat.fromBitsLE (pairSnd q) + 1
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  have ht : target (packet q r s D) = BinaryNatCode.encode D := by
    simp only [target, packet, pairSnd_pair]
  simp only [finish, pairFst_pair, pairSnd_pair, ht, BinaryNat.normalize_eq_bits,
    MacaulayBits.fromBits_encode, BinaryNat.bits_eq_nil_iff]
  by_cases h0 : D = 0
  · simp only [h0, ite_true]
  · rw [ite_eq_right h0, ite_eq_right h0]
    have h1 : D.bits = [true] ↔ D = 1 := by
      change BinaryNatCode.encode D = BinaryNatCode.encode 1 ↔ D = 1
      exact BinaryNatCode.encode_injective.eq_iff
    simp only [h1]
    by_cases hD : D = 1
    · rw [ite_eq_left hD, ite_eq_left hD]
      simp only [linearCoefficient, negative, diagonal, pairFst_pair, pairSnd_pair,
        originalQuery_packet, MacaulayBits.identityEntry_packet, modulus_packet,
        ArithmeticBits.negate_residueBits, ArithmeticBits.one_residueBits, ArithmeticBits.combine_residueBits]
      congr 1
      ring
    · rw [ite_eq_right hD, ite_eq_right hD]
      simp [residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.MacaulayDeformationBits
