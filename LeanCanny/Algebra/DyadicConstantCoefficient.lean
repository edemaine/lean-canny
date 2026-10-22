/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairReaders
public import LeanCanny.Encoding.BinaryPowModFP
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native residues of dyadic integer constants

Binary exponents are sent directly to modular exponentiation. The integer
constant and its full binary expansion are never constructed by the reader.
-/

@[expose] public section
namespace LeanCanny.Algebra.DyadicConstantBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)
attribute [local irreducible] BinaryNat.powMod

/-- A selected positive-degree coefficient of a constant polynomial is zero. -/
def value (E : List Bool → ℕ) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (selectedDegree q) = 0 then
    BinaryNat.powMod (pair (BinaryNatCode.encode 2)
      (pair (BinaryNatCode.encode (E (context q))) (pairSnd q)))
  else []

theorem degreeZero_pred : FPPred (fun q => Nat.fromBitsLE (selectedDegree q) = 0) :=
  (BinaryNat.le_fppred RationalSubstitution.IntegerBits.selectedDegree_mem_FP (constFn_mem_FP [])).of_iff
    (fun q => by
      change Nat.fromBitsLE (selectedDegree q) ≤ 0 ↔ Nat.fromBitsLE (selectedDegree q) = 0
      omega)

theorem value_FP {E : List Bool → ℕ} (hE : BinaryFn E) : value E ∈ FP := by
  have he := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP hE.bits_mem_FP
  have hp := mem_FP_comp (mem_FP_pair (constFn_mem_FP (BinaryNatCode.encode 2))
    (mem_FP_pair he pairSnd_mem_FP)) BinaryNat.powMod_mem_FP
  have H := degreeZero_pred.ite_mem_FP hp (constFn_mem_FP [])
  refine mem_FP_of_eq H (fun q => ?_)
  simp only [value, Function.comp_apply]

theorem value_eq (E : List Bool → ℕ) (q : List Bool) :
    value E q = PrimitivePairBits.coefficient (fun c => C ((2 ^ E c : ℕ) : ℤ)) q := by
  let _ : NeZero (mValue q) := ⟨by dsimp [mValue]; omega⟩
  unfold value PrimitivePairBits.coefficient
  rw [Polynomial.coeff_C]
  by_cases hk : Nat.fromBitsLE (selectedDegree q) = 0
  · simp only [hk, ite_true, BinaryNat.powMod_eq_bits, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, coefficientResidue, residueBits,
      Int.cast_natCast, ZMod.val_natCast]
  · simp only [hk, ite_false, coefficientResidue, Int.cast_zero, residueBits, ZMod.val_zero]
    rfl

theorem coefficient_FP {E : List Bool → ℕ} (hE : BinaryFn E) :
    PrimitivePairBits.coefficient (fun c => C ((2 ^ E c : ℕ) : ℤ)) ∈ FP :=
  mem_FP_of_eq (value_FP hE) (value_eq E)

theorem coefficientEvaluator {E : List Bool → ℕ} (hE : BinaryFn E) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => C ((2 ^ E c : ℕ) : ℤ))) :=
  SpaceFunction.ofFP _ (coefficient_FP hE)

theorem oneCoefficient_FP : PrimitivePairBits.coefficient (fun _ => (1 : ℤ[X])) ∈ FP := by
  simpa only [pow_zero, Nat.cast_one, Polynomial.C_1] using coefficient_FP (BinaryFn.const 0)

theorem oneCoefficientEvaluator : SpaceFunction (PrimitivePairBits.coefficient (fun _ => (1 : ℤ[X]))) :=
  SpaceFunction.ofFP _ oneCoefficient_FP

end LeanCanny.Algebra.DyadicConstantBits
