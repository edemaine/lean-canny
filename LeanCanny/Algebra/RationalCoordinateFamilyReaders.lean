/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalCoordinateFamily
public import LeanCanny.Algebra.FixedWidthRationalSubstitutionSpace

/-! # Native substitution readers for rational parent families -/

@[expose] public section
namespace LeanCanny.Algebra.RationalCoordinateFamily
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
attribute [local irreducible] PrimitivePairBits.coefficient

noncomputable def numerator (F : Family) (u : List Bool) (i : ℕ) : Polynomial ℤ :=
  (F.coordinate (pair u (BinaryNatCode.encode i))).numerator
noncomputable def denominator (F : Family) (u : List Bool) (i : ℕ) : Polynomial ℤ :=
  (F.coordinate (pair u (BinaryNatCode.encode i))).denominator

def readerQuery (q : List Bool) : List Bool :=
  pair (pair (pair (RationalSubstitution.IntegerBits.context q)
    (pairFst (RationalSubstitution.IntegerBits.selectedDegree q)))
      (pairSnd (RationalSubstitution.IntegerBits.selectedDegree q))) (pairSnd q)

theorem readerQuery_FP : readerQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP
    (mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairFst_mem_FP))
      (mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def readers {F : Family} (A : Access F) (arity : List Bool → ℕ) :
    RationalSubstitution.IntegerBits.CoordinateReaders arity (numerator F) (denominator F) where
  numerator := PrimitivePairBits.coefficient (fun u => (F.coordinate u).numerator) ∘ readerQuery
  denominator := PrimitivePairBits.coefficient (fun u => (F.coordinate u).denominator) ∘ readerQuery
  numeratorEvaluator := A.numerator.precompose readerQuery readerQuery_FP
  denominatorEvaluator := A.denominator.precompose readerQuery readerQuery_FP
  numerator_eq c i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.coefficientResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [readerQuery, RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [readerQuery, RationalSubstitution.IntegerBits.mValue, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  denominator_eq c i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.coefficientResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [readerQuery, RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [readerQuery, RationalSubstitution.IntegerBits.mValue, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)

end LeanCanny.Algebra.RationalCoordinateFamily
