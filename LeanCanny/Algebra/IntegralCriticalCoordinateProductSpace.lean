/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalGradientSpace
public import LeanCanny.Algebra.FixedWidthCoordinateMulSpace

/-! # Native spatial-coordinate multiples of actual cleared gradients

The exponent-decrement query changes only the requested spatial monomial.
The saved source and free derivative rank remain intact. These are the
actual X_j*g_j terms needed by integral Euler elimination, computed from
the original coefficient, retained-height, and denominator readers.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalCoordinateProductBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalGradientBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def arity (S : Source) (z : List Bool) : ℕ := S.free (pairFst z)
def width (S : Source) (z : List Bool) : ℕ := S.targetWidth (pairFst z)
def selected (z : List Bool) : ℕ := Nat.fromBitsLE (pairFst (pairSnd z))
def targetWord (z : List Bool) : List Bool := pairSnd (pairSnd z)

def gradientQuery (q : List Bool) : List Bool :=
  pair (pairFst (pairFst q)) (pair (pairFst (pairSnd (pairFst q))) (pairSnd q))

theorem gradientQuery_FP : gradientQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP) pairSnd_mem_FP)

noncomputable def value (S : Source) : List Bool → List Bool :=
  FixedWidthCoordinateMulBits.value (arity S) (width S) selected targetWord
    ((family S).value ∘ gradientQuery)

theorem evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) : SpaceFunction (value S) :=
  FixedWidthCoordinateMulBits.evaluator (arity S) (width S) selected targetWord
    ((IntegralCriticalGradientBits.evaluator S a EC EH EQ).precompose gradientQuery gradientQuery_FP)
    (a.free.comp pairFst_mem_FP) (a.targetWidth.comp pairFst_mem_FP)
    (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

theorem packet (S : Source) (c : List Bool) (j : Fin (S.free c)) (e : ℕ) :
    letI := S.ring c
    value S (pair c (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))) =
      residueBits ((Algebra.leftMulMatrix (S.basis c)
        ((MvPolynomial.X j * polynomial S c j).coeff (RationalSubstitution.Indexed.exponentVector (S.free c)
          (FixedWidthPolynomial.entry (S.targetWidth c) e))) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  let z := pair c (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))
  let extract := IntegralPurePowerReductionBits.coefficientHom (S.basis c) (S.row c) (S.col c)
  have HA : arity S z = S.free c := by simp only [arity, z, pairFst_pair]
  have HS : selected z = j.val := by
    simp only [selected, z, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HC (r : ℕ) : ((family S).value ∘ gradientQuery) (pair z (BinaryNatCode.encode r)) =
      residueBits ((extract ((polynomial S c j).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (S.free c))) (width S z) r)) : ℤ) : ZMod (S.modulus c)) := by
    simp only [Function.comp_apply, gradientQuery, z, pairFst_pair, pairSnd_pair]
    rw [FixedWidthPolynomial.nativeExponent_refl]
    simp only [width, pairFst_pair]
    dsimp only [extract, IntegralPurePowerReductionBits.coefficientHom]
    exact IntegralCriticalGradientBits.packet S c j r
  have H := FixedWidthCoordinateMulBits.packet (arity S) (width S) selected targetWord
    (Equiv.refl (Fin (S.free c))) extract ((family S).value ∘ gradientQuery) z
    (polynomial S c j) j (S.modulus c) HA HS HC
  have HE : FixedWidthDerivativeBits.exponent (width S) targetWord (Equiv.refl (Fin (S.free c))) z =
      RationalSubstitution.Indexed.exponentVector (S.free c) (FixedWidthPolynomial.entry (S.targetWidth c) e) := by
    apply Finsupp.ext
    intro i
    simp only [FixedWidthDerivativeBits.exponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply,
      FixedWidthQuery.coordinate_eq_entry, width, targetWord, z, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl
  rw [HE] at H
  exact H

end LeanCanny.Algebra.IntegralCriticalCoordinateProductBits
