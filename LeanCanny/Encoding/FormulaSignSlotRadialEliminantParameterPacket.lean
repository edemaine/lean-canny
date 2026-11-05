/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterCoefficient
/-! # The original row frontend satisfies the literal Macaulay source ABI -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterCoefficient
open LeanCanny.Algebra MatrixPower
open FormulaSignSlotRadialEliminantParameterQuery
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] value FormulaSignSlotRadialEliminantPacked.system

private noncomputable def assemble (n W : List Bool → ℕ)
    (Q : (c : List Bool) → Fin (n c + 1) → MvPolynomial (Fin (n c + 1)) (Polynomial ℤ))
    (c m row spatial parameter : List Bool) : List Bool :=
  residueBits (((((Q c ⟨min (Nat.fromBitsLE row) (n c),
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩).coeff
      (RationalSubstitution.Indexed.exponentVector (n c + 1)
        (FixedWidthPolynomial.entry (W c) (Nat.fromBitsLE spatial)))).coeff
      (Nat.fromBitsLE parameter)) : ℤ) : ZMod (Nat.fromBitsLE m + 1))

attribute [local irreducible] assemble

private theorem assemble_packet (n W : List Bool → ℕ)
    (Q : (c : List Bool) → Fin (n c + 1) → MvPolynomial (Fin (n c + 1)) (Polynomial ℤ))
    (c m : List Bool) (i : Fin (n c + 1)) (r k : ℕ) :
    assemble n W Q c m (BinaryNatCode.encode i.val) (BinaryNatCode.encode r) (BinaryNatCode.encode k) =
      residueBits (((((Q c i).coeff (RationalSubstitution.Indexed.exponentVector (n c + 1)
        (FixedWidthPolynomial.entry (W c) r))).coeff k) : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  have HI : i.val ≤ n c := by have := i.isLt; omega
  simp only [assemble, BinaryNatCode.encode, Nat.fromBitsLE_bits, min_eq_left HI]

private noncomputable def rawValue (n W : List Bool → ℕ)
    (Q : (c : List Bool) → Fin (n c + 1) → MvPolynomial (Fin (n c + 1)) (Polynomial ℤ))
    (q : List Bool) : List Bool :=
  assemble n W Q (context q) (modulus q) (rowWord q) (spatialWord q) (parameterWord q)

private theorem rawValue_packet (n W : List Bool → ℕ)
    (Q : (c : List Bool) → Fin (n c + 1) → MvPolynomial (Fin (n c + 1)) (Polynomial ℤ))
    (z : List Bool) (i : Fin (n (pairFst z) + 1)) (r k : ℕ) :
    rawValue n W Q (pair z (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode r) (BinaryNatCode.encode k)))) =
      residueBits (((((Q (pairFst z) i).coeff
        (RationalSubstitution.Indexed.exponentVector (n (pairFst z) + 1)
          (FixedWidthPolynomial.entry (W (pairFst z)) r))).coeff k) : ℤ) :
            ZMod (Nat.fromBitsLE (pairSnd z) + 1)) := by
  simp only [rawValue, context, modulus, rowWord, spatialWord, parameterWord, pairFst_pair, pairSnd_pair]
  exact assemble_packet n W Q _ _ i r k

private theorem value_eq_rawValue : value = rawValue
    FormulaSignSlotRadialEliminantPackingLayout.spatial FormulaSignSlotRadialEliminantPackingLayout.width
    FormulaSignSlotRadialEliminantPacked.system := by
  funext q
  rw [correct]
  simp only [rawValue, assemble, row, spatialExponent, FixedWidthPolynomial.nativeExponent_refl,
    spatial, macroWidth]
  rfl

theorem source_packet (z : List Bool)
    (i : Fin (FormulaSignSlotRadialEliminantPackingLayout.spatial (pairFst z) + 1)) (r k : ℕ) :
    value (pair z (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode k)))) =
      residueBits (((((FormulaSignSlotRadialEliminantPacked.system (pairFst z) i).coeff
        (RationalSubstitution.Indexed.exponentVector
          (FormulaSignSlotRadialEliminantPackingLayout.spatial (pairFst z) + 1)
          (FixedWidthPolynomial.entry (FormulaSignSlotRadialEliminantPackingLayout.width (pairFst z)) r))).coeff k) : ℤ) :
            ZMod (Nat.fromBitsLE (pairSnd z) + 1)) := by
  rw [value_eq_rawValue]
  exact rawValue_packet _ _ _ z i r k

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterCoefficient
