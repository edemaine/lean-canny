/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairReaders
public import LeanCanny.Algebra.IntegerSignumSpace
public import LeanCanny.Algebra.PolynomialDegreeSpace
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Actual degrees from arbitrary integer coefficient-residue routines

FP degree and coefficient-mass upper bounds suffice. Source residue access
may take arbitrary time in polynomial space, and zero polynomials are included.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerPolynomialBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation

noncomputable def value (p : List Bool → ℤ[X]) (q : List Bool) : ℤ :=
  (p (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q))

theorem signEvaluator (p : List Bool → ℤ[X]) (P : SpaceFunction (PrimitivePairBits.coefficient p))
    (b : List Bool → ℕ) (hb : BinaryFn b) (hbound : ∀ c, coefficientMass (p c) ≤ 2 ^ b c) :
    SpaceFunction (fun q => if value p q = 0 then [] else if value p q < 0 then [true] else [false, true]) := by
  let budget q := BinaryNatCode.encode (b (pairFst q) + 1)
  have hbudget : budget ∈ FP := mem_FP_of_eq
    (mem_FP_comp pairFst_mem_FP (hb.add (BinaryFn.const 1)).bits_mem_FP) (fun _ => rfl)
  apply IntegerSignumBits.evaluator P budget hbudget (value p)
  · intro q
    have h := Nat.size_le_size ((coeff_natAbs_le_coefficientMass (p (pairFst q)) (Nat.fromBitsLE (pairSnd q))).trans (hbound _))
    simpa only [value, budget, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.size_pow] using h
  · intro q m hm
    simp only [PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
    rfl

private theorem sign_zero_iff (z : ℤ) :
    (if z = 0 then ([] : List Bool) else if z < 0 then [true] else [false, true]) = [] ↔ z = 0 := by
  by_cases hz : z = 0 <;> by_cases hn : z < 0 <;> simp [hz, hn]

theorem degreeEvaluator (p : List Bool → ℤ[X]) (P : SpaceFunction (PrimitivePairBits.coefficient p))
    (D b : List Bool → ℕ) (hD : BinaryFn D) (hb : BinaryFn b)
    (hdegree : ∀ c, (p c).natDegree ≤ D c) (hbound : ∀ c, coefficientMass (p c) ≤ 2 ^ b c) :
    SpaceFunction (fun c => BinaryNatCode.encode (p c).natDegree) := by
  apply PolynomialDegreeBits.degreeEvaluator (signEvaluator p P b hb hbound)
    (fun c => BinaryNatCode.encode (D c)) hD.bits_mem_FP p
  · intro c
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using hdegree c
  · intro c i
    rw [sign_zero_iff]
    simp only [value, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Algebra.IntegerPolynomialBits
