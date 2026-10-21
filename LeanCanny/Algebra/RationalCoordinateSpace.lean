/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateRationalSpaceExponent
public import LeanCanny.Algebra.IntegerPolynomialDegreeSpace

/-! # Native coefficient routines for actual rational-coordinate composition

The common clearing exponent is the actual maximum numerator/denominator
degree. Native coefficient-zero scans compute it from FP upper bounds and
space-bounded residue children. All four coefficient children may use
polynomial space and arbitrary time.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalCoordinateBits
open Polynomial UnivariateRational
open LeanCanny.Encoding LeanCanny.Computation
attribute [local irreducible] BinaryNat.normalize

def maximum (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairFst q) ≤ Nat.fromBitsLE (pairSnd q) then BinaryNat.normalize (pairSnd q)
  else BinaryNat.normalize (pairFst q)

theorem maximum_FP : maximum ∈ FP := by
  have h := (BinaryNat.le_fppred pairFst_mem_FP pairSnd_mem_FP).ite_mem_FP
    (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP) (mem_FP_comp pairFst_mem_FP BinaryNat.normalize_mem_FP)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem maximum_eq (q : List Bool) :
    maximum q = BinaryNatCode.encode (max (Nat.fromBitsLE (pairFst q)) (Nat.fromBitsLE (pairSnd q))) := by
  by_cases h : Nat.fromBitsLE (pairFst q) ≤ Nat.fromBitsLE (pairSnd q)
  · simp only [maximum, ite_eq_left h, BinaryNat.normalize_eq_bits, Nat.max_eq_right h]
    rfl
  · have h' : Nat.fromBitsLE (pairSnd q) ≤ Nat.fromBitsLE (pairFst q) := by omega
    simp only [maximum, ite_eq_right h, BinaryNat.normalize_eq_bits, Nat.max_eq_left h']
    rfl

theorem degreeEvaluator (r : List Bool → Coordinate)
    (N : SpaceFunction (PrimitivePairBits.coefficient (fun c => (r c).numerator)))
    (D : SpaceFunction (PrimitivePairBits.coefficient (fun c => (r c).denominator)))
    (bound mass : List Bool → ℕ) (hB : BinaryFn bound) (hM : BinaryFn mass)
    (hdegree : ∀ c, (r c).degree ≤ bound c)
    (hn : ∀ c, coefficientMass (r c).numerator ≤ 2 ^ mass c)
    (hd : ∀ c, coefficientMass (r c).denominator ≤ 2 ^ mass c) :
    SpaceFunction (fun c => BinaryNatCode.encode (r c).degree) := by
  have EN := IntegerPolynomialBits.degreeEvaluator (fun c => (r c).numerator) N bound mass hB hM
    (fun c => (le_max_left _ _).trans (hdegree c)) hn
  have ED := IntegerPolynomialBits.degreeEvaluator (fun c => (r c).denominator) D bound mass hB hM
    (fun c => (le_max_right _ _).trans (hdegree c)) hd
  have E := (EN.pairOutputs ED).postcompose maximum maximum_FP
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, maximum_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Coordinate.degree]

theorem evaluatorsWithDegree (outer inner : List Bool → Coordinate)
    (E : SpaceFunction (fun c => BinaryNatCode.encode (outer c).degree))
    (ON : SpaceFunction (PrimitivePairBits.coefficient (fun c => (outer c).numerator)))
    (OD : SpaceFunction (PrimitivePairBits.coefficient (fun c => (outer c).denominator)))
    (IN : SpaceFunction (PrimitivePairBits.coefficient (fun c => (inner c).numerator)))
    (ID : SpaceFunction (PrimitivePairBits.coefficient (fun c => (inner c).denominator))) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => ((outer c).comp (inner c)).numerator)) ∧
    SpaceFunction (PrimitivePairBits.coefficient (fun c => ((outer c).comp (inner c)).denominator)) :=
  ⟨UnivariateRationalBits.evaluatorWithExponent _ _ _ _ E ON IN ID,
   UnivariateRationalBits.evaluatorWithExponent _ _ _ _ E OD IN ID⟩

theorem evaluators (outer inner : List Bool → Coordinate)
    (ON : SpaceFunction (PrimitivePairBits.coefficient (fun c => (outer c).numerator)))
    (OD : SpaceFunction (PrimitivePairBits.coefficient (fun c => (outer c).denominator)))
    (IN : SpaceFunction (PrimitivePairBits.coefficient (fun c => (inner c).numerator)))
    (ID : SpaceFunction (PrimitivePairBits.coefficient (fun c => (inner c).denominator)))
    (bound mass : List Bool → ℕ) (hB : BinaryFn bound) (hM : BinaryFn mass)
    (hdegree : ∀ c, (outer c).degree ≤ bound c)
    (hn : ∀ c, coefficientMass (outer c).numerator ≤ 2 ^ mass c)
    (hd : ∀ c, coefficientMass (outer c).denominator ≤ 2 ^ mass c) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => ((outer c).comp (inner c)).numerator)) ∧
    SpaceFunction (PrimitivePairBits.coefficient (fun c => ((outer c).comp (inner c)).denominator)) :=
  evaluatorsWithDegree outer inner (degreeEvaluator outer ON OD bound mass hB hM hdegree hn hd) ON OD IN ID

end LeanCanny.Algebra.RationalCoordinateBits
