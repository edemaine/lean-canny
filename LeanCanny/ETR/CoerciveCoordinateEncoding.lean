/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveSymbolicBounds
public import LeanCanny.Algebra.BivariateRationalSubstitutionEncoding
public import LeanCanny.Computation.SpaceFunction
public import LeanCanny.Algebra.DyadicSpecializationSpace

/-! # Native Kronecker access from actual prepared coordinate readers -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveCoordinateEncoding
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open CoerciveSourceSampling CoercivePreparationControls CoerciveSymbolicSampling CoerciveSymbolicBounds
open Polynomial
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix
attribute [local irreducible] CoercivePreparationControls.referenceExponent CoerciveSymbolicBounds.queryDegree

structure Readers where
  numerator : List Bool → List Bool
  denominator : List Bool → List Bool
  numerator_eq : ∀ bits (i : Fin (dimension bits + 1)) j k m, 0 < m → numerator
    (pair (pair bits (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))))
      (BinaryNatCode.encode (m - 1))) =
        DyadicBits.integerResidue ((((family bits).fixedCoordinate i).numerator.coeff j).coeff k) m
  denominator_eq : ∀ bits (i : Fin (dimension bits + 1)) j k m, 0 < m → denominator
    (pair (pair bits (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))))
      (BinaryNatCode.encode (m - 1))) =
        DyadicBits.integerResidue ((((family bits).fixedCoordinate i).denominator.coeff j).coeff k) m
  numerator_space : SpaceFunction numerator
  denominator_space : SpaceFunction denominator

noncomputable def radix (bits : List Bool) : ℕ := queryDegree bits + 1
noncomputable def radixCode (bits : List Bool) : List Bool := BinaryNatCode.encode (radix bits)

theorem radixCode_FP : radixCode ∈ FP := (queryDegree_binary.add (BinaryFn.const 1)).bits_mem_FP

theorem reference_le_queryDegree (bits : List Bool) : referenceExponent bits ≤ queryDegree bits := by
  have ha : 1 ≤ allowance bits := by unfold allowance; omega
  have hc : 1 ≤ 2 * (dimension bits + 1) * allowance bits := by
    exact (show 1 ≤ 2 * (dimension bits + 1) by omega) |>.trans
      (Nat.le_mul_of_pos_right _ (by omega))
  unfold queryDegree
  simpa only [one_mul] using Nat.mul_le_mul_right (referenceExponent bits) hc

noncomputable def request (input index degree modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  pair (pair (input c) (pair (BinaryNat.normalize (index c))
    (pair (BinaryNat.div (pair (degree c) (radixCode (input c))))
      (BinaryNat.mod (pair (degree c) (radixCode (input c))))))) (BinaryNat.normalize (modulus c))

theorem request_FP {input index degree modulus : List Bool → List Bool}
    (hi : input ∈ FP) (hj : index ∈ FP) (hd : degree ∈ FP) (hm : modulus ∈ FP) :
    request input index degree modulus ∈ FP := by
  have hr := mem_FP_comp hi radixCode_FP
  have hp := mem_FP_pair hd hr
  have h := mem_FP_pair (mem_FP_pair hi (mem_FP_pair (mem_FP_comp hj BinaryNat.normalize_mem_FP)
    (mem_FP_pair (mem_FP_comp hp BinaryNat.div_mem_FP) (mem_FP_comp hp BinaryNat.mod_mem_FP))))
    (mem_FP_comp hm BinaryNat.normalize_mem_FP)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem request_eq (input index degree modulus : List Bool → List Bool) (c : List Bool) :
    request input index degree modulus c =
      pair (pair (input c) (pair (BinaryNatCode.encode (Nat.fromBitsLE (index c)))
        (pair (BinaryNatCode.encode (Nat.fromBitsLE (degree c) / radix (input c)))
          (BinaryNatCode.encode (Nat.fromBitsLE (degree c) % radix (input c))))))
        (BinaryNatCode.encode (Nat.fromBitsLE (modulus c))) := by
  simp only [request, BinaryNat.normalize_eq_bits, BinaryNat.div_pair, BinaryNat.mod_pair,
    radixCode, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def numerator (R : Readers) (input index degree modulus : List Bool → List Bool) :=
  R.numerator ∘ request input index degree modulus
noncomputable def denominator (R : Readers) (input index degree modulus : List Bool → List Bool) :=
  R.denominator ∘ request input index degree modulus

theorem numerator_evaluator (R : Readers) {input index degree modulus : List Bool → List Bool}
    (hi : input ∈ FP) (hj : index ∈ FP) (hd : degree ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (numerator R input index degree modulus) := R.numerator_space.precompose _ (request_FP hi hj hd hm)

theorem denominator_evaluator (R : Readers) {input index degree modulus : List Bool → List Bool}
    (hi : input ∈ FP) (hj : index ∈ FP) (hd : degree ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (denominator R input index degree modulus) := R.denominator_space.precompose _ (request_FP hi hj hd hm)

theorem numerator_eq (R : Readers) (input index degree modulus : List Bool → List Bool)
    (c : List Bool) (i : Fin (dimension (input c) + 1)) (hi : Nat.fromBitsLE (index c) = i.val) :
    numerator R input index degree modulus c = DyadicBits.integerResidue
      ((PolynomialKronecker.encode (radix (input c)) ((family (input c)).fixedCoordinate i).numerator).coeff
        (Nat.fromBitsLE (degree c))) (Nat.fromBitsLE (modulus c) + 1) := by
  rw [numerator, Function.comp_apply, request_eq, hi]
  have h := R.numerator_eq (input c) i (Nat.fromBitsLE (degree c) / radix (input c))
    (Nat.fromBitsLE (degree c) % radix (input c)) (Nat.fromBitsLE (modulus c) + 1) (by omega)
  rw [Nat.add_sub_cancel_right] at h
  have hB : (family (input c)).exponent < radix (input c) := by
    simpa only [referenceExponent, radix] using
      lt_of_le_of_lt (reference_le_queryDegree (input c)) (Nat.lt_succ_self (queryDegree (input c)))
  have hc := (family (input c)).coordinate_numerator_encoded (radix (input c)) hB i (Nat.fromBitsLE (degree c))
  rw [h, hc]

theorem denominator_eq (R : Readers) (input index degree modulus : List Bool → List Bool)
    (c : List Bool) (i : Fin (dimension (input c) + 1)) (hi : Nat.fromBitsLE (index c) = i.val) :
    denominator R input index degree modulus c = DyadicBits.integerResidue
      ((PolynomialKronecker.encode (radix (input c)) ((family (input c)).fixedCoordinate i).denominator).coeff
        (Nat.fromBitsLE (degree c))) (Nat.fromBitsLE (modulus c) + 1) := by
  rw [denominator, Function.comp_apply, request_eq, hi]
  have h := R.denominator_eq (input c) i (Nat.fromBitsLE (degree c) / radix (input c))
    (Nat.fromBitsLE (degree c) % radix (input c)) (Nat.fromBitsLE (modulus c) + 1) (by omega)
  rw [Nat.add_sub_cancel_right] at h
  have hB : (family (input c)).exponent < radix (input c) := by
    simpa only [referenceExponent, radix] using
      lt_of_le_of_lt (reference_le_queryDegree (input c)) (Nat.lt_succ_self (queryDegree (input c)))
  have hc := (family (input c)).coordinate_denominator_encoded (radix (input c)) hB i (Nat.fromBitsLE (degree c))
  rw [h, hc]

end LeanCanny.ETR.CoerciveCoordinateEncoding
