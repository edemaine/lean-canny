/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateRationalComposition
public import LeanCanny.Algebra.PrimitivePairReaders
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native streamed coefficients of denominator-cleared univariate substitution

One indexed variable specializes the existing modular rational-substitution
evaluator. The exponent and term count stay binary. Every source coefficient
routine may take arbitrary time in polynomial space.
-/

@[expose] public section

namespace LeanCanny.Algebra.UnivariateRationalBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue)
attribute [local irreducible] BinaryNat.normalize

noncomputable def family (p n d : List Bool → ℤ[X]) (e : List Bool → ℕ) : RationalSubstitution.IntegerBits.Family where
  arity _ := 1
  width := e
  terms c := e c + 1
  exponent _ r _ := r
  coefficient c r := (p c).coeff r
  numerator c _ := n c
  denominator c _ := d c
  exponent_le _ _ hr _ _ := by omega

theorem family_polynomial (p n d : List Bool → ℤ[X]) (e : List Bool → ℕ) (c : List Bool) :
    (family p n d e).polynomial c = UnivariateRational.clear (e c) (p c) (n c) (d c) := by
  simp only [RationalSubstitution.IntegerBits.Family.polynomial, family, RationalSubstitution.Indexed.cleared,
    Finset.prod_range_one, UnivariateRational.clear, mul_assoc]

def coordinateQuery (q : List Bool) : List Bool :=
  LeanCanny.pair (LeanCanny.pair (context q) (pairSnd (selectedDegree q))) (pairSnd q)

theorem coordinateQuery_FP : coordinateQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP
    (mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def access (p n d : List Bool → ℤ[X]) (e : List Bool → ℕ) :
    RationalSubstitution.IntegerBits.Access (family p n d e) where
  arity _ := BinaryNatCode.encode 1
  width c := BinaryNatCode.encode (e c)
  terms c := BinaryNatCode.encode (e c + 1)
  exponent q := BinaryNat.normalize (pairFst (pairSnd q))
  coefficient := PrimitivePairBits.coefficient p
  numerator := PrimitivePairBits.coefficient n ∘ coordinateQuery
  denominator := PrimitivePairBits.coefficient d ∘ coordinateQuery
  arity_eq _ := rfl
  width_eq _ := Nat.fromBitsLE_bits _
  terms_eq _ := Nat.fromBitsLE_bits _
  exponent_eq _ _ _ _ _ := by
    simp only [pairSnd_pair, pairFst_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl
  coefficient_eq c r _ m hm := by
    simp only [PrimitivePairBits.coefficient, context, selectedDegree, mValue, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
    rfl
  numerator_eq c i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, coordinateQuery, context, selectedDegree, mValue,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
    rfl
  denominator_eq c i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, coordinateQuery, context, selectedDegree, mValue,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
    rfl

theorem access_controls (p n d : List Bool → ℤ[X]) (e : List Bool → ℕ) (he : BinaryFn e) :
    (access p n d e).ControlsPolyTime := by
  have hx : (fun q => BinaryNat.normalize (pairFst (pairSnd q))) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) BinaryNat.normalize_mem_FP) (fun _ => rfl)
  exact ⟨constFn_mem_FP (BinaryNatCode.encode 1), he.bits_mem_FP, (he.add (BinaryFn.const 1)).bits_mem_FP, hx⟩

theorem evaluator (p n d : List Bool → ℤ[X]) (e : List Bool → ℕ) (he : BinaryFn e)
    (P : SpaceFunction (PrimitivePairBits.coefficient p)) (N : SpaceFunction (PrimitivePairBits.coefficient n))
    (D : SpaceFunction (PrimitivePairBits.coefficient d)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => UnivariateRational.clear (e c) (p c) (n c) (d c))) := by
  have E := RationalSubstitution.IntegerBits.Access.evaluator (access p n d e) (access_controls p n d e he)
    P (N.precompose coordinateQuery coordinateQuery_FP) (D.precompose coordinateQuery coordinateQuery_FP)
  refine E.congr (funext fun q => ?_)
  change PrimitivePairBits.coefficient (family p n d e).polynomial q = _
  simp only [PrimitivePairBits.coefficient, family_polynomial]

end LeanCanny.Algebra.UnivariateRationalBits
