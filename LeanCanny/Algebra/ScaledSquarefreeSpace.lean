/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SquarefreeGCDSpace
public import LeanCanny.Algebra.ScaledSquarefree
public import LeanCanny.Algebra.ScaledPolynomialQuotientSpace

/-! # Complete native coefficient computation for square-free preprocessing

First compute the derivative GCD degree. A prepared context retains it while
the quotient determinant calls the GCD coefficient determinant and original
polynomial reader. All children may use arbitrary time in polynomial space.
-/

@[expose] public section

namespace LeanCanny.Algebra.SeparableBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open PrincipalCoefficientBits (integerResidue)
attribute [local irreducible] BinaryNat.normalize BinaryNat.sub

noncomputable def quotientSource (F : Family) : ScaledQuotientBits.Family where
  divisor c := ScaledSquarefree.gcd (F.polynomial (pairFst c))
  dividend c := F.polynomial (pairFst c)
  divisorDegree c := Nat.fromBitsLE (pairSnd c)
  quotientDegree c := (F.polynomial (pairFst c)).natDegree - Nat.fromBitsLE (pairSnd c)

noncomputable def quotientAccess (F : Family) (A : Readers F) : ScaledQuotientBits.Access (quotientSource F) where
  divisorDegree := BinaryNat.normalize ∘ pairSnd
  quotientDegree c := BinaryNat.sub (pair (A.degree (pairFst c)) (BinaryNat.normalize (pairSnd c)))
  divisorCoefficient := PolynomialGCDBits.value (resultantFamily F) ∘ PrincipalCoefficientBits.sourceQuery
  dividendCoefficient := A.coefficient ∘ PrincipalCoefficientBits.sourceQuery
  divisorDegree_eq c := BinaryNat.normalize_eq_bits _
  quotientDegree_eq c := by
    simp only [A.degree_eq, BinaryNat.sub_pair, BinaryNat.normalize_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, quotientSource]
  divisor_eq q k := by
    simp only [Function.comp_apply, PolynomialGCDBits.value, PrincipalCoefficientBits.sourceQuery,
      PolynomialGCDBits.context, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      resultantFamily, quotientSource, ScaledSquarefree.gcd]
  dividend_eq q k := by
    simp only [Function.comp_apply, PrincipalCoefficientBits.sourceQuery, pairFst_pair, pairSnd_pair]
    have h := A.coefficient_eq (pair (pairFst (pairFst q)) (pairSnd q)) k
    change _ = integerResidue ((F.polynomial (pairFst (pair (pairFst (pairFst q)) (pairSnd q)))).coeff k)
      (Nat.fromBitsLE (pairSnd (pair (pairFst (pairFst q)) (pairSnd q))) + 1) at h
    rw [pairFst_pair, pairSnd_pair] at h
    exact h

theorem quotientAccess_controls (F : Family) (A : Readers F) : (quotientAccess F A).ControlsPolyTime := by
  have hd := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  have hL := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP A.degreeFP) hd) BinaryNat.sub_mem_FP
  have hL' : (fun c => BinaryNat.sub (pair (A.degree (pairFst c)) (BinaryNat.normalize (pairSnd c)))) ∈ FP :=
    mem_FP_of_eq hL (fun _ => rfl)
  exact ⟨hd, hL'⟩

def squarefreeRequest (z : List Bool) : List Bool :=
  pair (pair (pair (ScaledQuotientBits.context (pairFst z)) (pairSnd z))
    (ScaledQuotientBits.modulusWord (pairFst z))) (pairSnd (pairFst z))

theorem squarefreeRequest_FP : squarefreeRequest ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP ScaledQuotientBits.context_FP
  have hm := mem_FP_comp pairFst_mem_FP ScaledQuotientBits.modulusWord_FP
  have hk := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair hc pairSnd_mem_FP) hm) hk

noncomputable def squarefreeValue (F : Family) (q : List Bool) : List Bool :=
  integerResidue ((ScaledSquarefree.polynomial (F.polynomial (ScaledQuotientBits.context q))).coeff
    (Nat.fromBitsLE (pairSnd q))) (ScaledQuotientBits.modulus q)

theorem squarefreeEvaluator (F : Family) (A : Readers F) : SpaceFunction (squarefreeValue F) := by
  have P : SpaceFunction (quotientAccess F A).divisorCoefficient := by
    simpa only [quotientAccess] using (gcdRepresentativeEvaluator F A).precompose
      PrincipalCoefficientBits.sourceQuery PrincipalCoefficientBits.sourceQuery_mem_FP
  have Q : SpaceFunction (quotientAccess F A).dividendCoefficient := by
    simpa only [quotientAccess] using A.evaluator.precompose
      PrincipalCoefficientBits.sourceQuery PrincipalCoefficientBits.sourceQuery_mem_FP
  have E := ScaledQuotientBits.Access.evaluator (quotientAccess F A) (quotientAccess_controls F A) P Q
  have D : SpaceFunction (fun c => BinaryNatCode.encode (ScaledSquarefree.degree (F.polynomial c))) :=
    (gcdDegreeEvaluator F A).congr (funext fun c => by
      simp only [ScaledSquarefree.degree, PolynomialGCDBits.degree, SquarefreePart.common, derivative_map])
  have R := ((D.precompose ScaledQuotientBits.context ScaledQuotientBits.context_FP).withInput.postcompose
    squarefreeRequest squarefreeRequest_FP).chain E
  refine R.congr (funext fun q => ?_)
  simp only [Function.comp_apply, squarefreeRequest, ScaledQuotientBits.Access.value,
    ScaledQuotientBits.context, ScaledQuotientBits.modulus, ScaledQuotientBits.modulusWord,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    quotientSource, squarefreeValue, ScaledSquarefree.polynomial]

end LeanCanny.Algebra.SeparableBits
