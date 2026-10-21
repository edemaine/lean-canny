/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeConstraintSubstitution
public import LeanCanny.ETR.TubeLevelSignBounds

/-! # Coordinate coefficient access for the tube sign stage

Coordinate indices are binary; the finite coordinate family extends by zero
outside its spatial range. Reindexing its native readers supplies the complete
rational substitution of each integer constraint.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelSign
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket MatrixPower RationalSubstitution
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def numerator (S : Source) (c : List Bool) (i : ℕ) : Polynomial ℤ :=
  if hi : i < TubeSampleCoefficient.A S.packet c then (S.coordinates c).numerator ⟨i, hi⟩ else 0

noncomputable def denominator (S : Source) (c : List Bool) (i : ℕ) : Polynomial ℤ :=
  if hi : i < TubeSampleCoefficient.A S.packet c then (S.coordinates c).denominator ⟨i, hi⟩ else 0

structure CoefficientReaders (S : Source) where
  rootCoefficient : List Bool → List Bool
  rootEvaluator : SpaceFunction rootCoefficient
  root_eq : ∀ c k m, 0 < m → rootCoefficient
    (pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) =
      residueBits ((((S.coordinates c).polynomial.coeff k : ℤ) : ZMod m))
  coordinates : TubeConstraintSubstitution.CoordinateReaders S.packet (numerator S) (denominator S)

noncomputable def substitutionFamily (S : Source) : IntegerBits.Family :=
  TubeConstraintSubstitution.family (S.packet ∘ pairFst) pairSnd
    (fun q => numerator S (pairFst q)) (fun q => denominator S (pairFst q))

def substitutionQuery (q : List Bool) : List Bool :=
  pair (pair (pair (IntegerBits.context q) (pairFst (IntegerBits.selectedDegree q)))
    (pairSnd (IntegerBits.selectedDegree q))) (pairSnd q)

theorem substitutionQuery_FP : substitutionQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair IntegerBits.context_mem_FP
    (mem_FP_comp IntegerBits.selectedDegree_mem_FP pairFst_mem_FP))
    (mem_FP_comp IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def substitutedValue (S : Source) : List Bool → List Bool :=
  (substitutionFamily S).value ∘ substitutionQuery

theorem substitutedEvaluator (S : Source) (C : CoefficientReaders S) (hp : S.packet ∈ FP) :
    SpaceFunction (substitutedValue S) :=
  (TubeConstraintSubstitution.evaluator _ _ _ _
    (TubeConstraintSubstitution.CoordinateReaders.precompose _ _ _ C.coordinates pairFst pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP hp) pairSnd_mem_FP).precompose _ substitutionQuery_FP

set_option backward.isDefEq.respectTransparency false in
theorem substitutionPolynomial (S : Source) (c : List Bool)
    (i : PerturbedSource.Index (pairFst (S.packet c))) :
    (substitutionFamily S).polynomial
      (pair c (BinaryNatCode.encode (TubeEncoding.constraintEquiv (TubeIndexed.arity (pairFst (S.packet c))) i).val)) =
      clearedWith (fun _ => TubeIndexed.degreeBound (pairFst (S.packet c))) (integerConstraint (S.packet c) i)
        (S.coordinates c).numerator (S.coordinates c).denominator := by
  let code := BinaryNatCode.encode (TubeEncoding.constraintEquiv (TubeIndexed.arity (pairFst (S.packet c))) i).val
  have hr : TubeConstraintCoefficient.decodedRow S.packet (fun _ => code) c = i := by
    apply TubeConstraintCoefficient.decodedRow_of_code
    exact Nat.fromBitsLE_bits _
  have he := TubeConstraintSubstitution.polynomial_eq S.packet (fun _ => code)
    (numerator S) (denominator S) c
  rw [hr] at he
  have hl : (substitutionFamily S).polynomial (pair c code) =
      (TubeConstraintSubstitution.family S.packet (fun _ => code) (numerator S) (denominator S)).polynomial c := by
    simp only [IntegerBits.Family.polynomial, substitutionFamily, TubeConstraintSubstitution.family,
      TubeSampleCoefficient.A, TubeConstraintIndexed.blockWidth, Function.comp_apply, pairFst_pair]
    congr 1
    funext r
    simp only [TubeConstraintIndexed.coefficient, Function.comp_apply, pairFst_pair, pairSnd_pair]
  have hn : (fun j : Fin (TubeSampleCoefficient.A S.packet c) => numerator S c j.val) =
      (S.coordinates c).numerator := by
    funext j
    exact dite_eq_left j.isLt
  have hd : (fun j : Fin (TubeSampleCoefficient.A S.packet c) => denominator S c j.val) =
      (S.coordinates c).denominator := by
    funext j
    exact dite_eq_left j.isLt
  exact hl.trans (he.trans (congrArg₂ (clearedWith
    (fun _ => TubeIndexed.degreeBound (pairFst (S.packet c))) (integerConstraint (S.packet c) i)) hn hd))

set_option backward.isDefEq.respectTransparency false in
theorem substitutedValue_packet (S : Source) (c : List Bool)
    (i : PerturbedSource.Index (pairFst (S.packet c))) (k m : ℕ) (hm : 0 < m) :
    substitutedValue S
      (pair (pair c (pair (BinaryNatCode.encode (TubeEncoding.constraintEquiv (TubeIndexed.arity (pairFst (S.packet c))) i).val)
        (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      IntegerBits.coefficientResidue
        ((clearedWith (fun _ => TubeIndexed.degreeBound (pairFst (S.packet c))) (integerConstraint (S.packet c) i)
          (S.coordinates c).numerator (S.coordinates c).denominator).coeff k) m := by
  simp only [substitutedValue, Function.comp_apply, substitutionQuery, IntegerBits.context,
    IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair]
  have he := (substitutionFamily S).value_packet
    (pair (pair c (BinaryNatCode.encode (TubeEncoding.constraintEquiv (TubeIndexed.arity (pairFst (S.packet c))) i).val))
      (BinaryNatCode.encode k)) m hm
  have hk : Nat.fromBitsLE (BinaryNatCode.encode k) = k := Nat.fromBitsLE_bits _
  rw [pairFst_pair, pairSnd_pair, hk] at he
  exact he.trans (congrArg (fun p : Polynomial ℤ => IntegerBits.coefficientResidue (p.coeff k) m)
    (substitutionPolynomial S c i))

end LeanCanny.ETR.TubeLevelSign
