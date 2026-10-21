/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyCoefficientSpace
public import LeanCanny.Algebra.PrimitivePairCoordinates
public import LeanCanny.Algebra.RationalSubstitutionResidue

/-! # Native coefficient readers for a primitive root-pair construction

Queries use `pair (pair context degree) modulusPredecessor`. Degree and direction
metadata are FP; the two source coefficient readers need only polynomial space.
The resultant and the actual piecewise recovery polynomials are computed from
those children on all binary inputs.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePairBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)
open scoped Classical
attribute [local irreducible] BinaryNat.normalize

structure Source where
  left : List Bool → Polynomial ℤ
  right : List Bool → Polynomial ℤ
  direction : List Bool → ℕ

noncomputable def coefficient (p : List Bool → Polynomial ℤ) (q : List Bool) : List Bool :=
  coefficientResidue ((p (context q)).coeff (Nat.fromBitsLE (selectedDegree q))) (mValue q)

structure Readers (S : Source) where
  leftDegree : List Bool → List Bool
  rightDegree : List Bool → List Bool
  direction : List Bool → List Bool
  leftDegreeFP : leftDegree ∈ FP
  rightDegreeFP : rightDegree ∈ FP
  directionFP : direction ∈ FP
  leftDegree_eq : ∀ c, leftDegree c = BinaryNatCode.encode (S.left c).natDegree
  rightDegree_eq : ∀ c, rightDegree c = BinaryNatCode.encode (S.right c).natDegree
  direction_eq : ∀ c, direction c = BinaryNatCode.encode (S.direction c)
  leftEvaluator : SpaceFunction (coefficient S.left)
  rightEvaluator : SpaceFunction (coefficient S.right)

noncomputable def sourceFamily (S : Source) : CannyResultantBits.Family where
  left q := S.left (pairFst q)
  right q := S.right (pairFst q)
  direction q := S.direction (pairFst q)
  degree q := Nat.fromBitsLE (pairSnd q)

def sourceQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst q))) (pairSnd q)) (pairSnd (pairFst q))

theorem sourceQuery_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def sourceAccess (S : Source) (A : Readers S) : CannyResultantBits.Access (sourceFamily S) where
  leftDegree := A.leftDegree ∘ pairFst
  rightDegree := A.rightDegree ∘ pairFst
  direction := A.direction ∘ pairFst
  degree := BinaryNat.normalize ∘ pairSnd
  leftCoefficient := coefficient S.left ∘ sourceQuery
  rightCoefficient := coefficient S.right ∘ sourceQuery
  leftDegree_eq q := A.leftDegree_eq _
  rightDegree_eq q := A.rightDegree_eq _
  direction_eq q := A.direction_eq _
  degree_eq q := BinaryNat.normalize_eq_bits _
  leftCoefficient_eq q k := by
    simp only [Function.comp_apply, coefficient, sourceQuery, context, selectedDegree, mValue,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, sourceFamily]
    rfl
  rightCoefficient_eq q k := by
    simp only [Function.comp_apply, coefficient, sourceQuery, context, selectedDegree, mValue,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, sourceFamily]
    rfl

theorem sourceAccess_controls (S : Source) (A : Readers S) : (sourceAccess S A).ControlsPolyTime := by
  have hl := mem_FP_comp pairFst_mem_FP A.leftDegreeFP
  have hr := mem_FP_comp pairFst_mem_FP A.rightDegreeFP
  have hc := mem_FP_comp pairFst_mem_FP A.directionFP
  have hd := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  constructor
  · simpa only [sourceAccess] using hl
  · simpa only [sourceAccess] using hr
  · simpa only [sourceAccess] using hc
  · simpa only [sourceAccess] using hd

theorem resultantEvaluator (S : Source) (A : Readers S) :
    SpaceFunction (coefficient (fun c => cannyResultant (S.left c) (S.right c) (S.direction c))) := by
  have E := (sourceAccess S A).evaluatorWithCoefficients (sourceAccess_controls S A)
    (A.leftEvaluator.precompose sourceQuery sourceQuery_FP) (A.rightEvaluator.precompose sourceQuery sourceQuery_FP)
  exact E.congr (funext fun _ => rfl)

noncomputable def coordinateFamily (S : Source) (r : ℕ) : CannySubresultantBits.Family where
  source := sourceFamily S
  coefficient _ := r

noncomputable def coordinateAccess (S : Source) (A : Readers S) (r : ℕ) : CannySubresultantBits.Access (coordinateFamily S r) where
  source := sourceAccess S A
  coefficient _ := BinaryNatCode.encode r
  coefficient_eq _ := rfl

theorem coordinateAccess_controls (S : Source) (A : Readers S) (r : ℕ) :
    (coordinateAccess S A r).ControlsPolyTime := ⟨sourceAccess_controls S A, constFn_mem_FP _⟩

theorem coordinateEvaluator (S : Source) (A : Readers S) (r : ℕ) :
    SpaceFunction (coefficient (fun c => coordinateCoefficient (S.left c) (S.right c) (S.direction c) r)) := by
  have E := CannyCoordinateBits.evaluatorWithCoefficients (coordinateAccess S A r) (coordinateAccess_controls S A r)
    (A.leftEvaluator.precompose sourceQuery sourceQuery_FP) (A.rightEvaluator.precompose sourceQuery sourceQuery_FP)
  exact E.congr (funext fun _ => rfl)

end LeanCanny.Algebra.PrimitivePairBits
