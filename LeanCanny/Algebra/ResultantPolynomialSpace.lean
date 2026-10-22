/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SylvesterPolynomialSpace
public import LeanCanny.Algebra.BerkowitzPolynomialSpace

/-!
# Polynomial-space symbolic resultant coefficient evaluation

The Sylvester matrix is accessed one polynomial coefficient at a time. The
polynomial determinant evaluator returns a selected coefficient of the
specified-degree resultant over a varying positive modulus. Both input
coefficient routines may use polynomial space.
-/

@[expose] public section

namespace LeanCanny.Algebra.ResultantPolynomial

open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open Polynomial

structure ModularFamily where
  modulus : List Bool → ℕ
  left : (c : List Bool) → Polynomial (Polynomial (ZMod (modulus c)))
  right : (c : List Bool) → Polynomial (Polynomial (ZMod (modulus c)))
  leftDegree : List Bool → ℕ
  rightDegree : List Bool → ℕ
  degree : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def ModularFamily.value (F : ModularFamily) (c : List Bool) : List Bool :=
  residueBits (((F.left c).resultant (F.right c) (F.leftDegree c) (F.rightDegree c)).coeff (F.degree c))

def ModularFamily.zeroLanguage (F : ModularFamily) : LeanCanny.Language :=
  {c | ((F.left c).resultant (F.right c) (F.leftDegree c) (F.rightDegree c)).coeff (F.degree c) = 0}

noncomputable def ModularFamily.determinant (F : ModularFamily) : BerkowitzPolynomial.ModularFamily where
  dimension := fun c => F.leftDegree c + F.rightDegree c
  modulus := F.modulus
  degree := F.degree
  matrix := fun c => Polynomial.sylvester (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c)
  modulus_ne_zero := F.modulus_ne_zero

structure ModularAccess (F : ModularFamily) where
  bits : SylvesterPolynomialBits.Access
  leftDegree_eq : ∀ c, bits.leftDegree c = BinaryNatCode.encode (F.leftDegree c)
  rightDegree_eq : ∀ c, bits.rightDegree c = BinaryNatCode.encode (F.rightDegree c)
  modulus_eq : ∀ c, bits.modulus c = BinaryNatCode.encode (F.modulus c)
  degree_eq : ∀ c, bits.degree c = BinaryNatCode.encode (F.degree c)
  leftCoefficient_eq : ∀ c k d, bits.leftCoefficient (pair c (pair (BinaryNatCode.encode k) (BinaryNatCode.encode d))) =
    residueBits (((F.left c).coeff k).coeff d)
  rightCoefficient_eq : ∀ c k d, bits.rightCoefficient (pair c (pair (BinaryNatCode.encode k) (BinaryNatCode.encode d))) =
    residueBits (((F.right c).coeff k).coeff d)

namespace ModularAccess

noncomputable def determinant {F : ModularFamily} (a : ModularAccess F) :
    BerkowitzPolynomial.ModularAccess F.determinant where
  dimension := a.bits.dimension
  modulus := a.bits.modulus
  degree := a.bits.degree
  entry := a.bits.entry
  dimension_eq := fun c => SylvesterPolynomialBits.Access.dimension_code a.bits c _ _ (a.leftDegree_eq c) (a.rightDegree_eq c)
  modulus_eq := a.modulus_eq
  degree_eq := a.degree_eq
  entry_eq := by
    intro c i j d
    exact SylvesterPolynomialBits.Access.entry_correct a.bits c (F.left c) (F.right c)
      (F.leftDegree c) (F.rightDegree c) d residueBits (a.leftDegree_eq c) (a.rightDegree_eq c)
      (fun k => a.leftCoefficient_eq c k d) (fun k => a.rightCoefficient_eq c k d)
      (by simp [residueBits, BinaryNatCode.encode]) i j

theorem determinant_controls {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime) :
    a.determinant.ControlsPolyTime := by
  have hd := SylvesterPolynomialBits.Access.dimension_mem_FP a.bits ha
  constructor
  · simpa only [determinant] using hd
  · simpa only [determinant] using ha.modulus
  · simpa only [determinant] using ha.degree

theorem entryEvaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.leftCoefficient) (R : SpaceFunction a.bits.rightCoefficient) :
    SpaceFunction a.determinant.entry := by
  have E := SylvesterPolynomialBits.Access.entryEvaluator a.bits ha L R
  simpa only [determinant] using E

theorem evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.leftCoefficient) (R : SpaceFunction a.bits.rightCoefficient) :
    SpaceFunction F.value := by
  have E := BerkowitzPolynomial.ModularAccess.evaluator a.determinant (determinant_controls a ha)
    (entryEvaluator a ha L R)
  refine E.congr ?_
  funext c
  rfl

theorem decider {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.leftCoefficient) (R : SpaceFunction a.bits.rightCoefficient) :
    SpaceDecider F.zeroLanguage :=
  BerkowitzPolynomial.ModularAccess.decider a.determinant (determinant_controls a ha) (entryEvaluator a ha L R)

theorem zeroLanguage_mem_PSPACE_of_evaluators {F : ModularFamily} (a : ModularAccess F)
    (ha : a.bits.ControlsPolyTime) (L : SpaceFunction a.bits.leftCoefficient) (R : SpaceFunction a.bits.rightCoefficient) :
    F.zeroLanguage ∈ PSPACE := (decider a ha L R).mem_PSPACE

end ModularAccess
end LeanCanny.Algebra.ResultantPolynomial
