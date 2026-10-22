/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedTableSeparability

/-! # Native resultant coefficients for candidate node directions

A candidate context pairs a table node with a binary direction. Its two
polynomials are read by the uniform table evaluator. Supplied child orders
define the resultant on every word; no table-consistency or child-degree
promise is needed for the native coefficient certificate.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials.Candidate
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open SeparableBits (Family Readers)
open BalancedParameterContext (child)

noncomputable def polynomial (B : Family) (w : List Bool) : ℤ[X] :=
  cannyResultantWithDegrees (node B (child false (pairFst w))) (node B (child true (pairFst w)))
    (Nat.fromBitsLE (pairSnd w)) (leftOrder w) (rightOrder w)

noncomputable def source (B : Family) : CannyResultantBits.Family where
  left s := node B (child false (pairFst (pairFst s)))
  right s := node B (child true (pairFst (pairFst s)))
  direction s := Nat.fromBitsLE (pairSnd (pairFst s))
  degree s := Nat.fromBitsLE (pairSnd s)

def leftOrderAt (s : List Bool) : ℕ := leftOrder (pairFst s)
def rightOrderAt (s : List Bool) : ℕ := rightOrder (pairFst s)

attribute [local irreducible] tree node BinaryNat.normalize BalancedMetadataTable.read

noncomputable def access (B : Family) : CannyResultantBits.Access (source B) leftOrderAt rightOrderAt where
  leftDegree := BinaryNat.normalize ∘ childCode false ∘ pairFst
  rightDegree := BinaryNat.normalize ∘ childCode true ∘ pairFst
  direction := BinaryNat.normalize ∘ pairSnd ∘ pairFst
  degree := BinaryNat.normalize ∘ pairSnd
  leftCoefficient := BalancedTablePolynomials.coefficient (source B).left
  rightCoefficient := BalancedTablePolynomials.coefficient (source B).right
  leftDegree_eq s := by
    change BinaryNat.normalize (childCode false (pairFst s)) = BinaryNatCode.encode (Nat.fromBitsLE (childCode false (pairFst s)))
    exact BinaryNat.normalize_eq_bits _
  rightDegree_eq s := by
    change BinaryNat.normalize (childCode true (pairFst s)) = BinaryNatCode.encode (Nat.fromBitsLE (childCode true (pairFst s)))
    exact BinaryNat.normalize_eq_bits _
  direction_eq s := BinaryNat.normalize_eq_bits _
  degree_eq s := BinaryNat.normalize_eq_bits _
  leftCoefficient_eq := BalancedTablePolynomials.coefficient_packet (source B).left
  rightCoefficient_eq := BalancedTablePolynomials.coefficient_packet (source B).right

theorem controls (B : Family) : (access B).ControlsPolyTime := by
  have hl := mem_FP_comp (mem_FP_comp pairFst_mem_FP (childCode_FP false)) BinaryNat.normalize_mem_FP
  have hr := mem_FP_comp (mem_FP_comp pairFst_mem_FP (childCode_FP true)) BinaryNat.normalize_mem_FP
  have hd := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have hk := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  exact ⟨hl, hr, hd, hk⟩

def childQuery (right : Bool) (p : List Bool) : List Bool :=
  pair (pair (child right (pairFst (pairFst (pairFst (pairFst p))))) (pairSnd p)) (pairSnd (pairFst p))

theorem childQuery_FP (right : Bool) : childQuery right ∈ FP := by
  have hn := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) pairFst_mem_FP
  have hnode := mem_FP_comp hn (BalancedParameterContext.child_FP right)
  have hmod := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair hnode pairSnd_mem_FP) hmod

theorem childEvaluator (B : Family) (A : Readers B) (right : Bool) :
    SpaceFunction (BalancedTablePolynomials.coefficient (fun s => node B (child right (pairFst (pairFst s))))) := by
  have E := (BalancedTablePolynomials.evaluator B A).precompose (childQuery right) (childQuery_FP right)
  exact E.congr (funext fun p => by
    simp only [Function.comp_apply, childQuery, nodeValue, BalancedTablePolynomials.coefficient,
      CannyBalancedTaskRouting.nodeContext, CannyResultantBits.mValue, pairFst_pair, pairSnd_pair])

noncomputable def coefficient (B : Family) : List Bool → List Bool :=
  (source B).specifiedValue leftOrderAt rightOrderAt ∘ separabilityCoefficientQuery

theorem source_value (B : Family) (c : List Bool) :
    (source B).specifiedValue leftOrderAt rightOrderAt c =
      PrincipalCoefficientBits.integerResidue
        ((polynomial B (pairFst (pairFst c))).coeff (Nat.fromBitsLE (pairSnd (pairFst c)))) (CannyResultantBits.mValue c) := rfl

theorem coefficientEvaluator (B : Family) (A : Readers B) : SpaceFunction (coefficient B) :=
  ((access B).specifiedEvaluatorWithCoefficients (controls B) (childEvaluator B A false) (childEvaluator B A true)).precompose
    separabilityCoefficientQuery separabilityCoefficientQuery_FP

theorem coefficient_packet (B : Family) (c : List Bool) (k : ℕ) :
    coefficient B (pair c (BinaryNatCode.encode k)) =
      residueBits (((polynomial B (pairFst c)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd c) + 1)) := by
  simp only [coefficient, Function.comp_apply, source_value, separabilityCoefficientQuery,
    CannyResultantBits.mValue, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

end LeanCanny.Algebra.BalancedTablePolynomials.Candidate
