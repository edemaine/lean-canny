/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedTableCoefficientSpace
public import LeanCanny.Algebra.SeparableBoundedTest

/-! # Testing table-defined node polynomials with local correctness promises

The native coefficient evaluator supplies every determinant and derivative
child. A supplied binary height control and the stored degree define a space
test on all words. Only its correctness at the currently prepared node needs
the exact-degree, nonzero, and coefficient-height invariants.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open SeparableBits (Family Readers)

def separabilityCoefficientQuery (p : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst p)) (pairSnd p)) (pairSnd (pairFst p))

theorem separabilityCoefficientQuery_FP : separabilityCoefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def separabilityCoefficient (B : Family) : List Bool → List Bool := nodeValue B ∘ separabilityCoefficientQuery

theorem separabilityCoefficient_packet (B : Family) (c : List Bool) (k : ℕ) :
    separabilityCoefficient B (pair c (BinaryNatCode.encode k)) =
      residueBits (((node B (pairFst c)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd c) + 1)) := by
  simp only [separabilityCoefficient, separabilityCoefficientQuery, nodeValue, Function.comp_apply,
    CannyBalancedTaskRouting.nodeContext, CannyResultantBits.mValue, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

noncomputable def separabilityTest (B : Family) (heightBound : List Bool → ℕ) : Language :=
  SeparableBoundedTest.language (node B) BalancedMetadataTable.order heightBound

theorem separabilityTestDecider (B : Family) (A : Readers B) (heightBound : List Bool → ℕ) (hb : BinaryFn heightBound) :
    SpaceDecider (separabilityTest B heightBound) := by
  have hd : BinaryFn BalancedMetadataTable.order := BinaryFn.fromBits (BalancedMetadataTable.read_FP false)
  have E := (evaluator B A).precompose separabilityCoefficientQuery separabilityCoefficientQuery_FP
  exact SeparableBoundedTest.decider (node B) (separabilityCoefficient B) (separabilityCoefficient_packet B)
    E BalancedMetadataTable.order heightBound hd hb

theorem separabilityTest_correct_at (B : Family) (heightBound : List Bool → ℕ) (p : List Bool)
    (hn : node B p ≠ 0) (hd : (node B p).natDegree = BalancedMetadataTable.order p)
    (hb : ∀ k, ((node B p).coeff k).natAbs ≤ 2 ^ heightBound p) :
    p ∈ separabilityTest B heightBound ↔ ((node B p).map (Int.castRingHom ℚ)).Separable :=
  SeparableBoundedTest.correct_at (node B) BalancedMetadataTable.order heightBound p hn hd hb

end LeanCanny.Algebra.BalancedTablePolynomials
