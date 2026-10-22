/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicPrimitivePairSpace

/-! # Native choice of either symbolic pair coordinate -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicPairRecoveryBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open SymbolicScaledQuotientBits (original modulus alpha target original_FP)

lemma Family.selectedNumeratorEvaluator (F : Family) (B : List Bool → ℕ)
    (hP : ∀ c k, ((F.left c).coeff k).natDegree ≤ B c)
    (hQ : ∀ c k, ((F.right c).coeff k).natDegree ≤ B c)
    (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) (hc : BinaryFn F.direction) (hB : BinaryFn B)
    (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.left))
    (Q : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.right))
    (right : List Bool → Bool) (hr : (fun c => [right c]) ∈ FP) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (fun c => F.numerator (right c) c)) := by
  have hs : (fun q => [right (original q)]) ∈ FP := mem_FP_comp original_FP hr
  have E := SpaceFunction.branch (fun q => right (original q)) hs
    (F.numeratorEvaluator B hP hQ hm hn hc hB P Q true)
    (F.numeratorEvaluator B hP hQ hm hn hc hB P Q false)
  refine E.congr (funext fun q => ?_)
  change (if right (original q) = true then
    SymbolicFixedTableEntryBits.coefficient (F.numerator true) q else
    SymbolicFixedTableEntryBits.coefficient (F.numerator false) q) =
      SymbolicFixedTableEntryBits.integerResidue
        (((F.numerator (right (original q)) (original q)).coeff (Nat.fromBitsLE (target q))).coeff
          (Nat.fromBitsLE (alpha q))) (Nat.fromBitsLE (modulus q) + 1)
  cases right (original q) <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    SymbolicFixedTableEntryBits.coefficient] <;> rfl

end LeanCanny.Algebra.SymbolicPairRecoveryBits
