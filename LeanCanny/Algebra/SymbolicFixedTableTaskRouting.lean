/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableProgram
public import LeanCanny.Algebra.BalancedParameterContext
public import LeanCanny.Algebra.BerkowitzTaskLevels

/-! # Concrete recursive tasks for symbolic primitive coefficients

A matrix context retains a node, alpha index, root index, and modulus. A child
request replaces the node and both selected indices; it does not retain matrix
row/column selectors. Unary node height strictly decreases at every nonleaf
source descent, including malformed words.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTableTaskRouting
open LeanCanny.Encoding LeanCanny.Computation
open BerkowitzPolynomial.TaskDispatch
open SymbolicFixedTableEntryBits

def nodeContext (c : List Bool) : List Bool := pairFst (pairFst c)
def level (c : List Bool) : ℕ := BalancedParameterContext.height (nodeContext c)
def isLeaf (c : List Bool) : Bool := (BalancedParameterContext.heightWord (nodeContext c)).isEmpty

def matrixPacket (node alpha root modulus : List Bool) : List Bool := pair (pair node (pair alpha root)) modulus

def sourceNode (p : List Bool) : List Bool := pairFst (pairFst (pairFst (pairFst p)))
def sourceAlpha (p : List Bool) : List Bool := pairSnd (pairFst (pairFst p))

def childInput (right : Bool) (p : List Bool) : List Bool :=
  matrixPacket (BalancedParameterContext.child right (sourceNode p)) (sourceAlpha p) (pairSnd p) (pairSnd (pairFst p))

def coefficientTask (right : Bool) : List Bool → List Bool := determinantTask ∘ childInput right

theorem nodeContext_FP : nodeContext ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem level_unary : UnaryFn level := BalancedParameterContext.height_unary.comp nodeContext_FP

theorem isLeaf_FP : (fun c => [isLeaf c]) ∈ FP := by
  have h := Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsIsEmpty.comp
    (mem_FP_comp nodeContext_FP BalancedParameterContext.heightWord_FP)
  exact h.encoded

theorem sourceNode_FP : sourceNode ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) pairFst_mem_FP

theorem sourceAlpha_FP : sourceAlpha ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem childInput_FP (right : Bool) : childInput right ∈ FP := by
  have hn := mem_FP_comp sourceNode_FP (BalancedParameterContext.child_FP right)
  have hm := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_of_eq (mem_FP_pair (mem_FP_pair hn (mem_FP_pair sourceAlpha_FP pairSnd_mem_FP)) hm) (fun _ => rfl)

theorem coefficientTask_FP (right : Bool) : coefficientTask right ∈ FP :=
  mem_FP_comp (childInput_FP right) (tag_FP false false)

theorem level_zero : level [] = 0 := rfl

theorem level_le_length (c : List Bool) : level c ≤ c.length :=
  (BalancedParameterContext.height_le_length (nodeContext c)).trans
    ((pairFst_length_le (pairFst c)).trans (pairFst_length_le c))

theorem origin_level_le_length (q : List Bool) : level (origin q) ≤ q.length :=
  (level_le_length (origin q)).trans (origin_length_le q)

theorem isLeaf_false_iff (c : List Bool) : isLeaf c = false ↔ 0 < level c := by
  unfold isLeaf level BalancedParameterContext.height
  cases BalancedParameterContext.heightWord (nodeContext c) <;> simp

theorem childInput_level (right : Bool) (p : List Bool) :
    level (childInput right p) = BalancedParameterContext.height (sourceNode p) - 1 := by
  simp only [level, childInput, matrixPacket, nodeContext, pairFst_pair, BalancedParameterContext.height_child]

theorem coefficientTask_level (right : Bool) (p : List Bool) :
    level (origin (coefficientTask right p)) = BalancedParameterContext.height (sourceNode p) - 1 := by
  rw [coefficientTask, Function.comp_apply, origin_determinant, childInput_level]

theorem sourceNode_leftQuery (F : Family) (radix : List Bool → List Bool) (p : List Bool) :
    sourceNode (CannyResultantBits.RecursiveStage.leftQuery F.access (sourceInput radix p)) = nodeContext (pairFst p) := by
  unfold sourceNode
  rw [CannyResultantBits.RecursiveStage.leftQuery_context]
  simp only [sourceInput, Function.comp_apply, entryQuery, splitInput, nodeContext, pairFst_pair, pairSnd_pair]

theorem sourceNode_rightQuery (radix : List Bool → List Bool) (p : List Bool) :
    sourceNode (CannyResultantBits.RecursiveStage.rightQuery (sourceInput radix p)) = nodeContext (pairFst p) := by
  unfold sourceNode
  rw [CannyResultantBits.RecursiveStage.rightQuery_context]
  simp only [sourceInput, Function.comp_apply, entryQuery, splitInput, nodeContext, pairFst_pair, pairSnd_pair]

theorem leftTask_decreases (F : Family) (radix : List Bool → List Bool) (p : List Bool)
    (hp : isLeaf (pairFst p) = false) :
    level (origin (coefficientTask false (CannyResultantBits.RecursiveStage.leftQuery F.access (sourceInput radix p)))) <
      level (pairFst p) := by
  rw [coefficientTask_level, sourceNode_leftQuery]
  exact Nat.sub_lt ((isLeaf_false_iff _).mp hp) (by decide)

theorem rightTask_decreases (radix : List Bool → List Bool) (p : List Bool)
    (hp : isLeaf (pairFst p) = false) :
    level (origin (coefficientTask true (CannyResultantBits.RecursiveStage.rightQuery (sourceInput radix p)))) <
      level (pairFst p) := by
  rw [coefficientTask_level, sourceNode_rightQuery]
  exact Nat.sub_lt ((isLeaf_false_iff _).mp hp) (by decide)

end LeanCanny.Algebra.SymbolicFixedTableTaskRouting
