/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedParameterContext
public import LeanCanny.Algebra.CannySquarefreeLeaves

/-! # Concrete child coefficient tasks for a balanced parameter tree

Matrix contexts carry a node address, the selected coefficient degree, and a
modulus predecessor. A child query replaces the address and degree, retaining
the original input and modulus; it does not nest the parent's matrix indices.
Unary remaining height discharges every nonleaf source-level decrease.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyBalancedTaskRouting
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM
open BerkowitzPolynomial.TaskDispatch

def nodeContext (c : List Bool) : List Bool := pairFst (pairFst c)
def level (c : List Bool) : ℕ := BalancedParameterContext.height (nodeContext c)
def isLeaf (c : List Bool) : Bool := (BalancedParameterContext.heightWord (nodeContext c)).isEmpty

def matrixPacket (node degree modulus : List Bool) : List Bool := pair (pair node degree) modulus

def childInput (right : Bool) (p : List Bool) : List Bool :=
  matrixPacket (BalancedParameterContext.child right (nodeContext (pairFst p))) (pairSnd p) (pairSnd (pairFst p))

def coefficientTask (right : Bool) : List Bool → List Bool := determinantTask ∘ childInput right

attribute [local irreducible] BinaryNat.normalize

theorem nodeContext_FP : nodeContext ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem level_unary : UnaryFn level := BalancedParameterContext.height_unary.comp nodeContext_FP

theorem isLeaf_FP : (fun c => [isLeaf c]) ∈ FP := by
  have h := ComputableTidilyInPolyTime.bitsIsEmpty.comp
    (mem_FP_comp nodeContext_FP BalancedParameterContext.heightWord_FP)
  exact h.encoded

theorem childInput_FP (right : Bool) : childInput right ∈ FP := by
  have hn := mem_FP_comp (mem_FP_comp pairFst_mem_FP nodeContext_FP) (BalancedParameterContext.child_FP right)
  have hm := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have h := mem_FP_pair (mem_FP_pair hn pairSnd_mem_FP) hm
  exact mem_FP_of_eq h (fun _ => by simp only [childInput, matrixPacket, Function.comp_apply])

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

theorem childInput_packet (right : Bool) (node parentDegree modulus degree : List Bool) :
    childInput right (pair (matrixPacket node parentDegree modulus) degree) =
      matrixPacket (BalancedParameterContext.child right node) degree modulus := by
  simp only [childInput, nodeContext, matrixPacket, pairFst_pair, pairSnd_pair]

theorem coefficientTask_level (right : Bool) (p : List Bool) :
    level (origin (coefficientTask right p)) = level (pairFst p) - 1 := by
  simp only [coefficientTask, Function.comp_apply, origin_determinant, level, nodeContext, childInput,
    matrixPacket, pairFst_pair, BalancedParameterContext.height_child]

theorem coefficientTask_packet_length (right : Bool) (node parentDegree modulus degree : List Bool) :
    (coefficientTask right (pair (matrixPacket node parentDegree modulus) degree)).length =
      4 * (BalancedParameterContext.child right node).length + 2 * degree.length + modulus.length + 8 := by
  change (determinantTask (childInput right (pair (matrixPacket node parentDegree modulus) degree))).length = _
  rw [childInput_packet]
  simp only [determinantTask, tag, List.length_cons, matrixPacket, pair_length]
  omega

theorem coefficientTask_length_le (right : Bool) (node parentDegree modulus degree : List Bool)
    (hp : BalancedParameterContext.Paired node) (hh : 0 < BalancedParameterContext.height node) :
    (coefficientTask right (pair (matrixPacket node parentDegree modulus) degree)).length ≤
      4 * node.length + 2 * degree.length + modulus.length + 8 := by
  rw [coefficientTask_packet_length]
  have h := BalancedParameterContext.child_length_lt right node hp hh
  omega

/-- The concrete address writers discharge every source-level decrease;
neither child semantics nor computation certificates are needed here. -/
theorem source_levels (L : SeparableBits.Family) {F : CannyResultantBits.Family} (a : CannyResultantBits.Access F)
    (tasks : List Bool → List Bool → Prop) :
    SourceLevels (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf)
      (CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf (coefficientTask false) (coefficientTask true)).controller
      (fun _ => 1) tasks level := by
  apply CannyResultantBits.WithSquarefreeLeaves.source_levels
  · intro p hs _ _ _
    rw [coefficientTask_level, CannyResultantBits.RecursiveStage.leftQuery_context]
    exact Nat.sub_lt (isLeaf_false_iff _ |>.mp hs) (by decide)
  · intro p hs _ _ _
    rw [coefficientTask_level, CannyResultantBits.RecursiveStage.rightQuery_context]
    exact Nat.sub_lt (isLeaf_false_iff _ |>.mp hs) (by decide)

end LeanCanny.Algebra.CannyBalancedTaskRouting
