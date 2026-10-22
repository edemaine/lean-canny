/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedTablePolynomials
public import LeanCanny.Algebra.CannyBalancedTaskResidues

/-! # The concrete table-driven balanced coefficient source

FP table projections supply every order/direction field. Mathematical tree
recursion proves the original-coefficient child identities against the same
mixed determinant family. The native uniform reader thus assumes neither
child answer certificates nor child semantic identities. Native FP controls
supply common metadata bounds, and modulus preservation bounds all replies.
Only a common reachable task-word bound remains to be instantiated.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (child original height index)
open CannyBalancedTaskRouting (nodeContext matrixPacket childInput coefficientTask isLeaf)
open BerkowitzPolynomial.TaskDispatch
open PrincipalCoefficientBits (integerResidue)

def leftOrder (s : List Bool) : ℕ := BalancedMetadataTable.order (child false (pairFst s))
def rightOrder (s : List Bool) : ℕ := BalancedMetadataTable.order (child true (pairFst s))

noncomputable def source (B : Family) : CannyResultantBits.Family where
  left s := node B (child false (pairFst s))
  right s := node B (child true (pairFst s))
  direction s := BalancedMetadataTable.direction (pairFst s)
  degree s := Nat.fromBitsLE (pairSnd s)

noncomputable def coefficient (P : List Bool → Polynomial ℤ) (p : List Bool) : List Bool :=
  integerResidue ((P (pairFst (pairFst p))).coeff (Nat.fromBitsLE (pairSnd p))) (CannyResultantBits.mValue (pairFst p))

theorem coefficient_packet (P : List Bool → Polynomial ℤ) (q : List Bool) (k : ℕ) :
    coefficient P (pair q (BinaryNatCode.encode k)) =
      MatrixPower.residueBits (((P (pairFst q)).coeff k : ℤ) : ZMod (CannyResultantBits.mValue q)) := by
  simp only [coefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem coefficient_length_le (P : List Bool → Polynomial ℤ) (p : List Bool) :
    (coefficient P p).length ≤ (CannyResultantBits.mValue (pairFst p)).size := by
  let : NeZero (CannyResultantBits.mValue (pairFst p)) := ⟨by unfold CannyResultantBits.mValue; omega⟩
  exact MatrixPower.residueBits_length_le _ _

def childCode (right : Bool) : List Bool → List Bool := BalancedMetadataTable.read false ∘ child right ∘ pairFst
def directionCode : List Bool → List Bool := BalancedMetadataTable.read true ∘ pairFst

attribute [local irreducible] tree node BinaryNat.normalize BalancedMetadataTable.read

noncomputable def sourceAccess (B : Family) : CannyResultantBits.Access (source B) leftOrder rightOrder where
  leftDegree := BinaryNat.normalize ∘ childCode false
  rightDegree := BinaryNat.normalize ∘ childCode true
  direction := BinaryNat.normalize ∘ directionCode
  degree := BinaryNat.normalize ∘ pairSnd
  leftCoefficient := coefficient (source B).left
  rightCoefficient := coefficient (source B).right
  leftDegree_eq s := by
    change BinaryNat.normalize (childCode false s) = BinaryNatCode.encode (Nat.fromBitsLE (childCode false s))
    exact BinaryNat.normalize_eq_bits _
  rightDegree_eq s := by
    change BinaryNat.normalize (childCode true s) = BinaryNatCode.encode (Nat.fromBitsLE (childCode true s))
    exact BinaryNat.normalize_eq_bits _
  direction_eq s := by
    change BinaryNat.normalize (directionCode s) = BinaryNatCode.encode (Nat.fromBitsLE (directionCode s))
    exact BinaryNat.normalize_eq_bits _
  degree_eq s := by
    change BinaryNat.normalize (pairSnd s) = BinaryNatCode.encode (Nat.fromBitsLE (pairSnd s))
    exact BinaryNat.normalize_eq_bits _
  leftCoefficient_eq := coefficient_packet (source B).left
  rightCoefficient_eq := coefficient_packet (source B).right

theorem childCode_FP (right : Bool) : childCode right ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP (BalancedParameterContext.child_FP right)) (BalancedMetadataTable.read_FP false)

theorem directionCode_FP : directionCode ∈ FP := mem_FP_comp pairFst_mem_FP (BalancedMetadataTable.read_FP true)

theorem source_controls (B : Family) : (sourceAccess B).ControlsPolyTime := by
  have hl := mem_FP_comp (childCode_FP false) BinaryNat.normalize_mem_FP
  have hr := mem_FP_comp (childCode_FP true) BinaryNat.normalize_mem_FP
  have hd := mem_FP_comp directionCode_FP BinaryNat.normalize_mem_FP
  have hk := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  exact ⟨hl, hr, hd, hk⟩

noncomputable def matrixFamily (B : Family) : BerkowitzPolynomial.ModularFamily :=
  CannyResultantBits.WithSquarefreeLeaves.family (leafFamily B) (F := source B) isLeaf leftOrder rightOrder

noncomputable def matrixAccess (B : Family) : BerkowitzPolynomial.ModularAccess (matrixFamily B) :=
  CannyResultantBits.WithSquarefreeLeaves.access (leafFamily B) (sourceAccess B) isLeaf

noncomputable def nodeValue (B : Family) (c : List Bool) : List Bool :=
  integerResidue ((node B (nodeContext c)).coeff (Nat.fromBitsLE (pairSnd (pairFst c)))) (CannyResultantBits.mValue c)

/-- This identity covers arbitrary metadata tables and arbitrary query words. -/
theorem matrixFamily_value (B : Family) (c : List Bool) : (matrixFamily B).value c = nodeValue B c := by
  rw [matrixFamily, CannyResultantBits.WithSquarefreeLeaves.family_value]
  by_cases hs : isLeaf c = true
  · simp only [hs, ite_true]
    rw [SeparableBits.LeafMatrix.squarefreeValue_packet]
    have hh : height (nodeContext c) = 0 := by
      by_contra hn
      have hf := (CannyBalancedTaskRouting.isLeaf_false_iff c).mpr (Nat.pos_of_ne_zero hn)
      rw [hf] at hs
      contradiction
    change integerResidue ((ScaledSquarefree.polynomial (B.polynomial (leafInput (pairFst c)))).coeff
      (Nat.fromBitsLE (pairSnd (pairFst c)))) (CannyResultantBits.mValue c) = nodeValue B c
    rw [leafInput_eq]
    unfold nodeValue
    rw [node_zero B _ hh]
    rfl
  · have hf := Bool.eq_false_iff.mpr hs
    have hh := (CannyBalancedTaskRouting.isLeaf_false_iff c).mp hf
    simp only [hf, Bool.false_eq_true, ite_false]
    change integerResidue ((cannyResultantWithDegrees (node B (child false (nodeContext c))) (node B (child true (nodeContext c)))
      (BalancedMetadataTable.direction (nodeContext c)) (BalancedMetadataTable.order (child false (nodeContext c)))
      (BalancedMetadataTable.order (child true (nodeContext c)))).coeff (Nat.fromBitsLE (pairSnd (pairFst c))))
      (CannyResultantBits.mValue c) = nodeValue B c
    rw [← node_children B _ hh]
    rfl

theorem nodeValue_childInput (B : Family) (right : Bool) (p : List Bool) :
    nodeValue B (childInput right p) = coefficient (fun s => node B (child right (pairFst s))) p := by
  simp only [nodeValue, coefficient, childInput, matrixPacket, nodeContext,
    CannyResultantBits.mValue, pairFst_pair, pairSnd_pair]

theorem child_answer (B : Family) (right : Bool) (p : List Bool) :
    answer (matrixAccess B) (coefficientTask right p) = coefficient (fun s => node B (child right (pairFst s))) p := by
  change answer (matrixAccess B) (determinantTask (childInput right p)) = _
  rw [answer_determinant, matrixFamily_value, nodeValue_childInput]

def reachableTasks (B : Family) : List Bool → List Bool → Prop := CannyBalancedTaskRouting.tasks (leafFamily B) (sourceAccess B)

/-- Uniform evaluation of the concrete supplied-table tree. Only the original
leaf reader and a common task-word bound are required. The child identities,
reply bounds, metadata bounds, query closure, and rank bounds are derived. -/
theorem evaluator (B : Family) (A : Readers B) (K : List Bool → ℕ) (hK : UnaryFn K)
    (hword : ∀ root q, reachableTasks B root q → q.length ≤ K root) :
    SpaceFunction (nodeValue B) := by
  have hw (root q : List Bool) (hq : reachableTasks B root q) : q.length ≤ K root + 1 :=
    (hword root q hq).trans (Nat.le_add_right _ _)
  have hr (root q : List Bool) (hq : reachableTasks B root q) :
      (answer (matrixAccess B) q).length ≤ K root + 1 := by
    have hb := CannyBalancedTaskRouting.reachable_answer_length_le (leafFamily B) (sourceAccess B)
      (coefficient_length_le (source B).right) root q hq
    exact hb.trans (Nat.add_le_add_right (hword root root (CannyBalancedTaskRouting.tasks_root _ _ root)) 1)
  have E := CannyBalancedTaskRouting.evaluator (leafFamily B) (sourceAccess B) (leafReaders B A) (source_controls B)
    (child_answer B false) (child_answer B true) (fun root => K root + 1) (hK.add (UnaryFn.const 1)) hw hr
  exact E.congr (funext (matrixFamily_value B))

end LeanCanny.Algebra.BalancedTablePolynomials
