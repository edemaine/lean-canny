/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ClosedFormulaGateNodes
/-! # Primitive native controls for actual strict-positive Boolean margin gates -/
@[expose] public section
namespace LeanCanny.Encoding.OpenFormulaGateMetadata
open LeanCanny.Computation ETR LeanCanny.Connectivity ClosedFormulaGateMetadata
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field MonotoneGateSource.index
  Brackets.firstNode Brackets.firstChild Brackets.afterNode Brackets.contents
  FormulaBooleanCircuitSource.arguments FormulaBooleanCircuitSource.termCode ClosedFormulaGateMetadata.query
  ClosedFormulaGateMetadata.HasTag ClosedFormulaGateMetadata.HasInner

def kind (q : List Bool) : ℕ :=
  if HasTag 2 q then 2 else if HasTag 3 q ∧ HasInner 0 q then 1 else
  if HasTag 4 q then 4 else if HasTag 5 q then 5 else 0

theorem kind_binary : BinaryFn kind :=
  BinaryFn.ite (hasTag_FP 2) (BinaryFn.const 2)
    (BinaryFn.ite ((hasTag_FP 3).and (hasInner_FP 0)) (BinaryFn.const 1)
      (BinaryFn.ite (hasTag_FP 4) (BinaryFn.const 4) (BinaryFn.ite (hasTag_FP 5) (BinaryFn.const 5) (BinaryFn.const 0))))

def rawAtomCode (q : List Bool) : List Bool :=
  if HasTag 2 q then Codec.taggedTwo 3 (Term.const (-1)).toData.toBits
    (TermView.normalize (FormulaBooleanCircuitSource.termCode (query q))) else (Term.const 0).toData.toBits

theorem rawAtomCode_FP : rawAtomCode ∈ FP := by
  have HT := mem_FP_comp (f := FormulaBooleanCircuitSource.termCode ∘ query) (g := TermView.normalize)
    (mem_FP_comp (f := query) (g := FormulaBooleanCircuitSource.termCode) query_FP FormulaBooleanCircuitSource.termCode_FP)
    TermView.normalize_mem_FP
  exact (hasTag_FP 2).ite_mem_FP (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP _) HT) (constFn_mem_FP _)

noncomputable def rawAtom (q : List Bool) : Term := TermView.term (rawAtomCode q)
attribute [local irreducible] rawAtomCode rawAtom

noncomputable def atomCode (q : List Bool) : List Bool :=
  if (rawAtom q).arity≤dimension (pairFst q) then TermView.normalize (rawAtomCode q) else (Term.const 0).toData.toBits
noncomputable def atom (q : List Bool) : Term := TermView.term (atomCode q)
attribute [local irreducible] atomCode atom

theorem atomCode_FP : atomCode ∈ FP := by
  have HA : UnaryFn (fun q => (rawAtom q).arity) := by
    unfold rawAtom
    exact TermArity.arity_unary (source := rawAtomCode) rawAtomCode_FP
  unfold atomCode
  exact (FPPred.le HA (dimension_unary.comp pairFst_mem_FP)).ite_mem_FP
    (mem_FP_comp (f := rawAtomCode) (g := TermView.normalize) rawAtomCode_FP TermView.normalize_mem_FP) (constFn_mem_FP _)

theorem atom_FP : (fun q => (atom q).toData.toBits) ∈ FP := by
  unfold atom
  exact mem_FP_of_eq (mem_FP_comp (f := atomCode) (g := TermView.normalize) atomCode_FP TermView.normalize_mem_FP)
    (fun q => TermView.normalize_eq_term (atomCode q))

theorem atom_scope (q : List Bool) : (atom q).arity≤dimension (pairFst q) := by
  unfold atom atomCode
  split_ifs with H
  · rw [TermView.normalize_eq_term,TermView.term_toBits]
    simpa only [rawAtom] using H
  · rw [TermView.term_toBits]
    exact Nat.zero_le _

noncomputable def family : MonotoneGateSource.Family where
  dimension := dimension
  count := count
  kind := kind
  left := ClosedFormulaGateMetadata.family.left
  right := ClosedFormulaGateMetadata.family.right
  atom := atom

theorem access : MonotoneGateSource.Access family :=
  ⟨dimension_unary,count_unary,kind_binary,ClosedFormulaGateMetadata.access.left,ClosedFormulaGateMetadata.access.right,atom_FP⟩

end LeanCanny.Encoding.OpenFormulaGateMetadata
