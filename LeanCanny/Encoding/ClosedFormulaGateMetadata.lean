/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.MonotoneGateSourceBounds
public import LeanCanny.ETR.FormulaBooleanCircuitNodes
public import LeanCanny.Connectivity.InputFP
/-! # Actual canonical formula records supply every native gate-source field

No polynomial evaluator is a premise. The original formula is read from the
canonical connectivity record. Atomic terms are extracted and scoped by the
native arity reader. Unsupported/malformed nodes have the constant false
value. A semantic closed-formula check is still needed for the reduction.
-/
@[expose] public section
namespace LeanCanny.Encoding.ClosedFormulaGateMetadata
open LeanCanny.Computation ETR LeanCanny.Connectivity
open scoped Classical

def dimension (c : List Bool) : ℕ := Codec.unaryValue (Input.field 1 c)
def count (c : List Bool) : ℕ := (FormulaView.normalize (Input.field 2 c)).length

def query (q : List Bool) : List Bool :=
  pair (Input.field 2 (pairFst q)) (BinaryNatCode.encode (MonotoneGateSource.index q))

theorem dimension_unary : UnaryFn dimension := Codec.unaryValue_unary.comp (Input.field_mem_FP 1)
theorem count_unary : UnaryFn count :=
  UnaryFn.comp (f := fun b => (FormulaView.normalize b).length) (g := Input.field 2)
    (UnaryFn.length (f := FormulaView.normalize) FormulaView.normalize_mem_FP) (Input.field_mem_FP 2)

attribute [local irreducible] pair Input.field MonotoneGateSource.index
  Brackets.firstNode Brackets.firstChild Brackets.afterNode Brackets.contents
  FormulaBooleanCircuitSource.arguments FormulaBooleanCircuitSource.termCode

theorem query_FP : query ∈ FP := by
  unfold query
  exact mem_FP_pair (f := Input.field 2 ∘ pairFst)
    (g := fun q => BinaryNatCode.encode (MonotoneGateSource.index q))
    (mem_FP_comp (f := pairFst) (g := Input.field 2) pairFst_mem_FP (Input.field_mem_FP 2))
    (BinaryFn.bits_mem_FP (BinaryFn.ofUnary MonotoneGateSource.index_unary))

attribute [local irreducible] query

def inner (q : List Bool) : List Bool := Brackets.firstNode (FormulaBooleanCircuitSource.arguments (query q))
def innerTag (q : List Bool) : List Bool := Brackets.firstChild (inner q)
def innerTerm (q : List Bool) : List Bool := Brackets.firstNode (Brackets.afterNode (Brackets.contents (inner q)))

attribute [local irreducible] inner innerTag innerTerm

theorem inner_FP : inner ∈ FP := by
  unfold inner
  exact mem_FP_comp (f := FormulaBooleanCircuitSource.arguments ∘ query) (g := Brackets.firstNode)
    (mem_FP_comp (f := query) (g := FormulaBooleanCircuitSource.arguments) query_FP FormulaBooleanCircuitSource.arguments_FP)
    Brackets.firstNode_mem_FP
theorem innerTag_FP : innerTag ∈ FP := by
  unfold innerTag
  exact mem_FP_comp (f := inner) (g := Brackets.firstChild) inner_FP Brackets.firstChild_mem_FP
theorem innerTerm_FP : innerTerm ∈ FP := by
  unfold innerTerm
  exact mem_FP_comp (f := Brackets.afterNode ∘ Brackets.contents ∘ inner) (g := Brackets.firstNode)
    (mem_FP_comp (f := Brackets.contents ∘ inner) (g := Brackets.afterNode)
      (mem_FP_comp (f := inner) (g := Brackets.contents) inner_FP Brackets.contents_mem_FP) Brackets.afterNode_mem_FP)
    Brackets.firstNode_mem_FP

def HasTag (k : ℕ) (q : List Bool) : Prop := FormulaBooleanCircuitSource.HasTag k (query q)
def HasInner (k : ℕ) (q : List Bool) : Prop := innerTag q=(Codec.unary k).toBits
instance (k : ℕ) (q : List Bool) : Decidable (HasTag k q) := inferInstanceAs (Decidable (FormulaBooleanCircuitSource.HasTag k (query q)))
instance (k : ℕ) (q : List Bool) : Decidable (HasInner k q) := inferInstanceAs (Decidable (innerTag q=(Codec.unary k).toBits))

attribute [local irreducible] HasTag HasInner

theorem hasTag_FP (k : ℕ) : FPPred (HasTag k) := by
  unfold HasTag
  exact (FormulaBooleanCircuitSource.hasTag_FP k).comp query_FP
theorem hasInner_FP (k : ℕ) : FPPred (HasInner k) := by
  unfold HasInner
  exact Brackets.stringEq_fppred innerTag_FP (constFn_mem_FP _)

def kind (q : List Bool) : ℕ :=
  if HasTag 1 q then 2 else if HasTag 3 q ∧ HasInner 2 q then 2 else
  if HasTag 3 q ∧ HasInner 0 q then 1 else if HasTag 4 q then 4 else if HasTag 5 q then 5 else 0

theorem kind_binary : BinaryFn kind :=
  BinaryFn.ite (hasTag_FP 1) (BinaryFn.const 2)
    (BinaryFn.ite ((hasTag_FP 3).and (hasInner_FP 2)) (BinaryFn.const 2)
      (BinaryFn.ite ((hasTag_FP 3).and (hasInner_FP 0)) (BinaryFn.const 1)
        (BinaryFn.ite (hasTag_FP 4) (BinaryFn.const 4) (BinaryFn.ite (hasTag_FP 5) (BinaryFn.const 5) (BinaryFn.const 0)))))

theorem kind_ne_three (q : List Bool) : kind q≠3 := by unfold kind; split_ifs <;> decide

def rawAtomCode (q : List Bool) : List Bool :=
  if HasTag 1 q then
    Codec.taggedTwo 3 (Term.const (-1)).toData.toBits
      (Codec.taggedTwo 3 (TermView.normalize (FormulaBooleanCircuitSource.termCode (query q))) (TermView.normalize (FormulaBooleanCircuitSource.termCode (query q))))
  else if HasTag 3 q ∧ HasInner 2 q then TermView.normalize (innerTerm q) else (Term.const (-1)).toData.toBits

theorem rawAtomCode_FP : rawAtomCode ∈ FP := by
  have HT := mem_FP_comp (f := FormulaBooleanCircuitSource.termCode ∘ query) (g := TermView.normalize)
    (mem_FP_comp (f := query) (g := FormulaBooleanCircuitSource.termCode) query_FP FormulaBooleanCircuitSource.termCode_FP)
    TermView.normalize_mem_FP
  exact (hasTag_FP 1).ite_mem_FP (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP _) (Codec.taggedTwo_mem_FP 3 HT HT))
    (((hasTag_FP 3).and (hasInner_FP 2)).ite_mem_FP (mem_FP_comp (f := innerTerm) (g := TermView.normalize) innerTerm_FP TermView.normalize_mem_FP) (constFn_mem_FP _))

noncomputable def rawAtom (q : List Bool) : Term := TermView.term (rawAtomCode q)

attribute [local irreducible] rawAtomCode rawAtom

noncomputable def atomCode (q : List Bool) : List Bool :=
  if (rawAtom q).arity≤dimension (pairFst q) then TermView.normalize (rawAtomCode q) else (Term.const (-1)).toData.toBits

noncomputable def atom (q : List Bool) : Term := TermView.term (atomCode q)

attribute [local irreducible] atomCode atom

theorem atomCode_FP : atomCode ∈ FP := by
  unfold atomCode
  have HA : UnaryFn (fun q => (rawAtom q).arity) := by
    unfold rawAtom
    exact TermArity.arity_unary (source := rawAtomCode) rawAtomCode_FP
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
  left q := FormulaBooleanCircuitSource.left (query q)
  right q := FormulaBooleanCircuitSource.right (query q)
  atom := atom

theorem access : MonotoneGateSource.Access family := by
  have HL : UnaryFn FormulaBooleanCircuitSource.left := ((UnaryFn.length FormulaBooleanCircuitSource.codes_FP).sub (UnaryFn.const 1)).sub FormulaBooleanCircuitSource.firstOffset_unary
  have HR : UnaryFn FormulaBooleanCircuitSource.right := ((UnaryFn.length FormulaBooleanCircuitSource.codes_FP).sub (UnaryFn.const 1)).sub FormulaBooleanCircuitSource.secondOffset_unary
  exact ⟨dimension_unary,count_unary,kind_binary,HL.comp query_FP,HR.comp query_FP,atom_FP⟩

theorem source_FP : (fun c => (MonotoneGateSource.polynomial family c).toData.toBits) ∈ FP := MonotoneGateSource.polynomial_FP family access

theorem source_scope (c : List Bool) : (MonotoneGateSource.polynomial family c).arity≤MonotoneGateSource.outputDimension family c := by
  apply MonotoneGateSource.polynomial_arity
  intro i _
  simpa only [family,pairFst_pair] using atom_scope (pair c (List.replicate i true))

end LeanCanny.Encoding.ClosedFormulaGateMetadata
