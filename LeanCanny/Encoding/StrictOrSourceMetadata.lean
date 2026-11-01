/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.StrictOrTraversalCorrect
public import LeanCanny.Encoding.TermForestIndex
public import LeanCanny.Encoding.ClosedFormulaGateMetadata
/-! # Actual canonical input fields supply every native strict-OR source control -/
@[expose] public section
namespace LeanCanny.Encoding.StrictOrSourceMetadata
open LeanCanny.Computation ETR LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field pairFst pairSnd

def dimension := ClosedFormulaGateMetadata.dimension
def raw (c : List Bool) : List Bool := StrictOrTraversal.forest (Input.field 2 c)
def count (c : List Bool) : ℕ := (raw c).length
def query (q : List Bool) : List Bool := pair (raw (pairFst q)) (pairSnd q)
noncomputable def rawAtom (q : List Bool) : Term := TermForestIndex.term (query q)

theorem dimension_unary : UnaryFn dimension := ClosedFormulaGateMetadata.dimension_unary
theorem raw_FP : raw ∈ FP := mem_FP_comp (Input.field_mem_FP 2) StrictOrTraversal.forest_FP
theorem count_unary : UnaryFn count := UnaryFn.length raw_FP
theorem query_FP : query ∈ FP := mem_FP_pair (mem_FP_comp (f := pairFst) (g := raw) pairFst_mem_FP raw_FP) pairSnd_mem_FP

attribute [local irreducible] dimension raw count query rawAtom

noncomputable def atomCode (q : List Bool) : List Bool :=
  if (rawAtom q).arity≤dimension (pairFst q) then TermView.normalize (TermForestIndex.word (query q)) else (Term.const 0).toData.toBits
noncomputable def atom (q : List Bool) : Term := TermView.term (atomCode q)

attribute [local irreducible] atomCode atom

theorem atomCode_FP : atomCode ∈ FP := by
  have HW := mem_FP_comp query_FP TermForestIndex.word_FP
  have HA : UnaryFn (fun q => (rawAtom q).arity) := by
    unfold rawAtom TermForestIndex.term
    exact TermArity.arity_unary (source := fun q => TermForestIndex.word (query q)) HW
  unfold atomCode
  exact (FPPred.le HA (dimension_unary.comp pairFst_mem_FP)).ite_mem_FP
    (mem_FP_comp HW TermView.normalize_mem_FP) (constFn_mem_FP _)

theorem atom_FP : (fun q => (atom q).toData.toBits) ∈ FP := by
  unfold atom
  exact mem_FP_of_eq (mem_FP_comp atomCode_FP TermView.normalize_mem_FP)
    (fun q => TermView.normalize_eq_term (atomCode q))

theorem atom_scope (q : List Bool) : (atom q).arity≤dimension (pairFst q) := by
  unfold atom atomCode
  split_ifs with H
  · rw [TermView.normalize_eq_term,TermView.term_toBits]
    simpa only [rawAtom,TermForestIndex.term] using H
  · rw [TermView.term_toBits]
    exact Nat.zero_le _

noncomputable def family : MonotoneGateSource.Family where
  dimension := dimension
  count := count
  kind _ := 0
  left _ := 0
  right _ := 0
  atom := atom

theorem access : MonotoneGateSource.Access family :=
  ⟨dimension_unary,count_unary,BinaryFn.const 0,UnaryFn.const 0,UnaryFn.const 0,atom_FP⟩

theorem raw_eq {p : Formula} (hp : StrictOrSyntax.Strict p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) : raw c=SumSquares.forest (StrictOrSyntax.atoms p) := by
  have HE:=StrictOrTraversal.forest_encode hp
  simpa only [raw,StrictOrTraversal.forest,StrictOrTraversal.init,hc,FormulaView.normalize_encode] using HE

theorem rawAtom_pair {p : Formula} (hp : StrictOrSyntax.Strict p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (i : ℕ) :
    rawAtom (pair c (List.replicate i true))=((StrictOrSyntax.atoms p)[i]?).getD (.const 0) := by
  unfold rawAtom query
  rw [pairFst_pair,pairSnd_pair,raw_eq hp c hc]
  exact TermForestIndex.term_pair _ i

theorem atom_eq_raw (q : List Bool) (h : (rawAtom q).arity≤dimension (pairFst q)) : atom q=rawAtom q := by
  unfold atom atomCode
  rw [ite_eq_left h,TermView.normalize_eq_term,TermView.term_toBits]
  unfold rawAtom TermForestIndex.term
  rfl

theorem atom_pair {p : Formula} (hp : StrictOrSyntax.Strict p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤dimension c) (i : ℕ) :
    atom (pair c (List.replicate i true))=((StrictOrSyntax.atoms p)[i]?).getD (.const 0) := by
  apply (atom_eq_raw _ ?_).trans (rawAtom_pair hp c hc i)
  rw [rawAtom_pair hp c hc,pairFst_pair]
  by_cases HI : i < (StrictOrSyntax.atoms p).length
  · rw [List.getElem?_eq_getElem HI,Option.getD_some]
    exact StrictOrSyntax.atoms_scope hp _ hs _ (List.getElem_mem HI)
  · rw [List.getElem?_eq_none (Nat.le_of_not_gt HI),Option.getD_none]
    exact Nat.zero_le _

end LeanCanny.Encoding.StrictOrSourceMetadata
