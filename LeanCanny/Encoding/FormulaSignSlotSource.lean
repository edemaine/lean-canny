/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ClosedFormulaGateMetadata
public import LeanCanny.Encoding.FormulaConjunctionWriter
public import LeanCanny.Connectivity.FormulaSignEnvelopes
/-! # Native original-formula sign slots and closed weak-envelope writers

Two bits per original circuit slot select zero, negative or positive. The
fourth code and malformed label widths denote the empty source. Terms are
read literally from the input, and scoped by the native arity reader.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotSource
open ETR LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical

def dimension (c : List Bool) := ClosedFormulaGateMetadata.dimension (pairFst c)
def count (c : List Bool) := ClosedFormulaGateMetadata.count (pairFst c)
def query (q : List Bool) := ClosedFormulaGateMetadata.query (pair (pairFst (pairFst q)) (pairSnd q))
def rawCode (q : List Bool) := FormulaBooleanCircuitSource.termCode (query q)
noncomputable def raw (q : List Bool) := TermView.term (rawCode q)
def slotCode (q : List Bool) := ((pairSnd (pairFst q)).drop (2*(pairSnd q).length)).take 2

theorem dimension_unary : UnaryFn dimension := ClosedFormulaGateMetadata.dimension_unary.comp pairFst_mem_FP
theorem count_unary : UnaryFn count := ClosedFormulaGateMetadata.count_unary.comp pairFst_mem_FP
theorem query_FP : query ∈ FP := by
  unfold query
  exact mem_FP_comp (f := fun q => pair (pairFst (pairFst q)) (pairSnd q))
    (g := ClosedFormulaGateMetadata.query)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) ClosedFormulaGateMetadata.query_FP
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension
  ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.query query

theorem rawCode_FP : rawCode ∈ FP := by
  unfold rawCode
  exact mem_FP_comp (f := query) (g := FormulaBooleanCircuitSource.termCode)
    query_FP FormulaBooleanCircuitSource.termCode_FP

theorem slotCode_FP : slotCode ∈ FP :=
  take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
    ((UnaryFn.const 2).mul (UnaryFn.length pairSnd_mem_FP))) (UnaryFn.const 2)

noncomputable def termCode (q : List Bool) :=
  if (raw q).arity≤dimension (pairFst q) then TermView.normalize (rawCode q) else (Term.const 0).toData.toBits
noncomputable def term (q : List Bool) := TermView.term (termCode q)

attribute [local irreducible] rawCode raw slotCode dimension count

theorem termCode_FP : termCode ∈ FP := by
  unfold termCode
  have HA : UnaryFn (fun q => (raw q).arity) := by
    unfold raw
    exact TermArity.arity_unary (source := rawCode) rawCode_FP
  exact (FPPred.le HA (dimension_unary.comp pairFst_mem_FP)).ite_mem_FP
    (mem_FP_comp rawCode_FP TermView.normalize_mem_FP) (constFn_mem_FP _)

theorem term_FP : (fun q => (term q).toData.toBits) ∈ FP := by
  unfold term
  exact mem_FP_of_eq (mem_FP_comp termCode_FP TermView.normalize_mem_FP) (fun q => TermView.normalize_eq_term _)

theorem term_scope (q : List Bool) : (term q).arity≤dimension (pairFst q) := by
  unfold term termCode
  split_ifs with H
  · rw [TermView.normalize_eq_term,TermView.term_toBits]
    simpa only [raw] using H
  · rw [TermView.term_toBits]
    exact Nat.zero_le _

noncomputable def weak (q : List Bool) : Formula :=
  if slotCode q=[false,false] then .eqZero (term q) else
  if slotCode q=[false,true] then .not (.ltZero (.mul (.const (-1)) (term q))) else
  if slotCode q=[true,false] then .not (.ltZero (term q)) else .falsum
noncomputable def strict (q : List Bool) : Formula :=
  if slotCode q=[false,false] then .eqZero (term q) else
  if slotCode q=[false,true] then .ltZero (term q) else
  if slotCode q=[true,false] then .ltZero (.mul (.const (-1)) (term q)) else .falsum

private theorem iteFormula_FP {P : List Bool → Prop} [DecidablePred P]
    (hP : FPPred P) {a b : List Bool → Formula}
    (ha : (fun q => (a q).encode) ∈ FP) (hb : (fun q => (b q).encode) ∈ FP) :
    (fun q => (if P q then a q else b q).encode) ∈ FP := by
  apply mem_FP_of_eq (hP.ite_mem_FP ha hb)
  intro q
  split_ifs <;> rfl

private theorem negative_FP : (fun q => (Term.mul (.const (-1)) (term q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) term_FP)
    (fun _ => (Term.mul_toBits _ _).symm)

private theorem eq_FP : (fun q => (Formula.eqZero (term q)).encode) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedOne_mem_FP 1 term_FP)
  intro q
  simp only [Codec.taggedOne_toBits,Formula.encode,Formula.toData]
private theorem lt_FP : (fun q => (Formula.ltZero (term q)).encode) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedOne_mem_FP 2 term_FP)
  intro q
  simp only [Codec.taggedOne_toBits,Formula.encode,Formula.toData]
private theorem neglt_FP : (fun q => (Formula.ltZero (.mul (.const (-1)) (term q))).encode) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedOne_mem_FP 2 negative_FP)
  intro q
  simp only [Codec.taggedOne_toBits,Formula.encode,Formula.toData]
private theorem not_FP {f : List Bool → Formula} (H : (fun q => (f q).encode) ∈ FP) :
    (fun q => (Formula.not (f q)).encode) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedOne_mem_FP 3 H)
  intro q
  simp only [Codec.taggedOne_toBits,Formula.encode,Formula.toData]

theorem weak_FP : (fun q => (weak q).encode) ∈ FP := by
  unfold weak
  exact iteFormula_FP (Brackets.stringEq_fppred slotCode_FP (constFn_mem_FP [false,false])) eq_FP
    (iteFormula_FP (Brackets.stringEq_fppred slotCode_FP (constFn_mem_FP [false,true])) (not_FP neglt_FP)
      (iteFormula_FP (Brackets.stringEq_fppred slotCode_FP (constFn_mem_FP [true,false])) (not_FP lt_FP)
        (constFn_mem_FP Formula.falsum.encode)))

theorem strict_FP : (fun q => (strict q).encode) ∈ FP := by
  unfold strict
  exact iteFormula_FP (Brackets.stringEq_fppred slotCode_FP (constFn_mem_FP [false,false])) eq_FP
    (iteFormula_FP (Brackets.stringEq_fppred slotCode_FP (constFn_mem_FP [false,true])) lt_FP
      (iteFormula_FP (Brackets.stringEq_fppred slotCode_FP (constFn_mem_FP [true,false])) neglt_FP
        (constFn_mem_FP Formula.falsum.encode)))

noncomputable def envelope (c : List Bool) : Formula :=
  if (pairSnd c).length=2*count c then FormulaConjunctionWriter.rangeConjunction weak count c else .falsum
noncomputable def stratum (c : List Bool) : Formula :=
  if (pairSnd c).length=2*count c then FormulaConjunctionWriter.rangeConjunction strict count c else .falsum

theorem envelope_FP : (fun c => (envelope c).encode) ∈ FP := by
  unfold envelope
  exact iteFormula_FP (FPPred.eq (UnaryFn.length pairSnd_mem_FP) ((UnaryFn.const 2).mul count_unary))
    (FormulaConjunctionWriter.range_FP weak_FP count_unary) (constFn_mem_FP Formula.falsum.encode)
theorem stratum_FP : (fun c => (stratum c).encode) ∈ FP := by
  unfold stratum
  exact iteFormula_FP (FPPred.eq (UnaryFn.length pairSnd_mem_FP) ((UnaryFn.const 2).mul count_unary))
    (FormulaConjunctionWriter.range_FP strict_FP count_unary) (constFn_mem_FP Formula.falsum.encode)

end LeanCanny.Encoding.FormulaSignSlotSource
