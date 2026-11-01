/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.OpenFormulaGateMetadata
/-! # Actual constructor and original-term identities for native open margin gates -/
@[expose] public section
namespace LeanCanny.Encoding.OpenFormulaGateMetadata
open ETR LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem kind_lt (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (ClosedFormulaGateMetadata.query q)=(Formula.ltZero t).encode) : kind q=2 := by
  have HT : ClosedFormulaGateMetadata.HasTag 2 q := by
    rw [ClosedFormulaGateMetadata.hasTag_node q _ hn 2]
    simp [Formula.encode,Formula.toData]
  simp only [kind,ite_eq_left HT]

theorem kind_false (q : List Bool)
    (hn : FormulaBooleanCircuitSource.node (ClosedFormulaGateMetadata.query q)=Formula.falsum.encode) : kind q=0 := by
  simp [kind,ClosedFormulaGateMetadata.HasTag,FormulaBooleanCircuitSource.HasTag,FormulaBooleanCircuitSource.tag,
    hn,Formula.encode,Formula.toData,Codec.unary_toBits_injective.eq_iff]

theorem kind_and (q : List Bool) (a b : Formula)
    (hn : FormulaBooleanCircuitSource.node (ClosedFormulaGateMetadata.query q)=(Formula.and a b).encode) : kind q=4 := by
  simp [kind,ClosedFormulaGateMetadata.HasTag,FormulaBooleanCircuitSource.HasTag,FormulaBooleanCircuitSource.tag,
    hn,Formula.encode,Formula.toData,Codec.unary_toBits_injective.eq_iff]

theorem kind_or (q : List Bool) (a b : Formula)
    (hn : FormulaBooleanCircuitSource.node (ClosedFormulaGateMetadata.query q)=(Formula.or a b).encode) : kind q=5 := by
  simp [kind,ClosedFormulaGateMetadata.HasTag,FormulaBooleanCircuitSource.HasTag,FormulaBooleanCircuitSource.tag,
    hn,Formula.encode,Formula.toData,Codec.unary_toBits_injective.eq_iff]

theorem kind_verum (q : List Bool)
    (hn : FormulaBooleanCircuitSource.node (ClosedFormulaGateMetadata.query q)=(Formula.not .falsum).encode) : kind q=1 := by
  have HI:=ClosedFormulaGateMetadata.inner_not q .falsum hn
  simp [kind,ClosedFormulaGateMetadata.HasTag,ClosedFormulaGateMetadata.HasInner,ClosedFormulaGateMetadata.innerTag,
    HI,FormulaBooleanCircuitSource.HasTag,FormulaBooleanCircuitSource.tag,hn,Formula.encode,Formula.toData,
    Codec.unary_toBits_injective.eq_iff]

theorem rawAtom_lt (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (ClosedFormulaGateMetadata.query q)=(Formula.ltZero t).encode) :
    rawAtom q=.mul (.const (-1)) t := by
  have HT:=FormulaBooleanCircuitSource.term_lt_node (ClosedFormulaGateMetadata.query q) t hn
  change TermView.term (FormulaBooleanCircuitSource.termCode (ClosedFormulaGateMetadata.query q))=t at HT
  have H2 : ClosedFormulaGateMetadata.HasTag 2 q := by
    rw [ClosedFormulaGateMetadata.hasTag_node q _ hn 2]
    simp [Formula.encode,Formula.toData]
  unfold rawAtom rawAtomCode
  rw [ite_eq_left H2,TermView.normalize_eq_term,HT]
  have HC : Codec.taggedTwo 3 (Term.const (-1)).toData.toBits t.toData.toBits=(Term.mul (.const (-1)) t).toData.toBits :=
    (Term.mul_toBits _ _).symm
  rw [HC,TermView.term_toBits]

theorem atom_eq_raw (q : List Bool) (h : (rawAtom q).arity≤ClosedFormulaGateMetadata.dimension (pairFst q)) : atom q=rawAtom q := by
  unfold atom atomCode
  rw [ite_eq_left h,TermView.normalize_eq_term,TermView.term_toBits]
  rfl

theorem atom_lt (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (ClosedFormulaGateMetadata.query q)=(Formula.ltZero t).encode)
    (ht : t.arity≤ClosedFormulaGateMetadata.dimension (pairFst q)) : atom q=.mul (.const (-1)) t := by
  rw [atom_eq_raw q (by simpa only [rawAtom_lt q t hn,Term.arity,Nat.zero_max] using ht),rawAtom_lt q t hn]

end LeanCanny.Encoding.OpenFormulaGateMetadata
