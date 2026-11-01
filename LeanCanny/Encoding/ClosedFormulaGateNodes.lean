/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ClosedFormulaGateMetadata
/-! # The native metadata retains the actual closed formula's gates and atomic terms -/
@[expose] public section
namespace LeanCanny.Encoding.ClosedFormulaGateMetadata
open LeanCanny.Computation ETR LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem query_pair (c : List Bool) (i : ℕ) :
    query (pair c (List.replicate i true)) = pair (Input.field 2 c) (BinaryNatCode.encode i) := by
  simp only [query,MonotoneGateSource.index,pairFst_pair,pairSnd_pair,List.length_replicate]

theorem node_at (c pre suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize (Input.field 2 c) = pre ++ p.encode ++ suffix) :
    FormulaBooleanCircuitSource.node (query (pair c (List.replicate
      (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))) = p.encode := by
  rw [query_pair]
  exact FormulaBooleanCircuitSource.node_at _ pre suffix p hc

theorem hasTag_node (q : List Bool) (p : Formula)
    (hn : FormulaBooleanCircuitSource.node (query q)=p.encode) (k : ℕ) :
    HasTag k q ↔ Brackets.firstChild p.encode=(Codec.unary k).toBits := by
  rw [HasTag,FormulaBooleanCircuitSource.HasTag,FormulaBooleanCircuitSource.tag,hn]

theorem kind_eqZero (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.eqZero t).encode) : kind q=2 := by
  have H : HasTag 1 q := by
    rw [hasTag_node q _ hn 1]
    simp [Formula.encode,Formula.toData]
  simp only [kind,ite_eq_left H]

theorem kind_falsum (q : List Bool)
    (hn : FormulaBooleanCircuitSource.node (query q)=Formula.falsum.encode) : kind q=0 := by
  simp [kind,HasTag,FormulaBooleanCircuitSource.HasTag,FormulaBooleanCircuitSource.tag,hn,
    Formula.encode,Formula.toData,Codec.unary_toBits_injective.eq_iff]

theorem kind_and (q : List Bool) (a b : Formula)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.and a b).encode) : kind q=4 := by
  simp [kind,HasTag,FormulaBooleanCircuitSource.HasTag,FormulaBooleanCircuitSource.tag,hn,
    Formula.encode,Formula.toData,Codec.unary_toBits_injective.eq_iff]

theorem kind_or (q : List Bool) (a b : Formula)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.or a b).encode) : kind q=5 := by
  simp [kind,HasTag,FormulaBooleanCircuitSource.HasTag,FormulaBooleanCircuitSource.tag,hn,
    Formula.encode,Formula.toData,Codec.unary_toBits_injective.eq_iff]

theorem inner_not (q : List Bool) (p : Formula)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.not p).encode) : inner q=p.encode := by
  rw [inner,FormulaBooleanCircuitSource.arguments_one _ 3 p.toData hn]
  have H := Brackets.firstNode_toBits_append p.toData []
  simpa only [List.append_nil,Formula.encode] using H

theorem kind_nonnegative (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.not (.ltZero t)).encode) : kind q=2 := by
  have HI := inner_not q (.ltZero t) hn
  simp [kind,HasTag,HasInner,innerTag,HI,FormulaBooleanCircuitSource.HasTag,FormulaBooleanCircuitSource.tag,hn,
    Formula.encode,Formula.toData,Codec.unary_toBits_injective.eq_iff]

theorem kind_verum (q : List Bool)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.not .falsum).encode) : kind q=1 := by
  have HI := inner_not q .falsum hn
  simp [kind,HasTag,HasInner,innerTag,HI,FormulaBooleanCircuitSource.HasTag,FormulaBooleanCircuitSource.tag,hn,
    Formula.encode,Formula.toData,Codec.unary_toBits_injective.eq_iff]

theorem innerTerm_nonnegative (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.not (.ltZero t)).encode) : innerTerm q=t.toData.toBits := by
  rw [innerTerm,inner_not q (.ltZero t) hn]
  simp only [Formula.encode,Formula.toData,Brackets.contents_toBits,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil,Brackets.afterNode_toBits_append]
  have H := Brackets.firstNode_toBits_append t.toData []
  simpa only [List.append_nil] using H

theorem rawAtom_eqZero (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.eqZero t).encode) :
    rawAtom q=.mul (.const (-1)) (.mul t t) := by
  have HT := FormulaBooleanCircuitSource.term_eq_node (query q) t hn
  change TermView.term (FormulaBooleanCircuitSource.termCode (query q))=t at HT
  have HE : HasTag 1 q := by rw [hasTag_node q _ hn 1]; simp [Formula.encode,Formula.toData]
  rw [rawAtom,rawAtomCode,ite_eq_left HE,TermView.normalize_eq_term,HT]
  have HC : Codec.taggedTwo 3 (Term.const (-1)).toData.toBits
      (Codec.taggedTwo 3 t.toData.toBits t.toData.toBits) = (Term.mul (.const (-1)) (.mul t t)).toData.toBits := by
    simp only [Term.mul_toBits]
  rw [HC,TermView.term_toBits]

theorem rawAtom_nonnegative (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.not (.ltZero t)).encode) : rawAtom q=t := by
  have H1 : ¬ HasTag 1 q := by rw [hasTag_node q _ hn 1]; simp [Formula.encode,Formula.toData,Codec.unary_toBits_injective.eq_iff]
  have H3 : HasTag 3 q := by rw [hasTag_node q _ hn 3]; simp [Formula.encode,Formula.toData]
  have H2 : HasInner 2 q := by
    rw [HasInner,innerTag,inner_not q (.ltZero t) hn]
    simp [Formula.encode,Formula.toData]
  rw [rawAtom,rawAtomCode,ite_eq_right H1,ite_eq_left ⟨H3,H2⟩,innerTerm_nonnegative q t hn,
    TermView.normalize_toBits,TermView.term_toBits]

theorem atom_eq_raw (q : List Bool) (h : (rawAtom q).arity≤dimension (pairFst q)) : atom q=rawAtom q := by
  rw [atom,atomCode,ite_eq_left h,TermView.normalize_eq_term,TermView.term_toBits]
  rfl

theorem atom_eqZero (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.eqZero t).encode)
    (ht : t.arity≤dimension (pairFst q)) : atom q=.mul (.const (-1)) (.mul t t) := by
  rw [atom_eq_raw q (by simpa only [rawAtom_eqZero q t hn,Term.arity,max_self,Nat.zero_max] using ht),rawAtom_eqZero q t hn]

theorem atom_nonnegative (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.not (.ltZero t)).encode)
    (ht : t.arity≤dimension (pairFst q)) : atom q=t := by
  rw [atom_eq_raw q (by simpa only [rawAtom_nonnegative q t hn] using ht),rawAtom_nonnegative q t hn]

end LeanCanny.Encoding.ClosedFormulaGateMetadata
