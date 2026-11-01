/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotSemantics
/-! # Actual original arithmetic atoms receive exact native sign-label replies -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotCircuit
open ETR LeanCanny.Computation LeanCanny.Connectivity FormulaSignSlotSource
open scoped Classical
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count

theorem requestedCode_eq (q : List Bool) :
    requestedCode q=signCode (FormulaBooleanCircuitSource.requested (FormulaBooleanCircuitSource.readerQuery read q)) := by
  unfold requestedCode FormulaBooleanCircuitSource.requested
  split_ifs <;> rfl

theorem unaryQuery_pair (c label : List Bool) (i : ℕ) (hi : i≤ClosedFormulaGateMetadata.count c) :
    unaryQuery (pair (pair c label) (BinaryNatCode.encode i))=pair (pair c label) (List.replicate i true) := by
  simp only [unaryQuery,pairFst_pair,pairSnd_pair,count,BinaryNatCode.encode,Nat.fromBitsLE_bits,min_eq_left hi]

theorem readerQuery_pair (c label : List Bool) (i : ℕ) :
    FormulaBooleanCircuitSource.readerQuery read (pair (pair c label) (BinaryNatCode.encode i))=
      pair (Input.field 2 c) (BinaryNatCode.encode i) := by
  simp only [FormulaBooleanCircuitSource.readerQuery,read,pairFst_pair,pairSnd_pair]

theorem query_unaryQuery (c label : List Bool) (i : ℕ) (hi : i≤ClosedFormulaGateMetadata.count c) :
    FormulaSignSlotSource.query (unaryQuery (pair (pair c label) (BinaryNatCode.encode i)))=
      FormulaBooleanCircuitSource.readerQuery read (pair (pair c label) (BinaryNatCode.encode i)) := by
  rw [unaryQuery_pair c label i hi,FormulaSignSlotSource.query_pair,readerQuery_pair]

theorem atom_sign (q : List Bool) (env : ℕ → ℝ) (H : (strict (unaryQuery q)).Holds env) :
    atom q=decide (SignType.sign ((term (unaryQuery q)).eval env)=
      FormulaBooleanCircuitSource.requested (FormulaBooleanCircuitSource.readerQuery read q)) := by
  unfold atom
  rw [(strict_sign_iff _ env).mp H,requestedCode_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact signCode_injective.eq_iff

theorem atom_eq_zero (c label : List Bool) (i : ℕ) (hi : i < ClosedFormulaGateMetadata.count c)
    (env : ℕ → ℝ) (H : (stratum (pair c label)).Holds env) (t : Term)
    (hn : FormulaBooleanCircuitSource.node
      (FormulaBooleanCircuitSource.readerQuery read (pair (pair c label) (BinaryNatCode.encode i)))=(Formula.eqZero t).encode)
    (ht : t.arity≤ClosedFormulaGateMetadata.dimension c) :
    atom (pair (pair c label) (BinaryNatCode.encode i))=decide (t.eval env=0) := by
  have HS := stratum_slot (pair c label) env H i (by simpa only [count,pairFst_pair] using hi)
  have HH : (strict (unaryQuery (pair (pair c label) (BinaryNatCode.encode i)))).Holds env := by
    rw [unaryQuery_pair c label i hi.le]
    exact HS
  have HE : term (unaryQuery (pair (pair c label) (BinaryNatCode.encode i)))=t := by
    apply eq_atomic_term
    · rw [query_unaryQuery c label i hi.le]
      exact hn
    · simpa only [unaryQuery,pairFst_pair,dimension] using ht
  have HR := atom_sign _ env HH
  rw [HE,FormulaBooleanCircuitSource.requested_eq_node _ t hn] at HR
  simpa only [sign_eq_zero_iff] using HR

theorem atom_lt_zero (c label : List Bool) (i : ℕ) (hi : i < ClosedFormulaGateMetadata.count c)
    (env : ℕ → ℝ) (H : (stratum (pair c label)).Holds env) (t : Term)
    (hn : FormulaBooleanCircuitSource.node
      (FormulaBooleanCircuitSource.readerQuery read (pair (pair c label) (BinaryNatCode.encode i)))=(Formula.ltZero t).encode)
    (ht : t.arity≤ClosedFormulaGateMetadata.dimension c) :
    atom (pair (pair c label) (BinaryNatCode.encode i))=decide (t.eval env < 0) := by
  have HS := stratum_slot (pair c label) env H i (by simpa only [count,pairFst_pair] using hi)
  have HH : (strict (unaryQuery (pair (pair c label) (BinaryNatCode.encode i)))).Holds env := by
    rw [unaryQuery_pair c label i hi.le]
    exact HS
  have HE : term (unaryQuery (pair (pair c label) (BinaryNatCode.encode i)))=t := by
    apply lt_atomic_term
    · rw [query_unaryQuery c label i hi.le]
      exact hn
    · simpa only [unaryQuery,pairFst_pair,dimension] using ht
  have HR := atom_sign _ env HH
  rw [HE,FormulaBooleanCircuitSource.requested_lt_node _ t hn] at HR
  simpa only [sign_eq_neg_one_iff] using HR

end LeanCanny.Encoding.FormulaSignSlotCircuit
