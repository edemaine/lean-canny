/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.BooleanCircuitIndexed
public import LeanCanny.Connectivity.FormulaSignSlotTruth
/-! # Literal subformula truth read from the original finite sign word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotSubformulaTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR BooleanCircuitSpace
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaView.normalize Input.field pair FormulaSignSlotCircuit.atom
  FormulaSignSlotTruth.frozenAtom ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count

def base (p : List Bool) := pairFst p
def family := FormulaSignSlotCircuit.family.comp base
def atom (z : List Bool) := FormulaSignSlotCircuit.atom (pair (base (pairFst z)) (pairSnd z))
theorem base_FP : base ∈ FP := pairFst_mem_FP
theorem atom_FP : (fun z => [atom z]) ∈ FP := mem_FP_comp
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP base_FP) pairSnd_mem_FP) FormulaSignSlotCircuit.atom_FP

def index (p : List Bool) :=
  (FormulaView.normalize (Input.field 2 (pairFst (base p)))).length-1-(pairSnd p).length
theorem index_unary : UnaryFn index := by
  have HB : (fun p => pairFst (base p)) ∈ FP := mem_FP_comp base_FP pairFst_mem_FP
  have HF := mem_FP_comp (mem_FP_comp HB (Input.field_mem_FP 2)) FormulaView.normalize_mem_FP
  exact ((UnaryFn.length HF).sub (UnaryFn.const 1)).sub (UnaryFn.length pairSnd_mem_FP)

def value (p : List Bool) := indexed family atom index p
theorem evaluator : SpaceFunction (fun p => [value p]) :=
  indexed_evaluator family (FormulaSignSlotCircuit.access.comp base base_FP) atom
    (SpaceFunction.ofFP _ atom_FP) index index_unary

theorem packet (c label : List Bool) (env : ℕ → ℝ)
    (H : (FormulaSignSlotSource.stratum (pair c label)).Holds env)
    (p : Formula) (pre suffix : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c) = pre ++ p.encode ++ suffix)
    (hs : p.arity ≤ ClosedFormulaGateMetadata.dimension c) :
    value (pair (pair c label) pre) = decide (p.Holds env) := by
  have HX : index (pair (pair c label) pre) = FormulaBooleanCircuitSource.wire (Input.field 2 c) pre := by
    simp only [index,base,pairFst_pair,pairSnd_pair,FormulaBooleanCircuitSource.wire]
  have HC : family.count (pair (pair c label) pre) = (FormulaView.normalize (Input.field 2 c)).length := by
    change FormulaBooleanCircuitSource.circuit.count (FormulaSignSlotCircuit.read (base (pair (pair c label) pre))) = _
    simp only [base,FormulaSignSlotCircuit.read,pairFst_pair]
    rfl
  have HI : index (pair (pair c label) pre) < family.count (pair (pair c label) pre) := by
    rw [HX,HC]
    unfold FormulaBooleanCircuitSource.wire
    rw [hc]
    have HP : 0 < p.encode.length := by simp [Formula.encode]
    simp only [List.length_append]
    omega
  rw [value,indexed_eq_wire family atom index _ HI,HX]
  change wireValue (FormulaSignSlotCircuit.family.comp base) atom (pair (pair c label) pre)
    (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) = _
  rw [wireValue_comp FormulaSignSlotCircuit.family base atom FormulaSignSlotCircuit.atom _ _
    (fun k _ => by simp only [atom,base,pairFst_pair,pairSnd_pair])]
  simp only [base,pairFst_pair]
  change wireValue (FormulaBooleanCircuitSource.circuit.comp FormulaSignSlotCircuit.read) FormulaSignSlotCircuit.atom
    (pair c label) (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) = _
  rw [wireValue_comp FormulaBooleanCircuitSource.circuit FormulaSignSlotCircuit.read FormulaSignSlotCircuit.atom
    (FormulaSignSlotTruth.frozenAtom c label) _ _
    (fun k _ => by simp only [FormulaSignSlotTruth.frozenAtom,pairSnd_pair])]
  have HR : FormulaSignSlotCircuit.read (pair c label) = Input.field 2 c := by
    simp only [FormulaSignSlotCircuit.read,pairFst_pair]
  rw [HR]
  exact FormulaSignSlotTruth.wire_truth c label env H p pre suffix hc hs

end LeanCanny.Encoding.FormulaSignSlotSubformulaTest
