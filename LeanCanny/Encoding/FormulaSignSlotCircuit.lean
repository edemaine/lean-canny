/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotLabels
public import LeanCanny.ETR.FormulaBooleanCircuitCorrect
/-! # Native original Boolean evaluation on fixed-width sign-slot labels

The circuit retains arbitrary original NOT/AND/OR gates. Atomic replies are
read directly from the proposed sign bits, without a real or polynomial evaluator.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotCircuit
open ETR LeanCanny.Computation LeanCanny.Connectivity FormulaSignSlotSource
open scoped Classical
attribute [local irreducible] pair Input.field

def read (c : List Bool) := Input.field 2 (pairFst c)
theorem read_FP : read ∈ FP := by
  unfold read
  exact mem_FP_comp (f := pairFst) (g := Input.field 2) pairFst_mem_FP (Input.field_mem_FP 2)

def family : BooleanCircuitSpace.Family := FormulaBooleanCircuitSource.circuit.comp read
theorem access : BooleanCircuitSpace.Access family := FormulaBooleanCircuitSource.circuit_access.comp read read_FP

def unaryQuery (q : List Bool) := pair (pairFst q)
  (List.replicate (min (Nat.fromBitsLE (pairSnd q)) (count (pairFst q))) true)
theorem unaryQuery_FP : unaryQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (UnaryFn.fromBitsLE_min pairSnd_mem_FP (count_unary.comp pairFst_mem_FP)).mem_FP

def requestedCode (q : List Bool) : List Bool :=
  if FormulaBooleanCircuitSource.HasTag 2 (FormulaBooleanCircuitSource.readerQuery read q)
    then signCode .neg else signCode .zero

theorem requestedCode_FP : requestedCode ∈ FP :=
  ((FormulaBooleanCircuitSource.hasTag_FP 2).comp (FormulaBooleanCircuitSource.readerQuery_FP read read_FP)).ite_mem_FP
    (constFn_mem_FP (signCode .neg)) (constFn_mem_FP (signCode .zero))

attribute [local irreducible] read family unaryQuery requestedCode

def atom (q : List Bool) : Bool := decide (slotCode (unaryQuery q)=requestedCode q)

theorem atom_FP : (fun q => [atom q]) ∈ FP :=
  (Brackets.stringEq_fppred (mem_FP_comp unaryQuery_FP slotCode_FP) requestedCode_FP).flag_mem_FP

def language : Language := BooleanCircuitSpace.language family atom

theorem decider : SpaceDecider language :=
  BooleanCircuitSpace.decider family access atom (SpaceFunction.ofFP _ atom_FP)

theorem evaluator : SpaceFunction (fun c => [BooleanCircuitSpace.value family atom c]) :=
  BooleanCircuitSpace.evaluator family access atom (SpaceFunction.ofFP _ atom_FP)

end LeanCanny.Encoding.FormulaSignSlotCircuit
