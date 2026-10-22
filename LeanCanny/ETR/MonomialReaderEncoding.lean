/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.MonomialReaderMachine
public import LeanCanny.ETR.MonomialCountFP
public import LeanCanny.Encoding.BinaryDivFP
public import LeanCanny.Encoding.BinarySubFP

/-!
# FP transitions for selected-monomial traversal

The packet retains the original input and pairs a task stack with an
accumulator. Every task stores one raw subtree and a binary monomial index.
Only leaf accumulation is a parameter; internal transitions use certified
counting, comparison, subtraction, quotient, and remainder routines.
-/

@[expose] public section

namespace LeanCanny.ETR.MonomialReader

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

def Task.encode (q : Task) : List Bool := pair q.term.toData.toBits (BinaryNatCode.encode q.index)
def State.encode {R : Type*} (code : R → List Bool) (s : State R) : List Bool :=
  pair (DynamicTreeFold.stackBits Task.encode s.todo) (code s.value)

def todoBits (p : List Bool) : List Bool := pairFst (pairSnd p)
def accumulator (p : List Bool) : List Bool := pairSnd (pairSnd p)
def headTask (p : List Bool) : List Bool := pairFst (todoBits p)
def termBits (p : List Bool) : List Bool := pairFst (headTask p)
def indexBits (p : List Bool) : List Bool := pairSnd (headTask p)
def restBits (p : List Bool) : List Bool := pairSnd (todoBits p)
def leftTerm (p : List Bool) : List Bool := NNF.second (termBits p)
def rightTerm (p : List Bool) : List Bool := NNF.third (termBits p)
def leftCount (p : List Bool) : List Bool := MonomialCount.read (leftTerm p)
def rightCount (p : List Bool) : List Bool := MonomialCount.read (rightTerm p)

def emit (p tasks value : List Bool) : List Bool := pair (pairFst p) (pair tasks value)
def leftTasks (p : List Bool) : List Bool := pair (pair (leftTerm p) (BinaryNat.normalize (indexBits p))) (restBits p)
def rightTasks (p : List Bool) : List Bool :=
  pair (pair (rightTerm p) (BinaryNat.sub (pair (indexBits p) (leftCount p)))) (restBits p)
def productTasks (p : List Bool) : List Bool :=
  pair (pair (leftTerm p) (BinaryNat.div (pair (indexBits p) (rightCount p))))
    (pair (pair (rightTerm p) (BinaryNat.mod (pair (indexBits p) (rightCount p)))) (restBits p))
def atomQuery (p : List Bool) : List Bool := pair (pairFst p) (pair (termBits p) (accumulator p))

def stepBits (atom : List Bool → List Bool) (p : List Bool) : List Bool :=
  if todoBits p = [] then p
  else if NNF.HasTwo 2 (termBits p) then
    emit p (if Nat.fromBitsLE (indexBits p) < Nat.fromBitsLE (leftCount p) then leftTasks p else rightTasks p) (accumulator p)
  else if NNF.HasTwo 3 (termBits p) then emit p (productTasks p) (accumulator p)
  else emit p (restBits p) (atom (atomQuery p))

theorem todoBits_mem_FP : todoBits ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem accumulator_mem_FP : accumulator ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem headTask_mem_FP : headTask ∈ FP := mem_FP_comp todoBits_mem_FP pairFst_mem_FP
theorem termBits_mem_FP : termBits ∈ FP := mem_FP_comp headTask_mem_FP pairFst_mem_FP
theorem indexBits_mem_FP : indexBits ∈ FP := mem_FP_comp headTask_mem_FP pairSnd_mem_FP
theorem restBits_mem_FP : restBits ∈ FP := mem_FP_comp todoBits_mem_FP pairSnd_mem_FP
theorem leftTerm_mem_FP : leftTerm ∈ FP := by
  have h := mem_FP_comp termBits_mem_FP NNF.second_mem_FP
  refine mem_FP_of_eq (g := leftTerm) h ?_
  intro p
  simp only [Function.comp_apply, leftTerm]
theorem rightTerm_mem_FP : rightTerm ∈ FP := by
  have h := mem_FP_comp termBits_mem_FP NNF.third_mem_FP
  refine mem_FP_of_eq (g := rightTerm) h ?_
  intro p
  simp only [Function.comp_apply, rightTerm]
theorem leftCount_mem_FP : leftCount ∈ FP := by
  have h := mem_FP_comp leftTerm_mem_FP MonomialCount.read_mem_FP
  refine mem_FP_of_eq (g := leftCount) h ?_
  intro p
  simp only [Function.comp_apply, leftCount]
theorem rightCount_mem_FP : rightCount ∈ FP := by
  have h := mem_FP_comp rightTerm_mem_FP MonomialCount.read_mem_FP
  refine mem_FP_of_eq (g := rightCount) h ?_
  intro p
  simp only [Function.comp_apply, rightCount]

theorem emit_mem_FP {tasks value : List Bool → List Bool} (ht : tasks ∈ FP) (hv : value ∈ FP) :
    (fun p => emit p (tasks p) (value p)) ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_pair ht hv)

theorem leftTasks_mem_FP : leftTasks ∈ FP := by
  have hr := mem_FP_comp indexBits_mem_FP BinaryNat.normalize_mem_FP
  have h := mem_FP_pair (mem_FP_pair leftTerm_mem_FP hr) restBits_mem_FP
  refine mem_FP_of_eq (g := leftTasks) h ?_
  intro p
  simp only [Function.comp_apply, leftTasks]

theorem rightTasks_mem_FP : rightTasks ∈ FP := by
  have hr := mem_FP_comp (mem_FP_pair indexBits_mem_FP leftCount_mem_FP) BinaryNat.sub_mem_FP
  have h := mem_FP_pair (mem_FP_pair rightTerm_mem_FP hr) restBits_mem_FP
  refine mem_FP_of_eq (g := rightTasks) h ?_
  intro p
  simp only [Function.comp_apply, rightTasks]

theorem productTasks_mem_FP : productTasks ∈ FP := by
  have hargs := mem_FP_pair indexBits_mem_FP rightCount_mem_FP
  have hl := mem_FP_comp hargs BinaryNat.div_mem_FP
  have hr := mem_FP_comp hargs BinaryNat.mod_mem_FP
  have h := mem_FP_pair (mem_FP_pair leftTerm_mem_FP hl) (mem_FP_pair (mem_FP_pair rightTerm_mem_FP hr) restBits_mem_FP)
  refine mem_FP_of_eq (g := productTasks) h ?_
  intro p
  simp only [Function.comp_apply, productTasks]

theorem atomQuery_mem_FP : atomQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair termBits_mem_FP accumulator_mem_FP)

theorem stepBits_mem_FP {atom : List Bool → List Bool} (ha : atom ∈ FP) : stepBits atom ∈ FP := by
  have hchoose := (BinaryNat.lt_fppred indexBits_mem_FP leftCount_mem_FP).ite_mem_FP leftTasks_mem_FP rightTasks_mem_FP
  have hadd := emit_mem_FP hchoose accumulator_mem_FP
  have hmul := emit_mem_FP productTasks_mem_FP accumulator_mem_FP
  have hleaf := emit_mem_FP restBits_mem_FP (mem_FP_comp atomQuery_mem_FP ha)
  have h := (stringEq_fppred todoBits_mem_FP (constFn_mem_FP [])).ite_mem_FP id_mem_FP
    (((NNF.hasTwo_fppred 2).comp termBits_mem_FP).ite_mem_FP hadd
      (((NNF.hasTwo_fppred 3).comp termBits_mem_FP).ite_mem_FP hmul hleaf))
  refine mem_FP_of_eq (g := stepBits atom) h ?_
  intro p
  simp only [stepBits, Function.comp_apply]
  rfl

end LeanCanny.ETR.MonomialReader
