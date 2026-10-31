/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMonomialTermSource

/-! # Native term factors from original coefficient, denominator, and height readers -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMonomialTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
open IntegralPowerProductBits (factorWord rowWord colWord)

def position (p : List Bool) : ℕ := Nat.fromBitsLE (factorWord p)
def index (p : List Bool) : ℕ := position p - 2

theorem position_binary : BinaryFn position := BinaryFn.fromBits IntegralPowerProductBits.factorWord_FP
theorem index_binary : BinaryFn index := position_binary.sub (BinaryFn.const 2)

def coefficientQuery (p : List Bool) : List Bool := pair (pairFst p) (pairSnd (pairSnd p))
def heightQuery (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (BinaryNatCode.encode (index p)) (pairSnd (pairSnd p)))

theorem coefficientQuery_FP : coefficientQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
theorem heightQuery_FP : heightQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair index_binary.bits_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

def sameIndex (p : List Bool) : Prop := Nat.fromBitsLE (rowWord p) = Nat.fromBitsLE (colWord p)
instance (p : List Bool) : Decidable (sameIndex p) := inferInstanceAs (Decidable (_ = _))
theorem sameIndex_fppred : FPPred sameIndex :=
  (BinaryFn.fromBits IntegralPowerProductBits.rowWord_FP).eq (BinaryFn.fromBits IntegralPowerProductBits.colWord_FP)

def freeIndex (S : Source) (p : List Bool) : Prop := isFree S (pairFst p) (index p)
instance (S : Source) (p : List Bool) : Decidable (freeIndex S p) := inferInstanceAs (Decidable (isFree S _ _))

theorem freeIndex_fppred (S : Source) (a : Access S) : FPPred (freeIndex S) := by
  have HO : BinaryFn (fun p => S.offset (pairFst p)) := a.offset.comp pairFst_mem_FP
  have HF : BinaryFn (fun p => S.free (pairFst p)) := a.free.comp pairFst_mem_FP
  exact (HO.le index_binary).and (index_binary.lt (HO.add HF))

def valid (S : Source) (p : List Bool) : Prop := index p < S.arity (pairFst p)
instance (S : Source) (p : List Bool) : Decidable (valid S p) := inferInstanceAs (Decidable (_ < _))

theorem valid_fppred (S : Source) (a : Access S) : FPPred (valid S) := by
  have HA : BinaryFn (fun p => S.arity (pairFst p)) := (BinaryFn.ofUnary a.arity).comp pairFst_mem_FP
  exact index_binary.lt HA

def scalarProgram {S : Source} (a : Access S) (p : List Bool) : List Bool :=
  if sameIndex p then a.denominator (pairFst p) else []

def unitProgram (S : Source) (p : List Bool) : List Bool :=
  if sameIndex p then ArithmeticBits.one (BinaryNatCode.encode (S.modulus (pairFst p))) else []

theorem scalar_evaluator (S : Source) (a : Access S) (E : SpaceFunction a.denominator) :
    SpaceFunction (scalarProgram a) :=
  (SpaceFunction.branch (fun p => decide (sameIndex p)) sameIndex_fppred.flag_mem_FP
    (E.precompose pairFst pairFst_mem_FP) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun _ => by simp only [scalarProgram, decide_eq_true_eq, Function.comp_apply])

theorem unitProgram_FP (S : Source) (a : Access S) : unitProgram S ∈ FP := by
  have HM : BinaryFn (fun p => S.modulus (pairFst p)) := a.modulus.comp pairFst_mem_FP
  have HO : (fun p => ArithmeticBits.one (BinaryNatCode.encode (S.modulus (pairFst p)))) ∈ FP :=
    mem_FP_comp (f := fun p => BinaryNatCode.encode (S.modulus (pairFst p))) (g := ArithmeticBits.one)
      HM.bits_mem_FP ArithmeticBits.one_mem_FP
  exact sameIndex_fppred.ite_mem_FP HO (constFn_mem_FP [])

def entryProgram (S : Source) (a : Access S) (p : List Bool) : List Bool :=
  if position p = 0 then a.coefficient (coefficientQuery p)
  else if position p = 1 then scalarProgram a p
  else if valid S p then if freeIndex S p then scalarProgram a p else a.height (heightQuery p)
  else unitProgram S p

theorem entry_evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) : SpaceFunction (entryProgram S a) := by
  have Z := scalar_evaluator S a EQ
  have H := EH.precompose heightQuery heightQuery_FP
  have F := SpaceFunction.branch (fun p => decide (freeIndex S p)) (freeIndex_fppred S a).flag_mem_FP Z H
  have V := SpaceFunction.branch (fun p => decide (valid S p)) (valid_fppred S a).flag_mem_FP F
    (SpaceFunction.ofFP _ (unitProgram_FP S a))
  have O := SpaceFunction.branch (fun p => decide (position p = 1)) (position_binary.eq (BinaryFn.const 1)).flag_mem_FP Z V
  exact (SpaceFunction.branch (fun p => decide (position p = 0)) (position_binary.eq (BinaryFn.const 0)).flag_mem_FP
    (EC.precompose coefficientQuery coefficientQuery_FP) O).congr
      (funext fun _ => by simp only [entryProgram, decide_eq_true_eq, Function.comp_apply])

end LeanCanny.Algebra.IntegralMonomialTermBits
