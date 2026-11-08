/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexTermMachine
public import LeanCanny.ETR.ComplexCircuitBuilders
public import LeanCanny.Encoding.DynamicTreeFold
public import LeanCanny.Tactic.PolyTime

/-! # Native source-circuit instruction encoding -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Source.Machine
open LeanCanny.Encoding LeanCanny.Encoding.Brackets Turing.MultiTapeTM

def Instruction.encode : Instruction → List Bool
  | .visit t => false :: t.toData.toBits
  | .join multiply => [true, multiply]

def State.encode (s : State) : List Bool :=
  pair (DynamicTreeFold.stackBits Instruction.encode s.todo)
    (pair (DynamicTreeFold.stackBits (fun i => List.replicate i true) s.values)
      (pair (List.replicate s.next true) (forest s.result)))

def todoBits (s : List Bool) : List Bool := pairFst s
def valuesBits (s : List Bool) : List Bool := pairFst (pairSnd s)
def counterBits (s : List Bool) : List Bool := pairFst (pairSnd (pairSnd s))
def resultBits (s : List Bool) : List Bool := pairSnd (pairSnd (pairSnd s))
def frame (s : List Bool) : List Bool := pairFst (todoBits s)
def sourceBits (s : List Bool) : List Bool := (frame s).drop 1
def counter (s : List Bool) : ℕ := (counterBits s).length
def rightValue (s : List Bool) : ℕ := (pairFst (valuesBits s)).length
def leftValue (s : List Bool) : ℕ := (pairFst (pairSnd (valuesBits s))).length
def varIndex (s : List Bool) : ℕ := Codec.unaryValue (NNF.second (sourceBits s))

@[program_certificate] theorem todoBits_mem_FP : ComputableTidilyInPolyTime todoBits encBits encBits := by polytime [todoBits]
@[program_certificate] theorem valuesBits_mem_FP : ComputableTidilyInPolyTime valuesBits encBits encBits := by polytime [valuesBits]
@[program_certificate] theorem counterBits_mem_FP : ComputableTidilyInPolyTime counterBits encBits encBits := by polytime [counterBits]
@[program_certificate] theorem resultBits_mem_FP : ComputableTidilyInPolyTime resultBits encBits encBits := by polytime [resultBits]
@[program_certificate] theorem frame_mem_FP : ComputableTidilyInPolyTime frame encBits encBits := by polytime [frame]
@[program_certificate] theorem sourceBits_mem_FP : ComputableTidilyInPolyTime sourceBits encBits encBits := by polytime [sourceBits]

attribute [local irreducible] todoBits valuesBits counterBits resultBits frame sourceBits

theorem counter_unary : UnaryFn counter := (UnaryFn.length counterBits_mem_FP).of_eq (fun _ => rfl)
theorem rightValue_unary : UnaryFn rightValue :=
  (UnaryFn.length (mem_FP_comp (f := valuesBits) (g := pairFst) valuesBits_mem_FP pairFst_mem_FP)).of_eq (fun _ => rfl)
theorem leftValue_unary : UnaryFn leftValue :=
  (UnaryFn.length (mem_FP_comp (f := valuesBits) (g := fun b => pairFst (pairSnd b)) valuesBits_mem_FP
    (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))).of_eq (fun _ => rfl)
theorem varIndex_unary : UnaryFn varIndex :=
  UnaryFn.of_eq (UnaryFn.comp (f := Codec.unaryValue) (g := fun s => NNF.second (sourceBits s))
    Codec.unaryValue_unary (mem_FP_comp (f := sourceBits) (g := NNF.second)
      sourceBits_mem_FP NNF.second_mem_FP)) (fun _ => rfl)

attribute [local irreducible] counter rightValue leftValue varIndex

def emit (todo values next result : List Bool) : List Bool := pair todo (pair values (pair next result))

def constantStep (s : List Bool) : List Bool :=
  emit (pairSnd (todoBits s)) (pair (counterBits s) (valuesBits s)) (counterBits s ++ [true])
    (resultBits s ++ constantGateBits (counter s) (sourceBits s))

def variableStep (s : List Bool) : List Bool :=
  emit (pairSnd (todoBits s)) (pair (List.replicate (varIndex s) true) (valuesBits s))
    (counterBits s) (resultBits s)

def binaryStep (multiply : Bool) (s : List Bool) : List Bool :=
  emit (pair (false :: NNF.second (sourceBits s))
      (pair (false :: NNF.third (sourceBits s)) (pair [true, multiply] (pairSnd (todoBits s)))))
    (valuesBits s) (counterBits s) (resultBits s)

def joinStep (multiply : Bool) (s : List Bool) : List Bool :=
  if valuesBits s = [] ∨ pairSnd (valuesBits s) = [] then s
  else emit (pairSnd (todoBits s))
    (pair (counterBits s) (pairSnd (pairSnd (valuesBits s)))) (counterBits s ++ [true])
    (resultBits s ++ arithmeticGateBits (if multiply then 2 else 1) (counter s) (leftValue s) (rightValue s))

@[program_certificate] theorem constantStep_mem_FP : ComputableTidilyInPolyTime constantStep encBits encBits := by
  have hc := constantGateBits_mem_FP counter_unary sourceBits_mem_FP
  have ht := mem_FP_comp todoBits_mem_FP pairSnd_mem_FP
  have hv := mem_FP_pair counterBits_mem_FP valuesBits_mem_FP
  have hn := appendFn_mem_FP counterBits_mem_FP (constFn_mem_FP [true])
  exact mem_FP_of_eq (mem_FP_pair ht (mem_FP_pair hv
    (mem_FP_pair hn (appendFn_mem_FP resultBits_mem_FP hc)))) (fun _ => rfl)

@[program_certificate] theorem variableStep_mem_FP : ComputableTidilyInPolyTime variableStep encBits encBits := by
  have ht := mem_FP_comp todoBits_mem_FP pairSnd_mem_FP
  have hv := mem_FP_pair (varIndex_unary.replicate_mem_FP true) valuesBits_mem_FP
  exact mem_FP_of_eq (mem_FP_pair ht (mem_FP_pair hv
    (mem_FP_pair counterBits_mem_FP resultBits_mem_FP))) (fun _ => rfl)

@[program_certificate] theorem binaryStep_mem_FP (multiply : Bool) : ComputableTidilyInPolyTime (binaryStep multiply) encBits encBits := by
  polytime [binaryStep, emit]

@[program_certificate] theorem joinStep_mem_FP (multiply : Bool) : ComputableTidilyInPolyTime (joinStep multiply) encBits encBits := by
  have hg := arithmeticGateBits_mem_FP (if multiply then 2 else 1) counter_unary leftValue_unary rightValue_unary
  have ht := mem_FP_comp todoBits_mem_FP pairSnd_mem_FP
  have hrest := mem_FP_comp valuesBits_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hv := mem_FP_pair counterBits_mem_FP hrest
  have hn := appendFn_mem_FP counterBits_mem_FP (constFn_mem_FP [true])
  have hyes := mem_FP_pair ht (mem_FP_pair hv (mem_FP_pair hn (appendFn_mem_FP resultBits_mem_FP hg)))
  have he := (stringEq_fppred valuesBits_mem_FP (constFn_mem_FP [])).or
    (stringEq_fppred (mem_FP_comp valuesBits_mem_FP pairSnd_mem_FP) (constFn_mem_FP []))
  exact mem_FP_of_eq (he.ite_mem_FP id_mem_FP hyes) (fun _ => rfl)

def HasTag (tag : ℕ) (bits : List Bool) : Prop := firstChild bits = (Codec.unary tag).toBits
instance (tag : ℕ) (bits : List Bool) : Decidable (HasTag tag bits) := inferInstanceAs (Decidable (_ = _))

theorem hasTag_fppred (tag : ℕ) : FPPred (HasTag tag) :=
  stringEq_fppred firstChild_mem_FP (constFn_mem_FP _)

def stepBits (s : List Bool) : List Bool :=
  if todoBits s = [] then s
  else if (frame s)[0]?.getD false then
    if (frame s)[1]?.getD false then joinStep true s else joinStep false s
  else if HasTag 2 (sourceBits s) then binaryStep false s
  else if HasTag 3 (sourceBits s) then binaryStep true s
  else if HasTag 1 (sourceBits s) then variableStep s
  else constantStep s

theorem stepBits_mem_FP : stepBits ∈ FP := by
  have he := stringEq_fppred todoBits_mem_FP (constFn_mem_FP [])
  have hf := FPPred.getBit frame_mem_FP (UnaryFn.const 0)
  have hm := FPPred.getBit frame_mem_FP (UnaryFn.const 1)
  have ht (k : ℕ) := (hasTag_fppred k).comp sourceBits_mem_FP
  exact mem_FP_of_eq (he.ite_mem_FP id_mem_FP
    (hf.ite_mem_FP (hm.ite_mem_FP (joinStep_mem_FP true) (joinStep_mem_FP false))
      ((ht 2).ite_mem_FP (binaryStep_mem_FP false) ((ht 3).ite_mem_FP (binaryStep_mem_FP true)
        ((ht 1).ite_mem_FP variableStep_mem_FP constantStep_mem_FP))))) (fun _ => rfl)

@[simp] theorem pair_ne_nil (a b : List Bool) : pair a b ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [pair_length, List.length_nil] at hl
  omega

private theorem constantGateBits_data (out : ℕ) (z : ℤ) :
    constantGateBits out (Data.l [Codec.unary 0, Codec.integer z]).toBits = (Gate.constant out z).encode :=
  constantGateBits_encode out z

theorem stepBits_encode (s : State) : stepBits s.encode = (step s).encode := by
  rcases s with ⟨todo, values, next, result⟩
  cases todo with
  | nil => simp [stepBits, step, State.encode, todoBits, DynamicTreeFold.stackBits]
  | cons ins rest =>
    cases ins with
    | visit t =>
      cases t <;>
        simp [stepBits, constantStep, variableStep, binaryStep, emit, step, State.encode,
          Instruction.encode, DynamicTreeFold.stackBits, todoBits, valuesBits, counterBits, resultBits,
          frame, sourceBits, counter, varIndex, HasTag, Term.toData, firstChild_toBits,
          NNF.second, NNF.third, remainingChildren_toBits, Codec.unaryValue,
          Codec.unary_toBits_injective.eq_iff, constantGateBits_data, forest,
          List.replicate_succ']
    | join multiply =>
      cases values with
      | nil => simp [stepBits, joinStep, step, State.encode, todoBits, valuesBits, frame,
          Instruction.encode, DynamicTreeFold.stackBits]
      | cons right tail => cases tail with
        | nil => simp [stepBits, joinStep, step, State.encode, todoBits, valuesBits, frame,
            Instruction.encode, DynamicTreeFold.stackBits]
        | cons left values =>
          cases multiply <;>
            simp [stepBits, joinStep, emit, step, State.encode, Instruction.encode,
              DynamicTreeFold.stackBits, todoBits, valuesBits, counterBits, resultBits,
              frame, counter, leftValue, rightValue, addGateBits_encode, mulGateBits_encode,
              forest, List.replicate_succ']

end LeanCanny.ETR.ComplexCircuit.Source.Machine
