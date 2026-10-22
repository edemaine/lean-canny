/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationCompilerAtomEncoding

/-! # The polynomial-time encoded step of the equation compiler -/

@[expose] public section

namespace LeanCanny.ETR.EquationCompiler

open LeanCanny.Encoding Turing.MultiTapeTM

def todoBits (state : List Bool) : List Bool := pairFst state
def valuesBits (state : List Bool) : List Bool := pairFst (pairSnd state)
def counterBits (state : List Bool) : List Bool := pairSnd (pairSnd state)
def frame (state : List Bool) : List Bool := pairFst (todoBits state)
def source (state : List Bool) : List Bool := (frame state).drop 1

theorem todoBits_mem_FP : todoBits ∈ FP := by polytime [todoBits]
theorem valuesBits_mem_FP : valuesBits ∈ FP := by polytime [valuesBits]
theorem counterBits_mem_FP : counterBits ∈ FP := by polytime [counterBits]
theorem frame_mem_FP : frame ∈ FP := by polytime [frame, todoBits]
theorem source_mem_FP : source ∈ FP := by polytime [source, frame, todoBits]

def emit (todo values counter : List Bool) : List Bool := pair todo (pair values counter)

def binaryStep (disjoin : Bool) (state : List Bool) : List Bool :=
  emit (pair (false :: NNF.second (source state))
      (pair (false :: NNF.third (source state)) (pair [true, disjoin] (pairSnd (todoBits state)))))
    (valuesBits state) (counterBits state)

def atomicStep (state : List Bool) : List Bool :=
  let out := atomBits (pair (source state) (counterBits state))
  emit (pairSnd (todoBits state)) (pair out (valuesBits state)) (pairFst out)

def joinStep (disjoin : Bool) (state : List Bool) : List Bool :=
  let values := valuesBits state
  if values = [] ∨ pairSnd values = [] then state
  else
    let packet := pair (pairFst (pairSnd values)) (pairFst values)
    let out := if disjoin then EquationSystem.disjunctionBits packet else EquationSystem.conjunctionBits packet
    emit (pairSnd (todoBits state)) (pair out (pairSnd (pairSnd values))) (pairFst out)

@[program_certificate]
theorem todoBits_computable : ComputableTidilyInPolyTime todoBits encBits encBits := todoBits_mem_FP

@[program_certificate]
theorem valuesBits_computable : ComputableTidilyInPolyTime valuesBits encBits encBits := valuesBits_mem_FP

@[program_certificate]
theorem counterBits_computable : ComputableTidilyInPolyTime counterBits encBits encBits := counterBits_mem_FP

@[program_certificate]
theorem frame_computable : ComputableTidilyInPolyTime frame encBits encBits := frame_mem_FP

@[program_certificate]
theorem source_computable : ComputableTidilyInPolyTime source encBits encBits := source_mem_FP

@[program_certificate]
theorem third_computable : ComputableTidilyInPolyTime NNF.third encBits encBits := NNF.third_mem_FP

@[program_certificate]
theorem conjunctionBits_computable :
    ComputableTidilyInPolyTime EquationSystem.conjunctionBits encBits encBits :=
  EquationSystem.conjunctionBits_mem_FP

@[program_certificate]
theorem disjunctionBits_computable :
    ComputableTidilyInPolyTime EquationSystem.disjunctionBits encBits encBits :=
  EquationSystem.disjunctionBits_mem_FP

theorem binaryStep_mem_FP (disjoin : Bool) : binaryStep disjoin ∈ FP := by
  polytime [binaryStep, emit]

theorem atomicStep_mem_FP : atomicStep ∈ FP := by polytime [atomicStep, emit]

theorem joinStep_mem_FP (disjoin : Bool) : joinStep disjoin ∈ FP := by
  cases disjoin <;> polytime [joinStep, emit]

def stepBits (state : List Bool) : List Bool :=
  if todoBits state = [] then state
  else if (frame state)[0]?.getD false then
    if (frame state)[1]?.getD false then joinStep true state else joinStep false state
  else if HasTag 4 (source state) then binaryStep false state
  else if HasTag 5 (source state) then binaryStep true state
  else atomicStep state

@[program_certificate]
theorem binaryStep_computable (disjoin : Bool) :
    ComputableTidilyInPolyTime (binaryStep disjoin) encBits encBits := binaryStep_mem_FP disjoin

@[program_certificate]
theorem atomicStep_computable : ComputableTidilyInPolyTime atomicStep encBits encBits := atomicStep_mem_FP

@[program_certificate]
theorem joinStep_computable (disjoin : Bool) :
    ComputableTidilyInPolyTime (joinStep disjoin) encBits encBits := joinStep_mem_FP disjoin

theorem stepBits_mem_FP : stepBits ∈ FP := by
  polytime [stepBits]

@[simp] theorem pair_ne_nil (a b : List Bool) : pair a b ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [pair_length, List.length_nil] at hl
  omega

@[simp] theorem todoBits_encode (s : State) :
    todoBits s.encode = DynamicTreeFold.stackBits Instruction.encode s.todo := by
  simp [todoBits, State.encode]

@[simp] theorem valuesBits_encode (s : State) :
    valuesBits s.encode = DynamicTreeFold.stackBits EquationSystem.encode s.values := by
  simp [valuesBits, State.encode]

@[simp] theorem counterBits_encode (s : State) : counterBits s.encode = (Codec.unary s.next).toBits := by
  simp [counterBits, State.encode]

@[simp] theorem frame_encode_cons (i : Instruction) (todo : List Instruction)
    (values : List EquationSystem) (next : ℕ) :
    frame (State.encode ⟨i :: todo, values, next⟩) = i.encode := by
  simp [frame, DynamicTreeFold.stackBits]

@[simp] theorem source_visit (p : SignedFormula) (todo : List Instruction)
    (values : List EquationSystem) (next : ℕ) :
    source (State.encode ⟨.visit p :: todo, values, next⟩) = p.toFormula.encode := by
  simp [source, Instruction.encode]

@[simp] theorem binaryStep_and (p q : SignedFormula) (todo : List Instruction)
    (values : List EquationSystem) (next : ℕ) :
    binaryStep false (State.encode ⟨.visit (.and p q) :: todo, values, next⟩) =
      State.encode ⟨.visit p :: .visit q :: .join false :: todo, values, next⟩ := by
  simp [binaryStep, emit, State.encode, Instruction.encode, frame, source, todoBits, valuesBits,
    counterBits, DynamicTreeFold.stackBits, SignedFormula.toFormula, Formula.encode, Formula.toData,
    NNF.second, NNF.third, Brackets.remainingChildren_toBits, Brackets.firstChild_toBits]

@[simp] theorem binaryStep_or (p q : SignedFormula) (todo : List Instruction)
    (values : List EquationSystem) (next : ℕ) :
    binaryStep true (State.encode ⟨.visit (.or p q) :: todo, values, next⟩) =
      State.encode ⟨.visit p :: .visit q :: .join true :: todo, values, next⟩ := by
  simp [binaryStep, emit, State.encode, Instruction.encode, frame, source, todoBits, valuesBits,
    counterBits, DynamicTreeFold.stackBits, SignedFormula.toFormula, Formula.encode, Formula.toData,
    NNF.second, NNF.third, Brackets.remainingChildren_toBits, Brackets.firstChild_toBits]

@[simp] theorem atomicStep_encode (p : SignedFormula) (todo : List Instruction)
    (values : List EquationSystem) (next : ℕ) (hp : Atomic p) :
    atomicStep (State.encode ⟨.visit p :: todo, values, next⟩) =
      State.encode ⟨todo, p.equations next :: values, (p.equations next).next⟩ := by
  simp only [atomicStep, source_visit, counterBits_encode, atomBits_encode p next hp,
    todoBits_encode, valuesBits_encode, DynamicTreeFold.stackBits, pairSnd_pair]
  simp [emit, State.encode, DynamicTreeFold.stackBits, EquationSystem.encode]

@[simp] theorem joinStep_encode (disjoin : Bool) (todo : List Instruction)
    (b a : EquationSystem) (values : List EquationSystem) (next : ℕ) :
    joinStep disjoin (State.encode ⟨.join disjoin :: todo, b :: a :: values, next⟩) =
      (step ⟨.join disjoin :: todo, b :: a :: values, next⟩).encode := by
  cases disjoin <;>
    simp only [joinStep, valuesBits_encode, todoBits_encode, DynamicTreeFold.stackBits,
      pair_ne_nil, or_self, ite_false, pairFst_pair, pairSnd_pair,
      Bool.false_eq_true, ite_true, EquationSystem.conjunctionBits_encode,
      EquationSystem.disjunctionBits_encode]
  all_goals simp [emit, State.encode, DynamicTreeFold.stackBits, EquationSystem.encode, step]

/-- The bitstring step implements the typed state transition on every encoded state. -/
theorem stepBits_encode (s : State) : stepBits s.encode = (step s).encode := by
  rcases s with ⟨todo, values, next⟩
  cases todo with
  | nil => simp [stepBits, step, DynamicTreeFold.stackBits]
  | cons instruction todo =>
      cases instruction with
      | visit p =>
          cases p <;>
            simp [stepBits, DynamicTreeFold.stackBits_eq_nil_iff, Instruction.encode,
              HasTag, SignedFormula.toFormula, Formula.firstChild_encode, Formula.constructorTag,
              Codec.unary_toBits_injective.eq_iff, step]
          all_goals exact atomicStep_encode _ _ _ _ (by trivial)
      | join disjoin =>
          cases values with
          | nil =>
              cases disjoin <;> simp [stepBits, joinStep, step, Instruction.encode, DynamicTreeFold.stackBits]
          | cons b values =>
              cases values with
              | nil =>
                  cases disjoin <;>
                    simp [stepBits, joinStep, step, Instruction.encode, DynamicTreeFold.stackBits]
              | cons a values =>
                  cases disjoin <;>
                    simp only [stepBits, todoBits_encode, DynamicTreeFold.stackBits_eq_nil_iff,
                      List.cons_ne_nil, ite_false, frame_encode_cons, Instruction.encode,
                      List.getElem?_cons_zero, List.getElem?_cons_succ,
                      Option.getD_some, Bool.false_eq_true, ite_true, joinStep_encode]

end LeanCanny.ETR.EquationCompiler
