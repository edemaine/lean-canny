/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationCompilerBounds
public import LeanCanny.Encoding.DynamicTreeFold

/-!
# Literal byte bounds for the equation compiler's complete state

Both stacks use self-delimiting pairs with their tails in the undoubled field.
Encoding a deep stack therefore charges its entries linearly. The complete
state, including pending formulas, old equation systems, and all counters, has
a cubic bit-length bound throughout the bounded formula compilation run.
-/

@[expose] public section

namespace LeanCanny.ETR
open Complexity

theorem SignedFormula.toFormula_dataSize_le (p : SignedFormula) :
    p.toFormula.toData.size ≤ 20 * p.budget := by
  induction p <;>
    simp only [toFormula, Formula.toData, Data.cons_size, Codec.unary_size,
      Data.size_empty, budget] <;> omega

namespace EquationCompiler
open LeanCanny.Encoding

def Instruction.encode : Instruction → List Bool
  | .visit p => false :: p.toFormula.encode
  | .join disjoin => [true, disjoin]

def State.encode (s : State) : List Bool :=
  pair (DynamicTreeFold.stackBits Instruction.encode s.todo)
    (pair (DynamicTreeFold.stackBits EquationSystem.encode s.values) (Codec.unary s.next).toBits)

theorem programStack_length_le (todo : List Instruction) :
    (DynamicTreeFold.stackBits Instruction.encode todo).length ≤ 44 * programBudget todo := by
  induction todo with
  | nil => simp [DynamicTreeFold.stackBits, programBudget]
  | cons instruction todo ih =>
      cases instruction with
      | visit p =>
          have hs := p.toFormula_dataSize_le
          have hp := p.budget_pos
          simp only [DynamicTreeFold.stackBits, pair_length, Instruction.encode,
            List.length_cons, Formula.encode, Data.length_toBits, programBudget]
          omega
      | join disjoin =>
          simp only [DynamicTreeFold.stackBits, pair_length, Instruction.encode,
            List.length_cons, List.length_nil, programBudget]
          omega

theorem valueStack_length_le (values : List EquationSystem) (next : ℕ)
    (h : ∀ a ∈ values, a.next ≤ next) :
    (DynamicTreeFold.stackBits EquationSystem.encode values).length ≤
      2 * valueSize values + (8 * next + 18) * values.length := by
  induction values with
  | nil => simp [DynamicTreeFold.stackBits, valueSize]
  | cons a values ih =>
      have ha := h a (List.mem_cons_self ..)
      have hr := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
      simp only [DynamicTreeFold.stackBits, pair_length, EquationSystem.encode_length,
        valueSize, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem State.encode_length_le (s : State) (h : s.CounterOk) :
    s.encode.length ≤ 88 * programBudget s.todo + 4 * valueSize s.values +
      (16 * s.next + 36) * s.values.length + 2 * s.next + 6 := by
  have ht := programStack_length_le s.todo
  have hv := valueStack_length_le s.values s.next h.1
  simp only [State.encode, pair_length, Data.length_toBits, Codec.unary_size]
  calc
    _ ≤ 2 * (44 * programBudget s.todo) + 2 +
        (2 * (2 * valueSize s.values + (8 * s.next + 18) * s.values.length) + 2 +
          (2 * s.next + 2)) := by omega
    _ = _ := by ring

/-- Every intermediate state has polynomial literal encoded length, not just
the final equation system. This includes both stacks and every unary index. -/
theorem formula_run_encode_length_le (p : Formula) (fuel : ℕ)
    (hfuel : fuel ≤ 2 * p.encode.length) :
    (run (p.toSigned true) p.encode.length fuel).encode.length ≤
      10000 * (p.encode.length + 1) ^ 3 := by
  let n := p.encode.length
  let s := run (p.toSigned true) n fuel
  have he := State.encode_length_le s (run_counterOk (p.toSigned true) n fuel)
  have hb : programBudget s.todo ≤ n := by
    apply (run_programBudget_le (p.toSigned true) n fuel).trans
    simpa only [n, Formula.encode, Data.length_toBits] using p.toSigned_budget_le true
  have hv : s.values.length ≤ 2 * n := (run_valueCount_le _ _ _).trans hfuel
  have hn : s.next ≤ 3 * n := by
    have hnext := run_next_le (p.toSigned true) n fuel
    dsimp only [s]
    omega
  have hs : valueSize s.values ≤ 1000 * (n + 1) ^ 3 := formula_run_valueSize_le p fuel hfuel
  have hm := Nat.mul_le_mul (show 16 * s.next + 36 ≤ 48 * n + 36 by omega) hv
  change s.encode.length ≤ 10000 * (n + 1) ^ 3
  calc
    _ ≤ 88 * n + 4 * (1000 * (n + 1) ^ 3) + (48 * n + 36) * (2 * n) + 2 * (3 * n) + 6 := by omega
    _ ≤ _ := by nlinarith [Nat.zero_le (n ^ 3)]

end EquationCompiler
end LeanCanny.ETR
