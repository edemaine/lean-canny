/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMonomialTermSpace
public import LeanCanny.Algebra.IntegralPowerProductRecursiveStage

/-! # Recursive original coefficients and retained-height term factors

Coefficient and frozen-height factors request one child. Integer scalar
and padding factors are computed locally from the FP denominator residue.
The actual monomial product then uses the retained-power product stage.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMonomialTermBits.EntryStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def request (S : Source) (p : List Bool) : Prop :=
  position p = 0 ∨ (position p ≠ 1 ∧ valid S p ∧ ¬freeIndex S p)
instance (S : Source) (p : List Bool) : Decidable (request S p) := inferInstanceAs (Decidable (_ ∨ _))

theorem request_FP (S : Source) (a : Access S) : FPPred (request S) :=
  (position_binary.eq (BinaryFn.const 0)).or
    (((position_binary.eq (BinaryFn.const 1)).not).and ((valid_fppred S a).and (freeIndex_fppred S a).not))

theorem scalar_FP (S : Source) (a : Access S) (hd : a.denominator ∈ FP) : scalarProgram a ∈ FP :=
  sameIndex_fppred.ite_mem_FP (mem_FP_comp (f := pairFst) (g := a.denominator) pairFst_mem_FP hd) (constFn_mem_FP [])

noncomputable def program (S : Source) (a : Access S)
    (coefficientTask heightTask : List Bool → List Bool) : SingleCall.Program where
  request p := decide (request S p)
  query p := if position p = 0 then coefficientTask (coefficientQuery p) else heightTask (heightQuery p)
  immediate p := if position p = 1 ∨ valid S p then scalarProgram a p else unitProgram S p
  finish := pairSnd

theorem controls (S : Source) (a : Access S) (hd : a.denominator ∈ FP)
    (coefficientTask heightTask : List Bool → List Bool) (hc : coefficientTask ∈ FP) (hh : heightTask ∈ FP) :
    (program S a coefficientTask heightTask).Controls := by
  have HQ := (position_binary.eq (BinaryFn.const 0)).ite_mem_FP
    (mem_FP_comp (f := coefficientQuery) (g := coefficientTask) coefficientQuery_FP hc)
    (mem_FP_comp (f := heightQuery) (g := heightTask) heightQuery_FP hh)
  have HI := ((position_binary.eq (BinaryFn.const 1)).or (valid_fppred S a)).ite_mem_FP
    (scalar_FP S a hd) (unitProgram_FP S a)
  exact ⟨(request_FP S a).flag_mem_FP, HQ, HI, pairSnd_mem_FP⟩

attribute [local irreducible] scalarProgram unitProgram

theorem value_eq (S : Source) (a : Access S) (coefficientTask heightTask answer : List Bool → List Bool)
    (hc : ∀ q, answer (coefficientTask q) = a.coefficient q)
    (hh : ∀ q, answer (heightTask q) = a.height q) (p : List Bool) :
    (program S a coefficientTask heightTask).value answer p = entryProgram S a p := by
  by_cases h0 : position p = 0 <;> by_cases h1 : position p = 1 <;>
    by_cases hv : valid S p <;> by_cases hf : freeIndex S p <;>
    simp_all [SingleCall.Program.value, program, request, entryProgram]

theorem requests_iff (S : Source) (a : Access S) (coefficientTask heightTask answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p child : List Bool) :
    (program S a coefficientTask heightTask).controller.Requests answer budget p child ↔
      request S p ∧ child = if position p = 0 then coefficientTask (coefficientQuery p) else heightTask (heightQuery p) := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

end LeanCanny.Algebra.IntegralMonomialTermBits.EntryStage

namespace LeanCanny.Algebra.IntegralMonomialTermBits.ProductStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

noncomputable def controller (S : Source) (a : Access S) (task : List Bool → List Bool) :=
  IntegralPowerProductBits.ProductStage.controller (family S) (familyAccess S a) task

theorem certificates (S : Source) (a : Access S) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (controller S a task).Certificates (encQ := encBits) (encS := encBits) :=
  IntegralPowerProductBits.ProductStage.certificates (family S) (familyAccess S a) task ht

theorem output_when_halted (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin ((IntegralPowerProductBits.productFamily (family S)).power.dimension c)),
      answer (task (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((IntegralPowerProductBits.productFamily (family S)).power.matrix c i j))
    (c : List Bool) (t : ℕ)
    (hh : (controller S a task).halted (((controller S a task).reference answer)^[t] ((controller S a task).initial c)) = true) :
    (controller S a task).output (((controller S a task).reference answer)^[t] ((controller S a task).initial c)) = S.value c :=
  (IntegralPowerProductBits.ProductStage.output_when_halted (family S) (familyAccess S a) task answer he c t hh).trans
    (congrFun (family_value S) c)

end LeanCanny.Algebra.IntegralMonomialTermBits.ProductStage
