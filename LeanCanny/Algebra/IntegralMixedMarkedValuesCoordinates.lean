/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerVector
public import Mathlib.Tactic.FinCases

/-! # The chronological marked vector retains the original and two real slacks -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedMarkedValuesCoordinates
open LeanCanny.Encoding LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number values)
open scoped Classical

theorem first_coordinates (n : List Bool→ℕ) (t : List Bool→Term) (R : List Bool→ℕ) (ctx : List Bool)
    (x : ℕ→ℝ) (u v : ℝ) :
    (fun i : Fin (number n ctx+4)=>values n t R ctx x u v i.val)=
      Fin.append (Fin.append (fun i : Fin (number n ctx)=>x i.val) ![u,0]) ![v,0] := by
  funext i
  refine Fin.addCases (m:=number n ctx+2) (n:=2) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=number n ctx) (n:=2) ?_ ?_ j
    · intro k
      simp only [Fin.append_left,Fin.val_castAdd,values,ite_eq_left k.isLt]
    · intro k
      fin_cases k <;> simp [values]
  · intro k
    fin_cases k <;> simp [values]
    split_ifs with hlt heq
    · omega
    · omega
    · rfl

end LeanCanny.Algebra.IntegralMixedMarkedValuesCoordinates
