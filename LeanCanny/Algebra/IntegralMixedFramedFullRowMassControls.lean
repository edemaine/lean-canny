/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullRowMass
/-! # Native binary ceilings for every full physical sampler row -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalRowBudget
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask

theorem exponent_binary {n S B W D L F H : List Bool→ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hW : UnaryFn W)
    (hD : BinaryFn D) (hL : BinaryFn L) (hF : BinaryFn F) (hH : BinaryFn H) :
    BinaryFn (fun q=>exponent (n q) (S q) (B q) (W q) (D q) (L q) (F q) (H q)) := by
  have hC : BinaryFn (fun q=>sourceC (F q) (H q)) := (hF.mul hH).add (BinaryFn.const 1)
  have hG : BinaryFn (fun q=>bankG (F q) (H q)) := ((hF.add (BinaryFn.const 3)).mul hH).add (BinaryFn.const 1)
  have hA : BinaryFn (fun q=>PhysicalCriticalMassBudget.sourceExponent (n q+1) (W q) (sourceC (F q) (H q))) :=
    ((((BinaryFn.ofUnary (hn.add (UnaryFn.const 1))).mul (BinaryFn.ofUnary hW)).add hC).add
      (BinaryFn.ofUnary (hn.add (UnaryFn.const 1))).size).add (BinaryFn.const 1)
  have hU : BinaryFn (fun q=>normalExponent (S q) (F q) (H q)) :=
    (((BinaryFn.ofUnary hS).add (BinaryFn.const 1)).mul hG).add (BinaryFn.const 2)
  have hR : BinaryFn (fun q=>heightExponent (S q) (B q) (L q) (F q) (H q)) :=
    ((BinaryFn.ofUnary hS).mul (BinaryFn.ofUnary hB)).add
      ((IntegralMixedGlobalHeightBounds.expressionFactor_binary (BinaryFn.ofUnary hS) hL).mul hG)
  have hK : BinaryFn (fun q=>criticalExponent (n q) (S q) (B q) (W q) (D q) (L q) (F q) (H q)) :=
    PhysicalCriticalMassBudget.exponent_binary (hn.add (UnaryFn.const 1)) hA hD hU hR
  have hQ := PaddedIntegralParameterExtension.rowMassHeight_binary (BinaryFn.ofUnary hS) (BinaryFn.ofUnary hB) hH
  exact (BinaryFn.ite (hK.le hQ) hQ hK).of_eq (fun q=>by
    unfold exponent
    split_ifs with h
    · exact (max_eq_right h).symm
    · exact (max_eq_left (by omega)).symm)

theorem familyMass_binary (P : Parameters) (a : Access P) {L F C : List Bool→ℕ}
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (familyMass P L F C) :=
  exponent_binary a.ambient (a.cap.add (UnaryFn.const 1)) a.width a.sourceWidth a.degree hL hF
    (IntegralMixedFramedStepHeight.height_binary a.ambient (a.cap.add (UnaryFn.const 1)) a.width a.sourceWidth
      a.degree hL hF hC (a.cap.add (UnaryFn.const 2)))

end LeanCanny.Algebra.IntegralMixedPhysicalRowBudget
