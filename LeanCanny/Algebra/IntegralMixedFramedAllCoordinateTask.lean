/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbeTask
/-! # Independent coordinate and parameter selectors in honest modulus packets

The outer coordinate degree is retained in slot8 and the spatial coordinate
in slot13. The parameter degree remains the coefficient field. Both source
selectors retain their explicit cap hypotheses in the readback theorem.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedAllCoordinateTaskBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedCutProbeTaskBits (parameters original root)

def coordinate (P : Parameters) (q : List Bool) := get P .slot13 (original q)
theorem coordinate_binary (P : Parameters) (a : Access P) : BinaryFn (coordinate P) :=
  (get_binary P a .slot13).comp IntegralMixedFramedCutProbeTaskBits.original_FP

def query (P : Parameters) (L F C : List Bool→ℕ) :=
  IntegralMixedValueFieldQuery.query (parameters P L F C) (IntegralMixedFramedChoiceProbeTaskBits.query P L F C)
    .rawFactor .companion .slot13 (coordinate P)
theorem query_FP (P : Parameters) (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : query P L F C∈FP :=
  IntegralMixedValueFieldQuery.query_FP _ (IntegralMixedFramedCutProbeTaskBits.access P a L F C hL hF hC)
    _ (IntegralMixedFramedChoiceProbeTaskBits.query_FP P a L F C hL hF hC) _ _ _ _ (coordinate_binary P a)

theorem query_root (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    RankedHistoryTask.root (query P L F C q)=root q :=
  (IntegralMixedValueFieldQuery.query_root _ _ _ _ _ _ q).trans (IntegralMixedFramedChoiceProbeTaskBits.query_root P L F C q)
theorem query_birth (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    birth (parameters P L F C) (query P L F C q)=birth P (original q) :=
  (IntegralMixedValueFieldQuery.query_birth _ _ _ _ _ _ q).trans (IntegralMixedFramedChoiceProbeTaskBits.query_birth P L F C q)
theorem query_modulus (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    modulus (parameters P L F C) (query P L F C q)=IntegralMixedFramedCutProbeTaskBits.callerModulus q :=
  (IntegralMixedValueFieldQuery.query_modulus _ _ _ _ _ _ q (by decide)).trans
    (IntegralMixedFramedChoiceProbeTaskBits.query_modulus P L F C q)
theorem query_phase (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) : phase (query P L F C q)=26 :=
  IntegralMixedValueFieldQuery.query_phase _ _ _ _ _ _ q
theorem query_routine (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    IntegralMixedRoutineTaskBits.routine (parameters P L F C) (query P L F C q)=4 :=
  IntegralMixedValueFieldQuery.query_routine _ _ _ _ _ _ q

theorem query_get (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) (f : Field) :
    get (parameters P L F C) f (query P L F C q)=if f=.slot14 then 4 else if f=.slot13 then
      min (coordinate P q) (numericCap (parameters P L F C) (root q)) else
      get (parameters P L F C) f (IntegralMixedFramedChoiceProbeTaskBits.query P L F C q) := by
  rw [query,IntegralMixedValueFieldQuery.query_get,IntegralMixedFramedChoiceProbeTaskBits.query_root]
  rfl

theorem query_coordinate (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hj : coordinate P q≤numericCap (parameters P L F C) (root q)) :
    get (parameters P L F C) .slot13 (query P L F C q)=coordinate P q := by
  simp only [query_get,reduceCtorEq,ite_false,ite_true,min_eq_left hj]
theorem query_choice (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedFramedChoiceProbeTaskBits.requested P q≤numericCap (parameters P L F C) (root q)) :
    get (parameters P L F C) .slot8 (query P L F C q)=IntegralMixedFramedChoiceProbeTaskBits.requested P q := by
  simp only [query_get,IntegralMixedFramedChoiceProbeTaskBits.query_get,reduceCtorEq,ite_false,ite_true,min_eq_left hc]

theorem query_saved_base (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q)=
      IntegralMixedVirtualTaskBits.saved (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.query P L F C q) :=
  (IntegralMixedValueFieldQuery.query_saved _ _ _ _ _ _ q (by decide)).trans
    (IntegralMixedFramedChoiceProbeTaskBits.query_saved_base P L F C q)
theorem query_saved (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (original q)) :
    IntegralMixedFramedRootPullback.key pairFst (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))=
      IntegralMixedVirtualTaskBits.saved P (original q) := by
  rw [query_saved_base]
  exact IntegralMixedFramedCutProbeTaskBits.query_saved P L F C q hc

theorem query_valid (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    IntegralMixedVirtualCaps.valid (parameters P L F C) (query P L F C q)↔IntegralMixedVirtualCaps.valid P (original q) := by
  unfold IntegralMixedVirtualCaps.valid
  rw [query_birth,query_root]
  simp only [parameters,IntegralMixedFramedNormalizationBits.planned,IntegralMixedFramedRootPullback.parameters,
    Function.comp_apply,root,pairFst_pair]
theorem query_context (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (original q)) :
    IntegralMixedVirtualContextBits.context (parameters P L F C) (query P L F C q) := by
  unfold IntegralMixedVirtualContextBits.context
  simp only [query_get,reduceCtorEq,ite_false]
  exact IntegralMixedFramedChoiceProbeTaskBits.query_context P L F C q hc

end LeanCanny.Algebra.IntegralMixedFramedAllCoordinateTaskBits
