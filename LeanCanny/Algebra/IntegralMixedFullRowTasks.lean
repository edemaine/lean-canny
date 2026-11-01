/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFullRowTaskBounds
public import LeanCanny.Algebra.IntegralMixedOriginalScaleStage

/-! # Concrete lower and scalar tasks restoring a full value-test row

The equation asks the actual frozen-low stage 12 and scalar `a*Q^D`.
A gradient asks cleared derivative stage 8 and scalar `a*Q^D*D`.
The lower query uses the canonically repacked exponent and selected free
derivative. Repeated native field updates preserve the same ROOT, physical
prefix, source context and literal caller modulus.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullRowTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open scoped Classical

noncomputable abbrev family (P : Parameters) (F : Family) := IntegralMixedVirtualTaskBits.family P F
noncomputable abbrev indices (P : Parameters) (F : Family) := IntegralMixedVirtualTaskBits.indices P F
noncomputable def width (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  IntegralMixedGridValue.width ((family P F).spatial q) ((family P F).rule q)
noncomputable abbrev equation (P : Parameters) (F : Family) := IntegralMixedFullRowMultiplier.isEquation (family P F) (indices P F)
noncomputable abbrev lowTarget (P : Parameters) (F : Family) :=
  IntegralMixedFullRowMultiplier.lowTarget (family P F) (indices P F) (width P F)

noncomputable def derivativeTask (P : Parameters) (F : Family) (p : Phase) :=
  IntegralMixedValueFieldQuery.query P id .critical p .derivative (fun q => ((indices P F).coordinate q).val)
noncomputable def targetTask (P : Parameters) (F : Family) (p : Phase) :=
  IntegralMixedValueFieldQuery.query P (derivativeTask P F p) .critical p .target (lowTarget P F)
noncomputable def taskAt (P : Parameters) (F : Family) (p : Phase) (expression : ℕ) :=
  IntegralMixedValueFieldQuery.query P (targetTask P F p) .critical p .expression (fun _ => expression)

noncomputable def lowTask (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if equation P F q then taskAt P F .frozenLower 0 q else taskAt P F .clearedGridSum 1 q
noncomputable def scalarTask (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if equation P F q then IntegralMixedOriginalScaleBits.query P q else IntegralMixedScalarQueryBits.commonLeading P q

theorem width_unary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : UnaryFn (width P F) :=
  IntegralMixedValueDeterminantMetadata.width_unary (family P F) (indices P F) (IntegralMixedVirtualTaskBits.metadata P a F h)
theorem equation_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (equation P F) :=
  IntegralMixedFullRowMultiplier.isEquation_FP _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)
theorem lowTarget_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (lowTarget P F) :=
  IntegralMixedFullRowMultiplier.lowTarget_binary _ _ _ (IntegralMixedVirtualTaskBits.metadata P a F h) (width_unary P a F h)

theorem derivativeTask_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : Phase) : derivativeTask P F p ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (IntegralMixedVirtualTaskBits.metadata P a F h).coordinate
theorem targetTask_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : Phase) : targetTask P F p ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (derivativeTask_FP P a F h p) _ _ _ _ (lowTarget_binary P a F h)
theorem taskAt_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : Phase) (x : ℕ) : taskAt P F p x ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (targetTask_FP P a F h p) _ _ _ _ (BinaryFn.const x)
theorem lowTask_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : lowTask P F ∈ FP :=
  (equation_FP P a F h).ite_mem_FP (taskAt_FP P a F h .frozenLower 0) (taskAt_FP P a F h .clearedGridSum 1)
theorem scalarTask_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : scalarTask P F ∈ FP :=
  (equation_FP P a F h).ite_mem_FP (IntegralMixedOriginalScaleBits.query_FP P a)
    (IntegralMixedScalarQueryBits.scalarQuery_FP P a .monomialFactor)

theorem derivative_root (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    RankedHistoryTask.root (derivativeTask P F p q) = RankedHistoryTask.root q :=
  IntegralMixedValueFieldQuery.query_root P id _ _ _ _ q
theorem target_root (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    RankedHistoryTask.root (targetTask P F p q) = RankedHistoryTask.root q :=
  (IntegralMixedValueFieldQuery.query_root P _ _ _ _ _ q).trans (derivative_root P F p q)
theorem task_root (P : Parameters) (F : Family) (p : Phase) (x : ℕ) (q : List Bool) :
    RankedHistoryTask.root (taskAt P F p x q) = RankedHistoryTask.root q :=
  (IntegralMixedValueFieldQuery.query_root P _ _ _ _ _ q).trans (target_root P F p q)

theorem task_birth (P : Parameters) (F : Family) (p : Phase) (x : ℕ) (q : List Bool) :
    birth P (taskAt P F p x q) = birth P q :=
  (IntegralMixedValueFieldQuery.query_birth P _ _ _ _ _ q).trans
    ((IntegralMixedValueFieldQuery.query_birth P _ _ _ _ _ q).trans
      (IntegralMixedValueFieldQuery.query_birth P id _ _ _ _ q))

theorem task_get (P : Parameters) (F : Family) (p : Phase) (x : ℕ) (q : List Bool) (f : Field) :
    get P f (taskAt P F p x q) =
      if f = .slot14 then 1 else
      if f = .expression then min x (numericCap P (RankedHistoryTask.root q)) else
      if f = .target then min (lowTarget P F q) (numericCap P (RankedHistoryTask.root q)) else
      if f = .derivative then min ((indices P F).coordinate q).val (numericCap P (RankedHistoryTask.root q)) else get P f q := by
  rw [taskAt, IntegralMixedValueFieldQuery.query_get, target_root]
  rw [targetTask, IntegralMixedValueFieldQuery.query_get, derivative_root]
  rw [derivativeTask, IntegralMixedValueFieldQuery.query_get]
  cases f <;> rfl

theorem task_saved (P : Parameters) (F : Family) (p : Phase) (x : ℕ) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (taskAt P F p x q) = IntegralMixedVirtualTaskBits.saved P q := by
  apply IntegralMixedVirtualTaskBits.saved_invariance
  · exact task_root P F p x q
  · exact task_birth P F p x q
  · simp only [task_get, reduceCtorEq, ite_false]

theorem task_modulus (P : Parameters) (F : Family) (p : Phase) (x : ℕ) (q : List Bool) :
    modulus P (taskAt P F p x q) = modulus P q := by
  unfold modulus
  simp only [task_get, reduceCtorEq, ite_false]

theorem task_fields (P : Parameters) (F : Family) (h : RootGeometry P F) (p : Phase) (x : ℕ)
    (hx : x ≤ 1) (q : List Bool) :
    get P .target (taskAt P F p x q) = lowTarget P F q ∧
    get P .derivative (taskAt P F p x q) = ((indices P F).coordinate q).val ∧
    get P .expression (taskAt P F p x q) = x := by
  have HC : 1 ≤ numericCap P (RankedHistoryTask.root q) := Nat.succ_le_of_lt (numericCap_pos P _)
  simp only [task_get, reduceCtorEq, ite_false, ite_true,
    min_eq_left (IntegralMixedFullRowTaskBounds.lowTarget_cap P F h (width P F) q),
    min_eq_left (IntegralMixedFullRowTaskBounds.coordinate_cap P F h q), min_eq_left (hx.trans HC), and_self]

end LeanCanny.Algebra.IntegralMixedFullRowTasks
