/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalCompanionChildren
/-! # One current physical critical coefficient supplies each companion child -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalUpperBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev CriticalMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 →
    isPhase .criticalCoefficient q → get P .slot15 q = 1 → answer q = (critical P F).value q

theorem critical_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : IntegralMixedPhysicalComponentBits.Matches P F answer) : CriticalMatches P F answer := by
  intro q hv hr hp hx
  exact hm .criticalCoefficient q (by decide) ((IntegralMixedPhysicalContextBits.selected_iff P .criticalCoefficient q).mpr
    ⟨(IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .criticalCoefficient q).mpr ⟨hv, hr, hp⟩, hx⟩)

theorem scalarDegree_cap (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F) (q : List Bool) :
    (scalarFamily P F).scalarDegree q ≤ numericCap P (RankedHistoryTask.root q) := by
  change 2 ^ F.width (IntegralMixedPhysicalTaskBits.saved P q) ≤ _
  rw [g.width]
  exact (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.1

theorem coefficientTask_value (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F) (q : List Bool) :
    (critical P F).value (coefficientTask P F q) = residueBits
      ((scalarFamily P F).coefficient q (IntegralScalarGeneratorBits.index (scalarFamily P F) q)
        ((scalarFamily P F).oldRow q) ((scalarFamily P F).oldCol q)) := by
  have HK : IntegralScalarGeneratorBits.index (scalarFamily P F) q ≤ numericCap P (RankedHistoryTask.root q) :=
    (Nat.sub_le _ _).trans (((scalarFamily P F).row q).isLt.le.trans (scalarDegree_cap P F g q))
  have HR : ((scalarFamily P F).oldRow q).val ≤ numericCap P (RankedHistoryTask.root q) :=
    ((scalarFamily P F).oldRow q).isLt.le.trans (IntegralMixedPhysicalCaps.rank_cap P F g q)
  have HT : ((scalarFamily P F).oldCol q).val ≤ numericCap P (RankedHistoryTask.root q) :=
    ((scalarFamily P F).oldCol q).isLt.le.trans (IntegralMixedPhysicalCaps.rank_cap P F g q)
  change (critical P F).value (coefficientTask P F q) = residueBits
    ((family P F).coefficient q (IntegralScalarGeneratorBits.index (scalarFamily P F) q)
      ((scalarFamily P F).oldRow q) ((scalarFamily P F).oldCol q))
  rw [coefficient_entry]
  exact writer_value P F q _ _ _ HK HR HT

theorem coefficient_reply (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : CriticalMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hx : get P .slot15 q = 1) :
    answer (coefficientTask P F q) = residueBits
      ((scalarFamily P F).coefficient q (IntegralScalarGeneratorBits.index (scalarFamily P F) q)
        ((scalarFamily P F).oldRow q) ((scalarFamily P F).oldCol q)) := by
  have HP : pairFst (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P F) q) = q := pairFst_pair _ _
  have HV : IntegralMixedVirtualCaps.valid P (coefficientTask P F q) := by
    unfold IntegralMixedVirtualCaps.valid coefficientTask
    rw [Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_birth,
      IntegralMixedCoefficientQueryBits.writer_root, HP]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P (coefficientTask P F q) = 1 :=
    IntegralMixedCoefficientQueryBits.writer_routine P .critical .criticalCoefficient _
  have HC : isPhase .criticalCoefficient (coefficientTask P F q) :=
    IntegralMixedCoefficientQueryBits.writer_phase P .critical .criticalCoefficient _
  have HX : get P .slot15 (coefficientTask P F q) = 1 := by
    unfold coefficientTask
    rw [Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_get]
    simpa only [reduceCtorEq, ite_false, HP] using hx
  exact (hm _ HV HR HC HX).trans (coefficientTask_value P F g q)

noncomputable def selected (P : Parameters) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 6 ∧
    isPhase .companion q ∧ get P .slot15 q = 1)

theorem selected_FP (P : Parameters) (a : Access P) : (fun q => [selected P q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 6)).and
      ((isPhase_FP .companion).and ((get_binary P a .slot15).eq (BinaryFn.const 1))))).flag_mem_FP

theorem selected_iff (P : Parameters) (q : List Bool) : selected P q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 6 ∧
      isPhase .companion q ∧ get P .slot15 q = 1 := by simp only [selected, decide_eq_true_eq]

end LeanCanny.Algebra.IntegralMixedPhysicalCompanionBits
