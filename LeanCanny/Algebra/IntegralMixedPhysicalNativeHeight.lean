/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeValidBranch
public import LeanCanny.Algebra.IntegralMixedPhysicalSnapshot
/-! # Actual physical height entries delegated to the scalar height routine -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def heightAt (A : IntegralClearedCriticalBits.Source) (i : ℕ) : List Bool := by
  let := A.ring []
  exact residueBits ((Algebra.leftMulMatrix (A.basis []) (A.height [] i) (A.row []) (A.col []) : ℤ) : ZMod (A.modulus []))
noncomputable def height (P : Parameters) (F : Family) (q : List Bool) :=
  heightAt (IntegralMixedPhysicalSnapshotBits.family P F q) (get P .slot8 q)

theorem height_eq (P : Parameters) (F : Family) (q : List Bool) :
    letI := (source P F).ring q
    height P F q = residueBits ((Algebra.leftMulMatrix ((source P F).basis q)
      ((source P F).height q (get P .slot8 q)) ((source P F).row q) ((source P F).col q) : ℤ) : ZMod (modulus P q)) := rfl

theorem family_routine (P : Parameters) (F : Family) (r : IntegralMixedRoutineTaskBits.Routine) (p : Phase) (q : List Bool) :
    IntegralMixedPhysicalSnapshotBits.family P F (IntegralMixedRoutineTaskBits.query P (birth P) r p q) =
      IntegralMixedPhysicalSnapshotBits.family P F q := by
  apply IntegralMixedPhysicalSnapshotBits.family_invariance
  · exact IntegralMixedRoutineTaskBits.query_root P (birth P) r p q
  · exact IntegralMixedRoutineTaskBits.query_birth P (birth P) r p q (min_le_right _ _)
  · rw [IntegralMixedRoutineTaskBits.query_get]; rfl
  · rw [IntegralMixedRoutineTaskBits.query_get]; rfl
  · rw [IntegralMixedRoutineTaskBits.query_get]; rfl
  · rw [IntegralMixedRoutineTaskBits.query_get]; rfl
  · rw [IntegralMixedRoutineTaskBits.query_get]; rfl
  · rw [IntegralMixedRoutineTaskBits.query_get]; rfl
  · unfold modulus
    rw [IntegralMixedRoutineTaskBits.query_get]
    rfl

theorem height_scalar_child (P : Parameters) (F : Family) (q : List Bool) :
    height P F (IntegralMixedScalarQueryBits.virtualHeight P q) = height P F q := by
  unfold height IntegralMixedScalarQueryBits.virtualHeight
  rw [family_routine, IntegralMixedRoutineTaskBits.query_get]
  rfl

noncomputable def heightProgram (P : Parameters) : SingleCall.Program where
  request _ := true
  query := IntegralMixedScalarQueryBits.virtualHeight P
  immediate _ := []
  finish := pairSnd

theorem height_certificates (P : Parameters) (a : Access P) :
    (heightProgram P).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (heightProgram P).certificates ⟨constFn_mem_FP [true], IntegralMixedScalarQueryBits.scalarQuery_FP P a .factorPower,
    constFn_mem_FP [], pairSnd_mem_FP⟩

noncomputable def heightMachine (P : Parameters) (a : Access P) (F : Family) : Machine :=
  ofSingleCall (heightProgram P) (height_certificates P a) (selectedValid P .clearedHeight) (selectedValid_FP P a .clearedHeight)
    (height P F) (replyBound P) (replyBound_unary P a)

theorem height_correct (P : Parameters) (a : Access P) (F : Family) (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .clearedHeight q = true →
      reply (IntegralMixedScalarQueryBits.virtualHeight P q) = height P F (IntegralMixedScalarQueryBits.virtualHeight P q)) :
    Correct (heightMachine P a F) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    simpa only [SingleCall.Program.value, heightProgram, ite_true, pairSnd_pair] using
      (he q hq).trans (height_scalar_child P F q)
  · intro q hq _
    change (reply (IntegralMixedScalarQueryBits.virtualHeight P q)).length ≤ replyBound P q
    rw [he q hq, height_scalar_child, height_eq]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hq hc
    have HR := ((selectedValid_iff P .clearedHeight q).mp hq).2.1
    have HC := ((heightProgram P).requests_iff reply budget q c).mp hc
    have HE : c = IntegralMixedScalarQueryBits.virtualHeight P q := HC.2
    apply Eq.mpr (congrArg (IntegralMixedRoutineTaskBits.Frame P q) HE)
    exact IntegralMixedScalarQueryBits.scalar_frame P .factorPower q (by rw [HR]; decide)
end LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
