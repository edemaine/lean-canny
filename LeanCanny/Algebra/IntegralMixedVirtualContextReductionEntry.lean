/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
public import LeanCanny.Algebra.IntegralMixedVirtualContextReductionPower
public import LeanCanny.Algebra.IntegralMixedVirtualLowerChild
public import LeanCanny.Algebra.IntegralMixedReductionEntryCorrect
public import LeanCanny.Algebra.IntegralMixedVirtualNativeHeight
/-! # Native reduction entries with actual lower and charged leading replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open IntegralMixedVirtualUpperBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def commonLeading (P : Parameters) (F : Family) (q : List Bool) :=
  IntegralCriticalLeadingBits.value (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen q

theorem commonLeading_snapshot (P : Parameters) (F : Family) (q : List Bool) : commonLeading P F q =
    IntegralCriticalLeadingBits.value (IntegralMixedVirtualSnapshotBits.family P F q).toEuler.toGradient.toFrozen [] := rfl

theorem commonLeading_child (P : Parameters) (F : Family) (q : List Bool) :
    commonLeading P F (IntegralMixedScalarQueryBits.commonLeading P q) = commonLeading P F q := by
  rw [commonLeading_snapshot, commonLeading_snapshot]
  unfold IntegralMixedScalarQueryBits.commonLeading
  rw [IntegralMixedVirtualNativeLowerBits.family_routine]

def finiteAxes (P : Parameters) (size : List Bool → ℕ) (q : List Bool) : Prop :=
  get P .row q < size q ∧ get P .col q < size q

theorem finiteAxes_FP (P : Parameters) (a : Access P) (size : List Bool → ℕ) (hs : BinaryFn size) : FPPred (finiteAxes P size) :=
  ((get_binary P a .row).lt hs).and ((get_binary P a .col).lt hs)

noncomputable def reductionSize (P : Parameters) (F : Family) (q : List Bool) :=
  (reduction P F).dimension q * (reduction P F).rank q

theorem reductionSize_binary (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : BinaryFn (reductionSize P F) :=
  (reductionAccess P a F h).dimension.mul (reductionAccess P a F h).rank

noncomputable def selectedFinite (P : Parameters) (p : Phase) (size : List Bool → ℕ) (q : List Bool) : Bool :=
  selected P p q && decide (finiteAxes P size q)

theorem selectedFinite_FP (P : Parameters) (a : Access P) (p : Phase) (size : List Bool → ℕ) (hs : BinaryFn size) :
    (fun q => [selectedFinite P p size q]) ∈ FP :=
  mem_FP_of_eq ((FPPred.of_flag (selected_FP P a p)).and (finiteAxes_FP P a size hs)).flag_mem_FP
    (fun q => by
      cases hb : selected P p q <;> by_cases hf : finiteAxes P size q <;>
        simp [selectedFinite, hb, hf])

theorem selectedFinite_iff (P : Parameters) (p : Phase) (size : List Bool → ℕ) (q : List Bool) :
    selectedFinite P p size q = true ↔ selected P p q = true ∧ finiteAxes P size q := by
  simp only [selectedFinite, Bool.and_eq_true, decide_eq_true_eq]

abbrev EntryRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  answer (IntegralMixedScalarQueryBits.commonLeading P q) = commonLeading P F (IntegralMixedScalarQueryBits.commonLeading P q) ∧
  answer (IntegralMixedVirtualLowerChildBits.child P F q) =
    IntegralMixedVirtualSnapshotBits.lower P F (IntegralMixedVirtualLowerChildBits.child P F q)

theorem value17 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (he : EntryRepliesAt P F answer q)
    (i j : Fin ((reduction P F).dimension q * (reduction P F).rank q))
    (hi : get P .row q = i.val) (hj : get P .col q = j.val) :
    (IntegralMixedReductionEntryBits.program P (relative P F)).value answer q = IntegralMixedVirtualMatrixBits.reductionEntry P F q := by
  let S := relative P F
  let := S.ring q
  have HL : ∀ _ : PurePowerReductionBits.Charged.scalar (IntegralPurePowerReductionBits.layout S)
      (IntegralPurePowerReductionBits.writer S (IntegralCriticalFlatReductionEntryBits.packet P S q)),
      answer (IntegralMixedScalarQueryBits.commonLeading P q) = (relativeAccess P a F h).leading q := by
    intro _
    exact he.1.trans (commonLeading_child P F q)
  have HE : ∀ _ : PurePowerReductionBits.request (IntegralPurePowerReductionBits.layout S)
      (fun z => S.layout.bound (pairFst z))
      (IntegralPurePowerReductionBits.writer S (IntegralCriticalFlatReductionEntryBits.packet P S q)),
      answer (IntegralCriticalFlatLowerQuery.writer P (IntegralCriticalFlatReductionEntryBits.lowerInput S
        (IntegralCriticalFlatReductionEntryBits.packet P S q))) = (relativeAccess P a F h).low
          (IntegralCriticalFlatReductionEntryBits.lowerInput S (IntegralCriticalFlatReductionEntryBits.packet P S q)) := by
    intro _
    exact he.2.trans (IntegralMixedVirtualLowerChildBits.child_value P a F h g q hv)
  have HD : (reduction P F).dimension q * (reduction P F).rank q = (reduction P F).dimension q * S.rank q := rfl
  let r := Fin.cast HD i
  let t := Fin.cast HD j
  have HV := IntegralMixedReductionEntryBits.value_block P S (relativeAccess P a F h) answer q HL HE r t hi hj
  have HM : S.modulus q = modulus P q := rfl
  have HB : IntegralCoefficientBlocks.blockHom (S.basis q) ((IntegralPurePowerActionBits.reductionSource S).dimension q)
      ((IntegralPurePowerActionBits.reductionSource S).matrix q) r t =
        IntegralCriticalTotalSnapshotBits.blockMatrix (reduction P F).toSource q i j := rfl
  rw [HB, HM] at HV
  rw [IntegralMixedVirtualMatrixBits.reductionEntry, hi, hj,
    IntegralMixedVirtualMatrixBits.reduction_snapshot, IntegralCriticalTotalSnapshotBits.integerEntry_fin]
  exact HV

noncomputable def stage17 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (IntegralMixedReductionEntryBits.program P (relative P F))
    ((IntegralMixedReductionEntryBits.program P (relative P F)).certificates
      (IntegralMixedReductionEntryBits.controls P a (relative P F) (relativeAccess P a F h)))
    (selectedFinite P .reductionEntry (reductionSize P F))
    (selectedFinite_FP P a .reductionEntry _ (reductionSize_binary P a F h))
    (IntegralMixedVirtualMatrixBits.reductionEntry P F) (IntegralCriticalHistoryEvaluator.residueWidth P)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct17 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (he : ∀ q, selectedFinite P .reductionEntry (reductionSize P F) q = true → EntryRepliesAt P F (fun q => residueBits (x q)) q) :
    Correct (stage17 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have HSEL := (selectedFinite_iff P .reductionEntry (reductionSize P F) q).mp hq
    have H := selected_base P .reductionEntry q HSEL.1
    exact value17 P a F h g _ q H.1 (he q hq) ⟨_, HSEL.2.1⟩ ⟨_, HSEL.2.2⟩ rfl rfl
  · intro q hq hr
    have HSEL := (selectedFinite_iff P .reductionEntry (reductionSize P F) q).mp hq
    have H := selected_base P .reductionEntry q HSEL.1
    let C := IntegralMixedReductionEntryBits.program P (relative P F)
    have HC : C.controller.Requests (fun q => residueBits (x q)) (fun _ => 1) q (C.query q) :=
      (C.requests_iff _ _ _ _).mpr ⟨hr, rfl⟩
    have HF := IntegralMixedReductionEntryBits.requests_frame P (relative P F) _ (fun _ => 1) q (C.query q)
      H.2.2 (by rw [H.2.1]; decide) HC
    have HE : IntegralCriticalHistoryEvaluator.residueWidth P (C.query q) = IntegralCriticalHistoryEvaluator.residueWidth P q :=
      congrArg (fun r => (numericCap P r).size) HF.1
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (C.query q)).trans_eq HE
  · intro q c budget hq hc
    have HSEL := (selectedFinite_iff P .reductionEntry (reductionSize P F) q).mp hq
    have H := selected_base P .reductionEntry q HSEL.1
    exact IntegralMixedReductionEntryBits.requests_frame P (relative P F) _ budget q c
      H.2.2 (by rw [H.2.1]; decide) hc

end LeanCanny.Algebra.IntegralMixedVirtualContextUpperBits
