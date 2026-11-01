/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeBranch
public import LeanCanny.Algebra.IntegralCriticalFlatActualRawRelativeEntry
public import LeanCanny.Algebra.IntegralCriticalFlatActualLowerChild
public import LeanCanny.Algebra.IntegralCriticalFlatActualMomentReplies
public import LeanCanny.Algebra.IntegralCriticalFlatActualCoefficient
public import LeanCanny.Algebra.IntegralCriticalFlatActualAction
public import LeanCanny.Algebra.IntegralCriticalFlatActualReductionPower
public import LeanCanny.Algebra.IntegralCriticalTotalCompanionChild
/-! # Concrete models and native guards for upper critical-history phases -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relative relativeAccess reduction reductionAccess characteristic characteristicAccess
  IntegralCriticalTotalCreatingBits.atFamily

noncomputable def reductionSize (F : Scripts) (q : List Bool) := (reduction F).dimension q * (reduction F).rank q
noncomputable def factorSize (F : Scripts) (q : List Bool) := IntegralBerkowitzBlockBits.powerDimension (characteristic F) q

theorem reductionSize_binary (F : Scripts) (h : Controls F) : BinaryFn (reductionSize F) :=
  (reductionAccess F h).dimension.mul (reductionAccess F h).rank

theorem factorSize_binary (F : Scripts) (h : Controls F) : BinaryFn (factorSize F) :=
  (((characteristicAccess F h).dimension.add (BinaryFn.const 1)).mul
    ((characteristicAccess F h).dimension.add (BinaryFn.const 1))).mul (characteristicAccess F h).rank

def finiteAxes (F : Scripts) (size : List Bool → ℕ) (q : List Bool) : Prop :=
  get F.toParameters .row q < size q ∧ get F.toParameters .col q < size q

instance (F : Scripts) (size : List Bool → ℕ) (q : List Bool) : Decidable (finiteAxes F size q) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem finiteAxes_FP (F : Scripts) (h : Controls F) (size : List Bool → ℕ) (hs : BinaryFn size) : FPPred (finiteAxes F size) :=
  ((get_binary F.toParameters h.task.toAccess .row).lt hs).and ((get_binary F.toParameters h.task.toAccess .col).lt hs)

def selectedFinite (F : Scripts) (p : Phase) (size : List Bool → ℕ) (q : List Bool) : Bool :=
  decide (IntegralCriticalTotalCompanionBits.valid F q ∧ isPhase p q ∧ finiteAxes F size q)

theorem selectedFinite_FP (F : Scripts) (h : Controls F) (p : Phase) (size : List Bool → ℕ) (hs : BinaryFn size) :
    (fun q => [selectedFinite F p size q]) ∈ FP :=
  ((IntegralCriticalTotalCompanionBits.valid_FP F h.task).and ((isPhase_FP p).and (finiteAxes_FP F h size hs))).flag_mem_FP

theorem selectedFinite_iff (F : Scripts) (p : Phase) (size : List Bool → ℕ) (q : List Bool) : selectedFinite F p size q = true ↔
    IntegralCriticalTotalCompanionBits.valid F q ∧ isPhase p q ∧ finiteAxes F size q := by
  simp only [selectedFinite, decide_eq_true_eq]

structure Matches (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) : Prop where
  lower : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .eulerLower q → answer F x q = IntegralCriticalActualScalarModels.lower F q
  reductionEntry : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .reductionEntry q → answer F x q = IntegralCriticalFlatActualReductionEntryBits.value F q
  reductionPower : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .reductionPower q → answer F x q = IntegralCriticalTotalActionSnapshotBits.powerValue F q
  action : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .actionEntry q → answer F x q = IntegralCriticalFlatActualActionBits.value F q
  momentEntry : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .momentEntry q → answer F x q = IntegralCriticalFlatActualMomentBits.value F q
  moment : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .momentPower q → answer F x q = IntegralCriticalTotalMomentValueSnapshotBits.value F q
  relativeFactor : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .relativeFactor q → answer F x q = IntegralCriticalFlatActualRelativeFactorBits.value F q
  relativePower : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .relativePower q → answer F x q = (characteristic F).value q
  coefficient : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .criticalCoefficient q → answer F x q = IntegralCriticalTotalCreatingBits.coefficientValue F q
  companion : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .companion q → answer F x q = IntegralCriticalFlatHeightBits.companionValue F q

noncomputable def single (F : Scripts) (h : Controls F) (P : SingleCall.Program)
    (hc : P.controller.Certificates (encQ := encBits) (encS := SingleCall.encState))
    (s : List Bool → Bool) (hs : (fun q => [s q]) ∈ FP) (model : List Bool → List Bool) : Machine :=
  ofSingleCall P hc s hs model (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)

theorem single_correct (F : Scripts) (h : Controls F) (P : SingleCall.Program)
    (hc : P.controller.Certificates (encQ := encBits) (encS := SingleCall.encState))
    (s : List Bool → Bool) (hs : (fun q => [s q]) ∈ FP) (model : List Bool → List Bool)
    (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hv : ∀ q, s q = true → P.value (answer F x) q = model q)
    (hf : ∀ q c budget, s q = true → P.controller.Requests (answer F x) budget q c → Frame F q c) :
    Correct (single F h P hc s hs model) (answer F x) (Frame F) := by
  apply ofSingleCall_correct
  · exact hv
  · intro q hq hr
    have HH := (P.requests_iff (answer F x) (fun _ => 1) q (P.query q)).mpr ⟨hr, rfl⟩
    exact IntegralCriticalNativeBranchBits.answer_length F x q _ (hf q _ _ hq HH).1
  · exact hf

end LeanCanny.Algebra.IntegralCriticalNativeUpperBits
