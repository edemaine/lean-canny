/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualMatrixModel
public import LeanCanny.Algebra.IntegralMixedMatrixFrames
public import LeanCanny.Algebra.IntegralCriticalFlatActualReductionPower
public import LeanCanny.Computation.NativeSingleCallBranch
public import LeanCanny.Algebra.IntegralMixedVirtualContextLeaves
/-! # Native reduction powering over the selected virtual mixed prefix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open IntegralMixedVirtualUpperBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev selected (P : Parameters) := IntegralMixedVirtualContextBits.selected P

theorem selected_FP (P : Parameters) (a : Access P) (p : Phase) : (fun q => [selected P p q]) ∈ FP :=
  IntegralMixedVirtualContextBits.selected_FP P a p

theorem selected_base (P : Parameters) (p : Phase) (q : List Bool) (hq : selected P p q = true) :
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 1 ∧ isPhase p q :=
  (IntegralMixedVirtualNativeLowerBits.selectedValid_iff P p q).mp (IntegralMixedVirtualContextBits.selected_raw P p q hq)

noncomputable def powerValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  (IntegralReductionActionBits.powerFamily (reduction P F)).value (IntegralCriticalFlatActionBits.packet P (reduction P F) q)

abbrev ReductionRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i j : Fin ((IntegralCriticalFlatReductionPowerBits.family P (reduction P F)).dimension q *
      (IntegralCriticalFlatReductionPowerBits.family P (reduction P F)).rank q),
    answer (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      IntegralMixedVirtualMatrixBits.reductionEntry P F (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry
        (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))))

theorem reduction_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (he : ReductionRepliesAt P F answer q) :
    IntegralCriticalFlatReductionPowerBits.RepliesAt P (reduction P F) answer q := by
  intro i j
  let r : Fin ((reduction P F).dimension q * (reduction P F).rank q) :=
    ⟨i.val, by simpa only [IntegralCriticalFlatActualReductionPowerBits.family_dimension,
      IntegralCriticalFlatActualReductionPowerBits.family_rank] using i.isLt⟩
  let t : Fin ((reduction P F).dimension q * (reduction P F).rank q) :=
    ⟨j.val, by simpa only [IntegralCriticalFlatActualReductionPowerBits.family_dimension,
      IntegralCriticalFlatActualReductionPowerBits.family_rank] using j.isLt⟩
  let c := IntegralCriticalFlatMatrixQuery.writer P .reductionEntry
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HV := (he i j).trans (IntegralMixedVirtualMatrixBits.reduction_child P F g q hv r t)
  have HE : (IntegralCriticalFlatReductionPowerBits.family P (reduction P F)).powerMatrix q i j =
      IntegralCriticalTotalSnapshotBits.blockMatrix (reduction P F).toSource q r t :=
    (IntegralCriticalTotalSnapshotBits.integerEntry_fin _ i j).symm.trans
      ((IntegralCriticalFlatActualReductionPowerBits.integerEntry_family P (reduction P F) q i.val j.val).trans
        (IntegralCriticalTotalSnapshotBits.integerEntry_fin _ r t))
  have HM : (IntegralCriticalFlatReductionPowerBits.family P (reduction P F)).modulus q = modulus P q :=
    IntegralCriticalFlatActualReductionPowerBits.family_modulus P (reduction P F) q
  rw [HE]
  exact HV.trans (congrArg (fun m => residueBits
    ((IntegralCriticalTotalSnapshotBits.blockMatrix (reduction P F).toSource q r t : ℤ) : ZMod m)) HM.symm)

noncomputable def stage18 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralCriticalFlatReductionPowerBits.controller P a (reduction P F)
    (reductionAccess P a F h) (reduction_controls P a F h)
  certificates := IntegralCriticalFlatReductionPowerBits.certificates P a (reduction P F)
    (reductionAccess P a F h) (reduction_controls P a F h)
  selected := selected P .reductionPower
  selected_FP := selected_FP P a .reductionPower
  model := powerValue P F
  clock := IntegralCriticalFlatReductionPowerBits.clock P (reduction P F)
  clock_binary := IntegralCriticalFlatReductionPowerBits.clock_binary P a (reduction P F)
    (reductionAccess P a F h) (reduction_controls P a F h)
  stateBound := IntegralCriticalFlatReductionPowerBits.stateBound P (reduction P F)
  stateBound_unary := IntegralCriticalFlatReductionPowerBits.stateBound_unary P a (reduction P F)
    (reductionAccess P a F h) (reduction_controls P a F h)

attribute [local irreducible] relative relativeAccess reduction reductionAccess characteristic characteristicAccess

theorem correct18 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool)
    (hx : ∀ q, selected P .reductionPower q = true → ReductionRepliesAt P F answer q) :
    Correct (stage18 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    have H := selected_base P .reductionPower q hq
    exact IntegralCriticalFlatReductionPowerBits.halted_after_local P a (reduction P F) (reductionAccess P a F h)
      (reduction_controls P a F h) answer q (reduction_replies P F g answer q H.1 (hx q hq))
  · intro q t hq hh
    have H := selected_base P .reductionPower q hq
    exact IntegralCriticalFlatReductionPowerBits.output_when_halted_local P a (reduction P F) (reductionAccess P a F h)
      (reduction_controls P a F h) answer q (reduction_replies P F g answer q H.1 (hx q hq)) t hh
  · intro q t hq
    have H := selected_base P .reductionPower q hq
    simpa only [stage18, encBits_apply] using IntegralCriticalFlatReductionPowerBits.state_length_local P a (reduction P F)
      (reductionAccess P a F h) (reduction_controls P a F h) answer q (reduction_replies P F g answer q H.1 (hx q hq)) t
  · intro q c budget hq hc
    have H := selected_base P .reductionPower q hq
    obtain ⟨i, j, rfl⟩ := IntegralBlockPowerBits.RecursiveStage.requests_in_bounds_local
      (IntegralCriticalFlatReductionPowerBits.family P (reduction P F))
      (IntegralCriticalFlatReductionPowerBits.access P a (reduction P F) (reductionAccess P a F h) (reduction_controls P a F h))
      (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry) answer q (reduction_replies P F g answer q H.1 (hx q hq)) budget c hc
    have HP := H.2.2
    have HS : Phase.reductionEntry.code < phase (pairFst
        (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) := by
      simp only [pairFst_pair]
      change 17 < phase q
      change phase q = 18 at HP
      omega
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .reductionEntry
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) HS

end LeanCanny.Algebra.IntegralMixedVirtualContextUpperBits
