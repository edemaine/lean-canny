/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationMomentEntry
/-! # Native normalization moments from actual augmented matrix replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def momentAccess (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : IntegralBlockMomentBits.Access (moment P F) :=
  IntegralCriticalFlatMomentBits.access P a (source P F) (access P a F h)

abbrev MomentEntryMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .monomialFactor q → answer q = momentEntry P F q

abbrev MomentRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i j : Fin (IntegralMixedNormalizationMomentMatrixBits.size P F q),
    answer (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((moment P F).powerMatrix q i j : ℤ) : ZMod ((moment P F).modulus q))

theorem moment_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : MomentEntryMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    MomentRepliesAt P F answer q := by
  intro i j
  let c := IntegralCriticalFlatMatrixQuery.writer P .monomialFactor
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HV : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid
    simp only [c, IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 5 := by
    simpa only [c, IntegralMixedMatrixFrames.matrix_routine, pairFst_pair] using hr
  exact (hx c HV HR (IntegralCriticalFlatMatrixQuery.writer_phase P .monomialFactor _)).trans
    (moment_entry_child P F g q hv i j)

noncomputable def stage4 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralBlockMomentBits.RecursiveStage.controller (moment P F) (momentAccess P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor)
  certificates := IntegralBlockMomentBits.RecursiveStage.certificates (moment P F) (momentAccess P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) (IntegralCriticalFlatMatrixQuery.writer_FP P a .monomialFactor)
  selected := selected P .factorPower
  selected_FP := selected_FP P a .factorPower
  model := momentValue P F
  clock := IntegralCriticalFlatMomentBits.clock P (source P F)
  clock_binary := IntegralCriticalFlatMomentBits.clock_binary P a (source P F) (access P a F h)
  stateBound := IntegralCriticalFlatMomentBits.stateBound P (source P F)
  stateBound_unary := IntegralCriticalFlatMomentBits.stateBound_unary P a (source P F) (access P a F h)

attribute [local irreducible] source access momentAccess

theorem correct4 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : MomentEntryMatches P F answer) :
    Correct (stage4 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    have H := (selected_iff P .factorPower q).mp hq
    exact ModularRecursiveStage.halted_after_local (IntegralBlockMomentBits.powerAccess (moment P F) (momentAccess P a F h))
      (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) answer q (moment_replies P F g answer hx q H.1 H.2.1)
  · intro q t hq hh
    have H := (selected_iff P .factorPower q).mp hq
    exact (ModularRecursiveStage.output_when_halted_local (IntegralBlockMomentBits.powerAccess (moment P F) (momentAccess P a F h))
      (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) answer q (moment_replies P F g answer hx q H.1 H.2.1) t hh).trans
      ((congrFun (IntegralBlockMomentBits.power_value (moment P F)) q).trans
        (IntegralBlockMomentBits.Family.requery_value _ _ q))
  · intro q t hq
    have H := (selected_iff P .factorPower q).mp hq
    simpa only [stage4, encBits_apply, IntegralBlockMomentBits.RecursiveStage.controller,
      IntegralCriticalFlatMomentBits.stateBound] using ModularRecursiveStage.state_length_local
      (IntegralBlockMomentBits.powerAccess (moment P F) (momentAccess P a F h))
      (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) answer q (moment_replies P F g answer hx q H.1 H.2.1) t
  · intro q c budget hq hc
    have H := (selected_iff P .factorPower q).mp hq
    obtain ⟨i, j, rfl⟩ := ModularRecursiveStage.requests_in_bounds_local
      (IntegralBlockMomentBits.powerAccess (moment P F) (momentAccess P a F h))
      (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) answer q (moment_replies P F g answer hx q H.1 H.2.1) budget c hc
    have HP := H.2.2
    change phase q = 4 at HP
    have HF := IntegralMixedMatrixFrames.matrix_frame P .monomialFactor
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
      (by simp only [pairFst_pair]; change 3 < phase q; omega)
    simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
