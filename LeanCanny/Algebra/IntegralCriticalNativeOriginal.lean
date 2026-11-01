/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerModel
/-! # A charged original-integer coefficient leaf in the native dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeOriginalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def program (F : Scripts) : SingleCall.Program where
  request _ := false
  query := id
  immediate := IntegralCriticalActualCoefficientModel.original F
  finish := id

theorem certificates (F : Scripts) (h : Controls F)
    (a : SpaceFunction (IntegralCriticalActualOriginalLeaf.rawReader F)) :
    (program F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program F).certificates_of_space (constFn_mem_FP [false]) id_mem_FP
    (IntegralCriticalActualCoefficientModel.original_space F h a).computable (SpaceFunction.ofFP _ id_mem_FP).computable

noncomputable def machine (F : Scripts) (h : Controls F)
    (a : SpaceFunction (IntegralCriticalActualOriginalLeaf.rawReader F)) : Machine :=
  ofSingleCall (program F) (certificates F h a) (selected F .originalCoefficient) (selected_FP F h .originalCoefficient)
    (IntegralCriticalActualCoefficientModel.original F) (fun _ => 0) (UnaryFn.const 0)

theorem correct (F : Scripts) (h : Controls F) (a : SpaceFunction (IntegralCriticalActualOriginalLeaf.rawReader F))
    (reply : List Bool → List Bool) : Correct (machine F h a) reply (Frame F) := by
  apply ofSingleCall_correct
  · intro q _
    rfl
  · intro q _ hr
    cases hr
  · intro q child budget _ hc
    obtain ⟨hr, _⟩ := ((program F).requests_iff reply budget q child).mp hc
    cases hr

end LeanCanny.Algebra.IntegralCriticalNativeOriginalBits
