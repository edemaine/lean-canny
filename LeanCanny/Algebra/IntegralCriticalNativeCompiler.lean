/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeModel
public import LeanCanny.Algebra.IntegralCriticalLocalBounds
/-! # Native local dispatcher contracts compile to a space evaluator -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeCompilerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem evaluator (F : Scripts) (h : Controls F) (M : Machine)
    (x : (q : List Bool) → ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))
    (hc : Correct M (answer F x) (Frame F))
    (hs : ∀ q, M.selected q = true) (hv : ∀ q, M.model q = answer F x q) :
    SpaceFunction (answer F x) := by
  let : Inhabited M.State := ⟨M.defaultValue⟩
  refine IntegralCriticalHistoryEvaluator.evaluator_of_local_bounds (encS := M.encoding)
    F.toParameters h.task.toAccess M.controller M.certificates x M.clock M.stateBound
    M.clock_binary M.stateBound_unary ?_ ?_ ?_ ?_
  · intro q
    exact hc.halted q (hs q)
  · intro q t _ hh
    exact (hc.output q t (hs q) hh).trans (hv q)
  · intro q child hr
    exact hc.requests q child M.clock (hs q) hr
  · intro q t _
    exact hc.state q t (hs q)

theorem actual_evaluator (F : Scripts) (h : Controls F) (M : Machine)
    (hc : Correct M (answer F (IntegralCriticalActualModelBits.residue F)) (Frame F))
    (hs : ∀ q, M.selected q = true)
    (hv : ∀ q, M.model q = IntegralCriticalActualModelBits.value F q) :
    SpaceFunction (IntegralCriticalActualModelBits.value F) := by
  have H := evaluator F h M (IntegralCriticalActualModelBits.residue F) hc hs
    (fun q => (hv q).trans (IntegralCriticalActualModelBits.residue_value F q).symm)
  exact H.congr (funext fun q => IntegralCriticalActualModelBits.residue_value F q)

end LeanCanny.Algebra.IntegralCriticalNativeCompilerBits
