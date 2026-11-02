/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScalarCurrentModel
public import LeanCanny.Algebra.IntegralMixedFullAlgebraSpaceCanonical
/-! # Joint native scalar, critical, and producer arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullCoreSpaceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Controls (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) where
  scalar : IntegralMixedFullScalarBits.Controls P D
  algebra : IntegralMixedFullAlgebraSpaceBits.Controls P D

noncomputable def scalar (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) : Machine :=
  (IntegralMixedFullScalarBits.machine P a D h.scalar).withGuard
    (fun q => decide (IntegralMixedRoutineTaskBits.routine P q = 0))
    ((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 0)).flag_mem_FP

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) : Machine :=
  (scalar P a D h).choose (IntegralMixedFullAlgebraSpaceBits.machine P a D h.algebra)

theorem model_scalar (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 0) :
    (machine P a D h).model q = (IntegralMixedFullScalarBits.machine P a D h.scalar).model q := by
  change (if decide (IntegralMixedRoutineTaskBits.routine P q = 0) then _ else _) = _
  rw [ite_eq_left (decide_eq_true hr)]
  rfl

theorem model_algebra (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q ≠ 0) :
    (machine P a D h).model q = (IntegralMixedFullAlgebraSpaceBits.machine P a D h.algebra).model q := by
  change (if decide (IntegralMixedRoutineTaskBits.routine P q = 0) then _ else _) = _
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hr)]

theorem selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (machine P a D h).selected q = true := by
  change (_ || (IntegralMixedFullAlgebraSpaceBits.machine P a D h.algebra).selected q) = true
  rw [IntegralMixedFullAlgebraSpaceBits.selected, Bool.or_true]

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q := by
  by_cases hr : IntegralMixedRoutineTaskBits.routine P q = 0
  · rw [model_scalar P a D h q hr]
    exact IntegralMixedFullScalarBits.canonical P a D h.scalar q
  · rw [model_algebra P a D h q hr]
    exact IntegralMixedFullAlgebraSpaceBits.canonical P a D h.algebra q

end LeanCanny.Algebra.IntegralMixedFullCoreSpaceBits
