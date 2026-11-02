/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeCorrect
public import LeanCanny.Algebra.IntegralMixedFramedNativeCanonical
public import LeanCanny.Algebra.IntegralMixedNativeCompiler
/-! # Polynomial-space arithmetic over actual changing-source histories

Only original syntax and original coefficient readers are charged leaves.
The current recursive answer function is derived from the native controller.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
set_option backward.isDefEq.respectTransparency false

noncomputable def residue (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) : ZMod (modulus P q) :=
  Classical.choose (canonical P a D H h q)
theorem residue_value (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    residueBits (residue P a D H h q) = (machine P a D H h).model q := Classical.choose_spec (canonical P a D H h q)

theorem correct_residue (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (hb : Bounds P D H h) :
    Correct (machine P a D H h) (fun q => residueBits (residue P a D H h q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a D H h hb (residue P a D H h) (fun q _ => residue_value P a D H h q)

theorem residue_space (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (hb : Bounds P D H h) : SpaceFunction (fun q => residueBits (residue P a D H h q)) :=
  IntegralMixedNativeCompilerBits.evaluator P a (machine P a D H h) (residue P a D H h)
    (correct_residue P a D H h hb) (selected P a D H h) (fun q => (residue_value P a D H h q).symm)

theorem model_space (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (hb : Bounds P D H h) : SpaceFunction (machine P a D H h).model := by
  have HE : (fun q => residueBits (residue P a D H h q)) = (machine P a D H h).model := funext (residue_value P a D H h)
  rw [← HE]
  exact residue_space P a D H h hb

end LeanCanny.Algebra.IntegralMixedFramedNativeBits
