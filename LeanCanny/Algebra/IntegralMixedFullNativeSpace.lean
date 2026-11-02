/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullNativeCurrent
public import LeanCanny.Algebra.IntegralMixedNativeCompiler
/-! # Native polynomial space for the complete mixed-history arithmetic model

The controls charge immutable original syntax and give explicit original
height/modulus bounds. No recursive answer evaluator is a cost premise.
Original integer degree and coefficient queries are charged in polynomial space.
The original-input source transport and syntax frontend remain explicit.
The connectivity geometry and its effective source construction remain separate.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch

noncomputable def residue (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) : ZMod (modulus P q) := Classical.choose (canonical P a D h q)
theorem residue_value (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) : residueBits (residue P a D h q) = (machine P a D h).model q := Classical.choose_spec (canonical P a D h q)

theorem correct_residue (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :
    Correct (machine P a D h) (fun q => residueBits (residue P a D h q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a D h (residue P a D h) (fun q _ => residue_value P a D h q)

theorem residue_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :
    SpaceFunction (fun q => residueBits (residue P a D h q)) :=
  IntegralMixedNativeCompilerBits.evaluator P a (machine P a D h) (residue P a D h)
    (correct_residue P a D h) (selected P a D h) (fun q => (residue_value P a D h q).symm)

theorem model_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :
    SpaceFunction (machine P a D h).model := by
  have HE : (fun q => residueBits (residue P a D h q)) = (machine P a D h).model := funext (residue_value P a D h)
  rw [← HE]
  exact residue_space P a D h

end LeanCanny.Algebra.IntegralMixedFullNativeBits
