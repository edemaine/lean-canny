/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeHeight
public import LeanCanny.Algebra.IntegralMixedFramedHeightTableArithmetic
/-! # Exact integer model and canonical residues of the native scalar-height controller -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

theorem model_eq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    model P D J q = IntegralMixedFramedHeightIntegerBits.word P D J q := by
  unfold model
  exact IntegralMixedFramedHeightTableArithmeticBits.post_table P D J q

theorem model_canonical (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = model P D J q := by
  rw [model_eq]
  exact IntegralMixedFramedHeightIntegerBits.word_canonical P D J q

end LeanCanny.Algebra.IntegralMixedFramedNativeHeightBits
