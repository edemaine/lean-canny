/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNativeHeight
public import LeanCanny.Algebra.IntegralMixedHeightTableArithmetic
/-! # Exact integer model and canonical residues of the native scalar-height controller -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNativeHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

theorem model_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    model P D q = IntegralMixedHeightIntegerBits.word P D q := by
  unfold model
  exact IntegralMixedHeightTableArithmeticBits.post_table P D q

theorem model_canonical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = model P D q := by
  rw [model_eq]
  exact IntegralMixedHeightIntegerBits.word_canonical P D q

end LeanCanny.Algebra.IntegralMixedNativeHeightBits
