/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalSourceAtSpace
public import LeanCanny.Algebra.IntegralMixedPhysicalOriginalSourceDerivativeSpace
/-! # Actual physical source derivatives retain the external exponent query -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalSourceAtBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family IntegralCriticalHistoryTask.modulus residueBits

theorem derivative_evaluator (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (base : List Bool→List Bool) (hb : base∈FP) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<(family P D J base).ambient q+1) (hselected : UnaryFn selected)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>(family P D J base).ambient q+1) V
      (fun q=>MvPolynomial.pderiv ⟨selected q,hs q⟩ (IntegralMixedPhysicalOriginalSourceBits.polynomial (family P D J base) q))
      target (IntegralMixedPhysicalOriginalSourceBits.modulusWord (family P D J base) (indices P D J base))) :=
  IntegralMixedPhysicalOriginalSourceBits.derivative_evaluator_of_modulus _ _ (metadata P a D J c base hb)
    (original_space P D J c base hb) (fun q=>IntegralCriticalHistoryTask.modulus P (base q))
    (fun q=>by
      dsimp only [indices,IntegralMixedPhysicalOriginalPullBits.indices,IntegralMixedFramedPhysicalLowBits.indices,
        IntegralMixedPhysicalTaskBits.indices,IntegralMixedPhysicalQueryBits.indices,IntegralMixedPhysicalTaskBits.queries,
        IntegralMixedPhysicalQueryBits.taskQueries,Function.comp_apply]) (leading_space P D J c base hb)
    selected hs hselected V hV target ht

end LeanCanny.Algebra.IntegralMixedFramedPhysicalSourceAtBits
