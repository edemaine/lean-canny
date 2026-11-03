/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalOriginalSourceSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalSourcePolynomialSpace
/-! # Original physical source leaves over a separate full-row query datum

The original source task is an FP projection. Arbitrary exponent words stay
in the outer query, rather than being clipped to a flat task numeric field.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalSourceAtBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family IntegralCriticalHistoryTask.modulus residueBits

noncomputable abbrev family (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (base : List Bool→List Bool) :=
  IntegralMixedPhysicalQueryBits.pull (IntegralMixedFramedPhysicalLowBits.family P D J) base
noncomputable abbrev indices (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (base : List Bool→List Bool) :=
  IntegralMixedPhysicalOriginalPullBits.indices (IntegralMixedFramedPhysicalLowBits.family P D J)
    (IntegralMixedFramedPhysicalLowBits.indices P D J) base

theorem metadata (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP) :
    IntegralMixedPhysicalCriticalBits.Metadata (family P D J base) (indices P D J base) :=
  IntegralMixedPhysicalOriginalPullBits.metadata _ _ (IntegralMixedFramedPhysicalLowBits.metadata P a D J c) base hb

theorem original_space (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (base : List Bool→List Bool) (hb : base∈FP) :
    SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar (family P D J base) (indices P D J base)) :=
  IntegralMixedPhysicalOriginalPullBits.original_space _ _ c.critical.physicalOriginal base hb

theorem leading_space (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (base : List Bool→List Bool) (hb : base∈FP) :
    SpaceFunction (fun q=>residueBits (((family P D J base).spatial q).leading : ZMod (IntegralCriticalHistoryTask.modulus P (base q)))) := by
  have EL : SpaceFunction (fun q=>residueBits (IntegralMixedFramedPhysicalSourcePolynomialBits.leading P D J q :
      ZMod (IntegralCriticalHistoryTask.modulus P q))) := c.scalar.leading.congr
        (funext fun q=>IntegralMixedFramedPhysicalSourcePolynomialBits.leading_value P D J q)
  apply (EL.precompose base hb).congr
  funext q
  have HF : ((family P D J base).spatial q).leading=IntegralMixedFramedPhysicalSourcePolynomialBits.leading P D J (base q) := by
    dsimp only [family,IntegralMixedPhysicalQueryBits.pull,IntegralMixedFramedPhysicalSourcePolynomialBits.leading]
  exact congrArg (fun z : ℤ=>residueBits (z : ZMod (IntegralCriticalHistoryTask.modulus P (base q)))) HF.symm

theorem evaluator (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (base : List Bool→List Bool) (hb : base∈FP) (V : List Bool→ℕ) (hV : UnaryFn V)
    (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>(family P D J base).ambient q+1) V
      (IntegralMixedPhysicalOriginalSourceBits.polynomial (family P D J base)) target
      (IntegralMixedPhysicalOriginalSourceBits.modulusWord (family P D J base) (indices P D J base))) :=
  IntegralMixedPhysicalOriginalSourceBits.evaluator_of_modulus _ _ (metadata P a D J c base hb)
    (original_space P D J c base hb) (fun q=>IntegralCriticalHistoryTask.modulus P (base q))
    (fun q=>by
      dsimp only [indices,IntegralMixedPhysicalOriginalPullBits.indices,IntegralMixedFramedPhysicalLowBits.indices,
        IntegralMixedPhysicalTaskBits.indices,IntegralMixedPhysicalQueryBits.indices,IntegralMixedPhysicalTaskBits.queries,
        IntegralMixedPhysicalQueryBits.taskQueries,Function.comp_apply]) (leading_space P D J c base hb) V hV target ht

end LeanCanny.Algebra.IntegralMixedFramedPhysicalSourceAtBits
