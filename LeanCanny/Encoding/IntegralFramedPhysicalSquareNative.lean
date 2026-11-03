/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowReaderSemantics
public import LeanCanny.Encoding.IntegralFramedPhysicalSquareAccess
/-! # Native access to the literal full physical complete-square sampler

Original controls supply both scalar and critical coefficients at arbitrary
caller moduli. No full-row evaluator is supplied by the caller.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

 theorem native_row_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hk : key∈FP) (hpos : ∀u,0<(family P D J).birth (key u))
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Jnew)
    (hc : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Jnew c) :
    SpaceFunction (SquareSampleInput.rowCoefficient (input P D J L F C hs key hpos)) :=by
  have E:=IntegralMixedFramedPhysicalRowReaderBits.evaluator P a D J T ht hT Jnew c hc key hk
    (IntegralMixedFramedPhysicalRowReaderBits.scalar_positive P D J key hpos)
  exact E.congr (funext (IntegralMixedFramedPhysicalRowReaderBits.value_rowCoefficient
    P D J T hT Jnew c L F C hs key hpos))

theorem native_access (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (key : List Bool→List Bool) (hk : key∈FP) (hpos : ∀u,0<(family P D J).birth (key u))
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Jnew)
    (hc : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Jnew c) :
    (input P D J L F C hs key hpos).Access :=
  access P a D J T ht hT L F C hs hL hF hC key hk hpos
    (native_row_evaluator P a D J T ht hT L F C hs key hk hpos Jnew c hc)

end LeanCanny.Encoding.IntegralFramedPhysicalSquare
