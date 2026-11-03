/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedFullCutIntervalStatistic
/-! # Original arithmetic supplies full-factor interval statistics -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedFullCutIntervalStatistic
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedScalarTarskiStatistic.value FixedWidthTarskiPrincipalBits.polynomial

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d selected : List Bool→ℕ)
variable (hpos : ∀q,0<(family P D H).birth (terminal q))

theorem budget_binary (a : Access P) (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (hj : BinaryFn selected) :
    BinaryFn (budget P D H L F C hs parent terminal d selected) :=by
  have HD:=hd
  have hD:=IntegralMixedFramedFullCutIntervalFamily.degree_binary d HD
  have hP:=IntegralMixedFramedFullCutHead.headDegree_binary P D H parent a hp
  have hQ : BinaryFn (IntegralMixedFramedFullCutIntervalFamily.queryBound P D H L F C hs terminal selected):=
    (BinaryFn.const 2).mul ((IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal selected a ht hj).add (BinaryFn.const 1))
  have hR:=MultivariateTarskiDegreeBounds.principalDegreeBound_binary hD (hD.sub (BinaryFn.const 1)) (hD.add (BinaryFn.const 2)) hP hQ
  exact (hP.add hQ).add hR

private theorem fit (power : Fin 3) (negativeEpsilon : Bool) (c b : List Bool) :
    (budget P D H L F C hs parent terminal d selected∘pairFst) (pair c b)<
      2^(mf P D H L F C hs parent terminal d selected power negativeEpsilon).width (pairFst (pair c b)) :=by
  unfold mf budget
  dsimp only [IntegralMixedFramedFullCutIntervalFamily.family,FixedWidthTarskiPrincipalBits.Family.width]
  unfold IntegralMixedFramedFullCutIntervalFamily.width
  exact Nat.lt_size_self _

theorem evaluator (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)

    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hrT : IntegralMixedFramedHeaderBits.Represents P D H T)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (hj : BinaryFn selected)
    (hS : (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos).Access)
    (hfactor : ∀root,1≤F root) (hf : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : Fin 3) (negativeEpsilon : Bool) :
    SpaceFunction (fun u=>SignStatisticBits.integerCode
      (value P D H L F C hs parent terminal d selected hpos hfactor hf power negativeEpsilon u)) :=by
  have HD:=hd
  let A:=IntegralMixedFramedFullCutIntervalFamily.access P D H L F C hs parent terminal d selected a hL hF hC h hb
    Hnew bank hbank hp ht HD hj (fun _=>power) (BinaryFn.const power.val) negativeEpsilon
  have HW:=IntegralMixedFramedFullCutIntervalFamily.width_unary P D H L F C hs parent terminal d selected a hp ht HD hj
  have HWM : UnaryFn (mf P D H L F C hs parent terminal d selected power negativeEpsilon).width :=by
    unfold mf
    dsimp only [IntegralMixedFramedFullCutIntervalFamily.family,FixedWidthTarskiPrincipalBits.Family.width]
    exact HW
  have HB:=budget_binary P D H L F C hs parent terminal d selected a hp ht hd hj
  have HH:=IntegralMixedFramedFullCutIntervalFamily.principalHeight_binary P D H L F C hs parent terminal d selected a
    hL hF hC hp ht HD hj
  unfold value
  exact IntegralFramedScalarTarskiStatistic.evaluator P D H L F C hs terminal hpos
    (prefixInput P D H L F C hs terminal hpos) (prefix_count P D H L F C hs terminal hpos)
    (mf P D H L F C hs parent terminal d selected power negativeEpsilon) pairFst
    (budget P D H L F C hs parent terminal d selected∘pairFst)
    (height P D H L F C hs parent terminal d selected∘pairFst)
    (dimensions P D H L F C hs parent terminal d selected hpos power negativeEpsilon)
    (degree_bound P D H L F C hs parent terminal d selected power negativeEpsilon)
    (mass_bound P D H L F C hs parent terminal d selected hfactor hf power negativeEpsilon)
    T hrT a hT ht hS A HWM pairFst_mem_FP (HB.comp pairFst_mem_FP) (HH.comp pairFst_mem_FP)
    (fit P D H L F C hs parent terminal d selected power negativeEpsilon)

end LeanCanny.Encoding.IntegralFramedFullCutIntervalStatistic
