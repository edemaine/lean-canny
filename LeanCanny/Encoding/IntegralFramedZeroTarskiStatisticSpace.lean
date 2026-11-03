/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedZeroTarskiStatistic
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateHeadWidth
/-! # Original current-Q arithmetic supplies the actual terminal statistic machine -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedZeroTarskiStatistic
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedScalarTarskiStatistic.value FixedWidthTarskiPrincipalBits.polynomial

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (selected : List Bool→ℕ)
variable (hpos : ∀q,0<(family P D H).birth (terminal q))
local notation "d" => IntegralMixedSelectedCoordinateHead.fullDegree P (family P D H) parent
local notation "e" => IntegralMixedSelectedCoordinateHead.fullParameter P parent

theorem budget_binary (a : Access P) (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (hp : parent∈FP) (ht : terminal∈FP) (hj : BinaryFn selected) :
    BinaryFn (budget P D H L F C hs parent terminal selected) :=by
  have HD:=IntegralMixedSelectedCoordinateHead.fullDegree_binary P a (family P D H) I parent hp
  have HE:=IntegralMixedSelectedCoordinateHead.fullParameter_binary P a parent hp
  exact IntegralMixedFramedZeroTarskiBits.wholeBound_binary P D H L F C hs parent terminal d e selected a hp ht HD HE hj

private theorem fit (power : Fin 3) (negative : Bool) (c b : List Bool) :
    (budget P D H L F C hs parent terminal selected∘pairFst) (pair c b)<
      2^(mf P D H L F C hs parent terminal selected power negative).width (pairFst (pair c b)) :=by
  unfold mf budget
  dsimp only [IntegralMixedFramedZeroTarskiBits.family,FixedWidthTarskiPrincipalBits.Family.width]
  unfold IntegralMixedFramedZeroTarskiBits.width
  exact Nat.lt_size_self _

theorem evaluator (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)

    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hrT : IntegralMixedFramedHeaderBits.Represents P D H T)
    (hp : parent∈FP) (ht : terminal∈FP) (hj : BinaryFn selected)
    (hS : (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos).Access)
    (hfactor : ∀root,1≤F root) (hf : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : Fin 3) (negative : Bool) :
    SpaceFunction (fun u=>SignStatisticBits.integerCode
      (value P D H L F C hs parent terminal selected hpos hfactor hf power negative u)) :=by
  have HD:=IntegralMixedSelectedCoordinateHead.fullDegree_binary P a (family P D H) I parent hp
  have HE:=IntegralMixedSelectedCoordinateHead.fullParameter_binary P a parent hp
  let A:=IntegralMixedFramedZeroTarskiBits.access P D H L F C hs parent terminal d e selected a hL hF hC I h hb
    Hnew bank hbank hp ht HD HE hj (fun _=>power) (BinaryFn.const power.val) negative
  have HW:=IntegralMixedFramedZeroTarskiBits.width_unary P D H L F C hs parent terminal d e selected a hp ht HD HE hj
  have HWM : UnaryFn (mf P D H L F C hs parent terminal selected power negative).width :=by
    unfold mf
    dsimp only [IntegralMixedFramedZeroTarskiBits.family,FixedWidthTarskiPrincipalBits.Family.width]
    exact HW
  have HB:=budget_binary P D H L F C hs parent terminal selected a I hp ht hj
  have HH:=IntegralMixedFramedZeroTarskiBits.principalHeight_binary P D H L F C hs parent terminal d e selected a
    hL hF hC I hp ht HD HE hj
  unfold value
  exact IntegralFramedScalarTarskiStatistic.evaluator P D H L F C hs terminal hpos
    (prefixInput P D H L F C hs terminal hpos) (prefix_count P D H L F C hs terminal hpos)
    (mf P D H L F C hs parent terminal selected power negative) pairFst
    (budget P D H L F C hs parent terminal selected∘pairFst)
    (height P D H L F C hs parent terminal selected∘pairFst)
    (dimensions P D H L F C hs parent terminal selected hpos power negative)
    (degree_bound P D H L F C hs parent terminal selected power negative)
    (mass_bound P D H L F C hs parent terminal selected hfactor hf power negative)
    T hrT a hT ht hS A HWM pairFst_mem_FP (HB.comp pairFst_mem_FP) (HH.comp pairFst_mem_FP)
    (fit P D H L F C hs parent terminal selected power negative)

end LeanCanny.Encoding.IntegralFramedZeroTarskiStatistic
