/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalTarskiStatistic
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateHeadWidth
/-! # Original current-Q arithmetic supplies the actual terminal statistic machine -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalTarskiStatistic
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedScalarTarskiStatistic.value FixedWidthTarskiPrincipalBits.polynomial

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (center selected : List Bool→ℕ)
variable (hpos : ∀q,0<(family P D H).birth (terminal q))
local notation "d" => IntegralMixedSelectedCoordinateHead.fullDegree P (family P D H) parent
local notation "e" => IntegralMixedSelectedCoordinateHead.fullParameter P parent

theorem budget_binary (a : Access P) (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (hp : parent∈FP) (ht : terminal∈FP) (hc : BinaryFn center) (hj : BinaryFn selected) :
    BinaryFn (budget P D H L F C hs parent terminal center selected) :=by
  have HD:=IntegralMixedSelectedCoordinateHead.fullDegree_binary P a (family P D H) I parent hp
  have HE:=IntegralMixedSelectedCoordinateHead.fullParameter_binary P a parent hp
  have hD:=IntegralMixedFramedTerminalTarskiFamilyBits.degree_binary d HD
  have hP:=IntegralMixedFramedTerminalTarskiHeadBits.degreeBound_binary P D H L F C hs parent terminal e center a hp ht HE hc
  have hQ : BinaryFn (IntegralMixedFramedTerminalTarskiFamilyBits.queryBound P D H L F C hs terminal selected):=
    (BinaryFn.const 2).mul ((IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal selected a ht hj).add (BinaryFn.const 1))
  have hR:=MultivariateTarskiDegreeBounds.principalDegreeBound_binary hD (hD.sub (BinaryFn.const 1)) (hD.add (BinaryFn.const 2)) hP hQ
  exact (hP.add hQ).add hR

private theorem fit (power : Fin 3) (negativeEta negativeEpsilon : Bool) (c b : List Bool) :
    (budget P D H L F C hs parent terminal center selected∘pairFst) (pair c b)<
      2^(mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon).width (pairFst (pair c b)) :=by
  unfold mf budget
  dsimp only [IntegralMixedFramedTerminalTarskiFamilyBits.family,FixedWidthTarskiPrincipalBits.Family.width]
  unfold IntegralMixedFramedTerminalTarskiFamilyBits.width
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
    (hp : parent∈FP) (ht : terminal∈FP) (hc : BinaryFn center) (hj : BinaryFn selected)
    (hS : (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos).Access)
    (hfactor : ∀root,1≤F root) (hf : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : Fin 3) (negativeEta negativeEpsilon : Bool) :
    SpaceFunction (fun u=>SignStatisticBits.integerCode
      (value P D H L F C hs parent terminal center selected hpos hfactor hf power negativeEta negativeEpsilon u)) :=by
  have HD:=IntegralMixedSelectedCoordinateHead.fullDegree_binary P a (family P D H) I parent hp
  have HE:=IntegralMixedSelectedCoordinateHead.fullParameter_binary P a parent hp
  let A:=IntegralMixedFramedTerminalTarskiFamilyBits.access P D H L F C hs parent terminal d e center selected a hL hF hC I h hb
    Hnew bank hbank hp ht HD HE hc hj (fun _=>power) (BinaryFn.const power.val) negativeEta negativeEpsilon
  have HW:=IntegralMixedFramedTerminalTarskiFamilyBits.width_unary P D H L F C hs parent terminal d e center selected a hp ht HD HE hc hj
  have HWM : UnaryFn (mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon).width :=by
    unfold mf
    dsimp only [IntegralMixedFramedTerminalTarskiFamilyBits.family,FixedWidthTarskiPrincipalBits.Family.width]
    exact HW
  have HB:=budget_binary P D H L F C hs parent terminal center selected a I hp ht hc hj
  have HH:=IntegralMixedFramedTerminalTarskiFamilyBits.principalHeight_binary P D H L F C hs parent terminal d e center selected a
    hL hF hC I hp ht HD HE hc hj
  unfold value
  exact IntegralFramedScalarTarskiStatistic.evaluator P D H L F C hs terminal hpos
    (prefixInput P D H L F C hs terminal hpos) (prefix_count P D H L F C hs terminal hpos)
    (mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon) pairFst
    (budget P D H L F C hs parent terminal center selected∘pairFst)
    (height P D H L F C hs parent terminal center selected∘pairFst)
    (dimensions P D H L F C hs parent terminal center selected hpos power negativeEta negativeEpsilon)
    (degree_bound P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon)
    (mass_bound P D H L F C hs parent terminal center selected hfactor hf power negativeEta negativeEpsilon)
    T hrT a hT ht hS A HWM pairFst_mem_FP (HB.comp pairFst_mem_FP) (HH.comp pairFst_mem_FP)
    (fit P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon)

end LeanCanny.Encoding.IntegralFramedTerminalTarskiStatistic
