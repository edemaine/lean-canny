/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalNear
public import LeanCanny.Encoding.IntegralFramedTerminalTarskiStatisticSpace
/-! # Native space bound for the five-query full-vertex Near test

Every principal statistic comes from the original CurrentQ arithmetic
factory. No selected sign, interpreting hom, or statistic evaluator is an
input to the public machine construction.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalNear
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedTerminalTarskiStatistic.value

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (center selected : List Bool→ℕ)
variable (hpos : ∀q,0<(family P D H).birth (terminal q))

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
    (right : Bool) :
    SpaceFunction (packet P D H L F C hs parent terminal center selected hpos hfactor hf right) :=by
  have E (power : Fin 3) (negativeEpsilon : Bool) :=
    (IntegralFramedTerminalTarskiStatistic.evaluator P D H L F C hs parent terminal center selected hpos
      a hL hF hC I h hb Hnew bank hbank T hT hrT hp ht hc hj hS hfactor hf power right negativeEpsilon).precompose reset reset_FP
  have EP:=SpaceFunction.ofFP pairSnd pairSnd_mem_FP
  exact EP.pairOutputs ((E 0 false).pairOutputs ((E 2 false).pairOutputs
    ((E 1 false).pairOutputs ((E 2 true).pairOutputs (E 1 true)))))

private theorem decider_of_evaluator
    (hfactor : ∀root,1≤F root) (hf : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (right : Bool)
    (E : SpaceFunction (packet P D H L F C hs parent terminal center selected hpos hfactor hf right)) :
    SpaceDecider (Accept P D H L F C hs parent terminal center selected hpos hfactor hf right) :=by
  apply E.decider (fun q=>decide (OrderedWindowStatisticBits.Accept q)) OrderedWindowStatisticBits.accept_fppred.flag_mem_FP
  intro u
  simp only [Accept,Set.mem_ofPred_eq,decide_eq_true_eq]

theorem decider (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
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
    (right : Bool) :
    SpaceDecider (Accept P D H L F C hs parent terminal center selected hpos hfactor hf right) :=
  decider_of_evaluator P D H L F C hs parent terminal center selected hpos hfactor hf right
    (evaluator P D H L F C hs parent terminal center selected hpos a hL hF hC I h hb Hnew bank hbank
      T hT hrT hp ht hc hj hS hfactor hf right)

end LeanCanny.Encoding.IntegralFramedPhysicalNear
