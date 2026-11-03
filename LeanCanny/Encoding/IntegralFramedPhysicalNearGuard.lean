/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalNearSpace
public import LeanCanny.Computation.SpaceFunctionQuantifiers
/-! # Guarded native Near requests

The total predicate rejects invalid full vertices, mismatched saved roots,
older counts beyond the terminal prefix, and invalid bank indices. The
actual physical branch anchor and slab avoidance remain geometric facts.
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

noncomputable def Metadata (q : List Bool) : Prop :=
  IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q ∧
  IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q ∧
  pairFst (terminal q)=pairFst (IntegralMixedVirtualTaskBits.saved P (parent q)) ∧
  center q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count ∧
  selected q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count

theorem metadata_FP (a : Access P) (hp : parent∈FP) (ht : terminal∈FP)
    (hc : BinaryFn center) (hj : BinaryFn selected) : FPPred (Metadata P D H parent terminal center selected) :=by
  have hn:=BinaryFn.ofUnary ((IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht)
  exact (IntegralMixedFramedCoordinateCoefficientSpaceBits.core_FP P a parent hp).and
    ((IntegralMixedFramedTerminalCoordinateHeadBits.valid_FP P a D H parent terminal hp ht).and
      ((Brackets.stringEq_fppred (mem_FP_comp ht pairFst_mem_FP)
        (mem_FP_comp (mem_FP_comp hp (IntegralMixedVirtualTaskBits.saved_FP P a)) pairFst_mem_FP)).and
        ((hc.lt hn).and (hj.lt hn))))

noncomputable def guarded (hfactor : ∀root,1≤F root)
    (hf : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key) (right : Bool) : Language :=
  {u | Metadata P D H parent terminal center selected (pairFst (pairFst u)) ∧
    SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos)
      (pairFst (pairFst u)) (pairSnd (pairFst u)) ∧
    u∈Accept P D H L F C hs parent terminal center selected hpos hfactor hf right}

theorem guarded_packet
    (hfactor : ∀root,1≤F root) (hf : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (right : Bool) (q w code : List Bool)
    (hm : Metadata P D H parent terminal center selected q)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w) :
    pair (pair q w) code∈guarded P D H L F C hs parent terminal center selected hpos hfactor hf right↔
      pair (pair q w) code∈Accept P D H L F C hs parent terminal center selected hpos hfactor hf right :=by
  simp only [guarded,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,hm,hv,true_and]

theorem guarded_decider (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
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
    SpaceDecider (guarded P D H L F C hs parent terminal center selected hpos hfactor hf right) :=by
  have EM:=SpaceFunction.ofFP _ ((metadata_FP P D H parent terminal center selected a hp ht hc hj).comp
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).flag_mem_FP
  have EV:=((SquareSampleCompleteVertices.decider hS).flagEvaluator).precompose pairFst pairFst_mem_FP
  have EN:=(decider P D H L F C hs parent terminal center selected hpos a hL hF hC I h hb Hnew bank hbank
    T hT hrT hp ht hc hj hS hfactor hf right).flagEvaluator
  have E:=EM.andFlags (EV.andFlags EN)
  apply E.decider (fun q=>decide (q=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro u
  simp only [guarded,Set.mem_ofPred_eq,Function.comp_apply,SquareSampleCompleteVertices.language,
    List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralFramedPhysicalNear
