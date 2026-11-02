/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutSign
public import LeanCanny.Encoding.IntegralFramedCutFiniteGuards
/-! # Native finite selected-cut guards on one complete terminal tuple

The padding check reads the retained creating head, not the newest terminal
scalar. All lower-choice, leading, higher and constant probes stay at the
same terminal vertex and actual selected parent.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutGuards
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))

noncomputable def headIndex (c : List Bool) := IntegralFramedTerminalCutTest.count P D H key c-birth P c-1
noncomputable def head (q : List Bool) :=
  SquareSampleCompleteCoordinateSign.value (IntegralFramedCompleteSquare.input P D H L F C hs key hpos)
    (pair q (BinaryNatCode.encode (headIndex P D H key (pairFst q))))
noncomputable abbrev Guards (q : List Bool) : Prop :=
  FiniteCoefficientSignScan.Guards (IntegralFramedTerminalCutTest.value P D H L F C hs hFpos hf key hpos)
    (head P D H L F C hs key hpos) (IntegralFramedCutFiniteGuards.choice P D H)
    (IntegralFramedCutFiniteGuards.degree P D H) (IntegralFramedCutFiniteGuards.cap P) q

omit L F C hs hFpos hf hpos in
theorem headIndex_unary (a : Access P) (hk : key∈FP) : UnaryFn (headIndex P D H key) :=
  ((IntegralFramedTerminalCutTest.count_unary P a D H key hk).sub (IntegralMixedOldHeightBits.birth_unary P a)).sub (UnaryFn.const 1)

attribute [local irreducible] head headIndex IntegralFramedTerminalCutTest.value IntegralFramedTerminalCutTest.count SquareSampleCompleteCoordinateSign.value

theorem evaluator (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hk : key∈FP)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) :
    SpaceFunction (fun q=>[decide (Guards P D H L F C hs hFpos hf key hpos q)]) := by
  have EA:=IntegralFramedCurrentQSquare.access_native P a D H Hnew hc hbc L F C hs hL hF hC key hk hpos
  have ES:=IntegralFramedTerminalCutTest.evaluator P D H L F C hs hFpos hf key hpos a hL hF hC hk h hb Hnew hc hbc
  have HI:=BinaryFn.ofUnary ((headIndex_unary P D H key a hk).comp pairFst_mem_FP)
  have EH:=(SquareSampleCompleteCoordinateSign.evaluator EA).precompose
    (fun q=>pair q (BinaryNatCode.encode (headIndex P D H key (pairFst q)))) (mem_FP_pair id_mem_FP HI.bits_mem_FP)
  have EH' : SpaceFunction (head P D H L F C hs key hpos) := EH.congr (funext fun q=>by rw [head]; rfl)
  exact FiniteCoefficientSignScan.evaluator _ _ _ _ _ ES EH'
    (IntegralFramedCutFiniteGuards.choice_binary P a D H h0)
    (IntegralFramedCutFiniteGuards.degree_binary P a D H h0) (IntegralFramedCutFiniteGuards.cap_binary P a)

omit hFpos hf in
theorem head_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w)
    (hfit : birth P c<IntegralFramedTerminalCutTest.count P D H key c) :
    head P D H L F C hs key hpos (pair c w)=InfinitesimalSign.encode
      (SignType.sign ((SquareSampleCompleteVertices.candidate (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w hv).val
        ⟨headIndex P D H key c,by
          have HC : (IntegralFramedCompleteSquare.input P D H L F C hs key hpos).count c=IntegralFramedTerminalCutTest.count P D H key c := by
            unfold IntegralFramedTerminalCutTest.count
            rfl
          rw [HC]
          unfold headIndex
          omega⟩)) := by
  unfold head
  rw [pairFst_pair]
  convert SquareSampleCompleteCoordinateSign.packet (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w hv
    (⟨headIndex P D H key c,by
      have HC : (IntegralFramedCompleteSquare.input P D H L F C hs key hpos).count c=IntegralFramedTerminalCutTest.count P D H key c := by
        unfold IntegralFramedTerminalCutTest.count
        rfl
      rw [HC]
      unfold headIndex
      omega⟩) using 1

end LeanCanny.Encoding.IntegralFramedTerminalCutGuards
