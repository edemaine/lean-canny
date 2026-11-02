/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutCoefficientSign
public import LeanCanny.Encoding.SquareSampleCompleteCoordinateSign
public import LeanCanny.Computation.FiniteCoefficientSignScan
/-! # Native finite selected-cut guards at one actual successor vertex

Every lower-choice and higher-coefficient test uses the same joint vertex.
The final guard removes exactly the possible zero root introduced by
padding. Original header metadata supplies the recorded choice and degree;
no relative-validity, root, coefficient or denominator oracle is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutFiniteGuards
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralFramedCutCoefficientTest.value

noncomputable def choice (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  IntegralMixedRawKindBits.choice (family P D H) (IntegralMixedVirtualTaskBits.saved P (pairFst q))
noncomputable def degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  (family P D H).degree (IntegralMixedVirtualTaskBits.saved P (pairFst q))
def cap (P : Parameters) (q : List Bool) := 2^P.width (RankedHistoryTask.root (pairFst q))

theorem choice_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) : BinaryFn (choice P D H) :=
  (IntegralMixedFramedNormalizationBits.kind P a D H h0).choice.comp
    (mem_FP_comp pairFst_mem_FP (IntegralMixedVirtualTaskBits.saved_FP P a))
theorem degree_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) : BinaryFn (degree P D H) :=
  (IntegralMixedFramedNormalizationBits.degree P a D H h0).comp
    (mem_FP_comp pairFst_mem_FP (IntegralMixedVirtualTaskBits.saved_FP P a))
theorem cap_binary (P : Parameters) (a : Access P) : BinaryFn (cap P) :=
  (BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp pairFst_mem_FP RankedHistoryTask.root_FP))

variable (P : Parameters) (a : Access P) (D : Plan P)
  (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
  (hFpos : ∀ root,1≤F root)
  (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
  (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)


noncomputable def head : List Bool→List Bool :=
  fun q=>SquareSampleCompleteCoordinateSign.value (IntegralFramedCutSuccessor.input P D H L F C hs) (pair q [])
noncomputable abbrev Guards (q : List Bool) : Prop :=
  FiniteCoefficientSignScan.Guards (IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf)
    (head P D H L F C hs) (choice P D H) (degree P D H) (cap P) q

attribute [local irreducible] choice degree cap head SquareSampleCompleteCoordinateSign.value

include a hL hF hC h hb in
theorem evaluator
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) :
    SpaceFunction (fun q=>[decide (Guards P D H L F C hs hFpos hf q)]) := by
  have EA:=IntegralFramedCutSuccessor.access P a D H Hnew hc hbc L F C hs hL hF hC
  have ES:=IntegralFramedCutCoefficientTest.evaluator P a D H L F C hs hL hF hC hFpos hf h hb Hnew hc hbc
  have EH0:=SquareSampleCompleteCoordinateSign.evaluator
    (F:=IntegralFramedCutSuccessor.input P D H L F C hs) EA
  have HEH : (SquareSampleCompleteCoordinateSign.value (IntegralFramedCutSuccessor.input P D H L F C hs) ∘
      (fun q=>pair q []))=head P D H L F C hs := by
    funext q
    rw [head]
    rfl
  have EH : SpaceFunction (head P D H L F C hs) :=
    (EH0.precompose (fun q=>pair q []) (mem_FP_pair id_mem_FP (constFn_mem_FP []))).congr HEH
  change SpaceFunction (fun q=>[decide (FiniteCoefficientSignScan.Guards
    (IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf)
    (head P D H L F C hs) (choice P D H) (degree P D H) (cap P) q)])
  exact FiniteCoefficientSignScan.evaluator
    (IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf)
    (head P D H L F C hs) (choice P D H) (degree P D H) (cap P) ES EH
    (choice_binary P a D H h0) (degree_binary P a D H h0) (cap_binary P a)

omit a hL hF hC h hb hFpos hf in
theorem head_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w) :
    head P D H L F C hs (pair c w)=InfinitesimalSign.encode
      (SignType.sign ((SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv).val
        ⟨0,IntegralFramedCutSuccessor.positive P D H c⟩)) := by
  unfold head
  exact SquareSampleCompleteCoordinateSign.packet _ c w hv ⟨0,IntegralFramedCutSuccessor.positive P D H c⟩

end LeanCanny.Encoding.IntegralFramedCutFiniteGuards
