/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutSource
public import LeanCanny.Encoding.SquareSampleCompleteCoordinateSign
public import LeanCanny.Computation.FiniteCoefficientSignScan
/-! # Native per-birth cut guards over one fixed terminal tuple

A stage packet is `((original root, terminal vertex), unary birth)`. Every
coefficient/choice probe writes the birth into its indexed datum and keeps
the original vertex untouched. The head test reads the retained creating
scalar at `terminalCount-birth-1`.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutGuards
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

def root (b : List Bool) := pairFst (pairFst b)
def word (b : List Bool) := pairSnd (pairFst b)
def stage (b : List Bool) := (pairSnd b).length
def descriptor (b : List Bool) := pair (root b) (pair (pairSnd b) [])
def parent (P : Parameters) := IntegralFramedTraceCutTask.task P∘descriptor
def signQuery (q : List Bool) := pair (pairFst (pairFst q)) (pair (pairSnd (pairFst q)) (pairSnd q))
theorem root_FP : root∈FP:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem word_FP : word∈FP:=mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem stage_unary : UnaryFn stage:=UnaryFn.length pairSnd_mem_FP
theorem descriptor_FP : descriptor∈FP:=mem_FP_pair root_FP (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP []))
theorem parent_FP (P : Parameters) (a : Access P) : parent P∈FP:=mem_FP_comp descriptor_FP (IntegralFramedTraceCutTask.task_FP P a)
theorem signQuery_FP : signQuery∈FP:=mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)

noncomputable def choice (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (b : List Bool) :=
  IntegralMixedRawKindBits.choice (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent P b))
noncomputable def degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (b : List Bool) :=
  (family P D H).degree (IntegralMixedVirtualTaskBits.saved P (parent P b))
def cap (P : Parameters) (b : List Bool) := 2^P.width (root b)
noncomputable def count (P : Parameters) (D : Plan P) (b : List Bool) := IntegralFramedTraceCutMetadata.length P D (root b)+1
noncomputable def headIndex (P : Parameters) (D : Plan P) (b : List Bool) := count P D b-stage b-1

attribute [local irreducible] parent IntegralFramedTraceCutTask.task IntegralMixedVirtualTaskBits.saved

theorem choice_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) : BinaryFn (choice P D H) :=
  (IntegralMixedFramedNormalizationBits.kind P a D H h0).choice.comp
    (mem_FP_comp (parent_FP P a) (IntegralMixedVirtualTaskBits.saved_FP P a))
theorem degree_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) : BinaryFn (degree P D H) :=
  (IntegralMixedFramedNormalizationBits.degree P a D H h0).comp
    (mem_FP_comp (parent_FP P a) (IntegralMixedVirtualTaskBits.saved_FP P a))
theorem cap_binary (P : Parameters) (a : Access P) : BinaryFn (cap P) :=
  (BinaryFn.const 2).powUnary (a.width.comp root_FP)
theorem count_unary (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) : UnaryFn (count P D) :=
  ((IntegralFramedTraceCutMetadata.length_unary P D H h0).comp root_FP).add (UnaryFn.const 1)
theorem headIndex_unary (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) : UnaryFn (headIndex P D) :=
  ((count_unary P D H h0).sub stage_unary).sub (UnaryFn.const 1)

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)

noncomputable def sign := IntegralFramedTraceCutSource.value P D H L F C hs hFpos hf∘signQuery
noncomputable def head (b : List Bool) := SquareSampleCompleteCoordinateSign.value
  (IntegralFramedTraceCutSource.input P D H L F C hs) (pair (pairFst b) (BinaryNatCode.encode (headIndex P D b)))
noncomputable abbrev Guards (b : List Bool) : Prop := FiniteCoefficientSignScan.Guards
  (sign P D H L F C hs hFpos hf) (head P D H L F C hs) (choice P D H) (degree P D H) (cap P) b

attribute [local irreducible] choice degree cap count headIndex sign head SquareSampleCompleteCoordinateSign.value

theorem evaluator (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) :
    SpaceFunction (fun b=>[decide (Guards P D H L F C hs hFpos hf b)]) := by
  have EA:=IntegralFramedCurrentQSquare.access_native P a D H Hnew hc hbc L F C hs hL hF hC
    (IntegralFramedTraceCutMetadata.terminal P D) (IntegralFramedTraceCutMetadata.terminal_FP P D H h0)
    (IntegralFramedTraceCutMetadata.terminal_positive P D H)
  have ES:=(IntegralFramedTraceCutSource.evaluator P D H L F C hs hFpos hf a hL hF hC h0 h hb Hnew hc hbc).precompose signQuery signQuery_FP
  have ES' : SpaceFunction (sign P D H L F C hs hFpos hf):=ES.congr (funext fun q=>by rw [sign])
  have HI : BinaryFn (headIndex P D):=BinaryFn.ofUnary (headIndex_unary P D H h0)
  have EH:=(SquareSampleCompleteCoordinateSign.evaluator EA).precompose
    (fun b=>pair (pairFst b) (BinaryNatCode.encode (headIndex P D b))) (mem_FP_pair pairFst_mem_FP HI.bits_mem_FP)
  have EH' : SpaceFunction (head P D H L F C hs):=EH.congr (funext fun b=>by rw [head]; rfl)
  exact FiniteCoefficientSignScan.evaluator _ _ _ _ _ ES' EH' (choice_binary P a D H h0) (degree_binary P a D H h0) (cap_binary P a)

end LeanCanny.Encoding.IntegralFramedTraceCutGuards
