/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalReplay
public import LeanCanny.Encoding.IntegralFramedPhysicalCandidateReplayThom
/-! # Source-associated OLD or EXTERNAL replay on an actual native bank

An external packet is checked against its canonical reconstruction before
accepting its Q-filtered own word. Both roles constrain original prelude
coordinates; neither asserts attachment of the latest critical point.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderReplay
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open IntegralFramedBankQuery (Bank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope
abbrev context := FormulaSignSlotRadialExternalReplay.context
abbrev target := FormulaSignSlotRadialExternalReplay.target
abbrev word := FormulaSignSlotRadialExternalReplay.word
abbrev packet := FormulaSignSlotRadialExternalReplay.packet

def header := FormulaSignSlotRadialExternalPrelude.jointHeader
def choice (ctx : List Bool) := Nat.fromBitsLE (pairSnd
  (ImplicitSourceGramGrid.header (FormulaSignSlotRadialExternalContext.gridContext ctx)))
def gamma (ctx : List Bool) := pairSnd (FormulaSignSlotRadialExternalContext.gridContext ctx)
def label (ctx : List Bool) := pairSnd (pairFst ctx)
def positiveSide (ctx : List Bool) : Prop := FormulaSignSlotRadialExternalContext.sideCode ctx=[true]
noncomputable def selectedSource (ctx : List Bool) := if positiveSide ctx then
  FormulaSignSlotRadialJointLayout.source true (header ctx) else
  FormulaSignSlotRadialJointLayout.source false (header ctx)
noncomputable def sideBits (ctx : List Bool) := if positiveSide ctx then [true] else [false]
noncomputable def canonical (ctx : List Bool) := pair (pair (selectedSource ctx) (label ctx))
  (pair [true] (pair (pair (FormulaSignSlotRadialJointStratum.packet (header ctx) (choice ctx)) (gamma ctx))
    (pair (sideBits ctx) (FormulaSignSlotRadialExternalContext.ownWord ctx))))
noncomputable def associated (ctx : List Bool) : Prop := ctx=canonical ctx

theorem header_FP : header∈FP := FormulaSignSlotRadialExternalPrelude.jointHeader_FP
theorem choice_binary : BinaryFn choice := BinaryFn.fromBits (by polytime [ImplicitSourceGramGrid.header,
  FormulaSignSlotRadialExternalContext.gridContext,FormulaSignSlotRadialExternalContext.metadata])
theorem gamma_FP : gamma∈FP := mem_FP_comp FormulaSignSlotRadialExternalContext.gridContext_FP pairSnd_mem_FP
theorem label_FP : label∈FP := by polytime [label]
theorem positiveSide_FP : FPPred positiveSide := Brackets.stringEq_fppred
  FormulaSignSlotRadialExternalContext.sideCode_FP (constFn_mem_FP [true])
theorem selectedSource_FP : selectedSource∈FP := positiveSide_FP.ite_mem_FP
  (mem_FP_comp (f:=header) (g:=FormulaSignSlotRadialJointLayout.source true) header_FP (FormulaSignSlotRadialJointLayout.source_FP true))
  (mem_FP_comp (f:=header) (g:=FormulaSignSlotRadialJointLayout.source false) header_FP (FormulaSignSlotRadialJointLayout.source_FP false))
theorem sideBits_FP : sideBits∈FP := positiveSide_FP.ite_mem_FP (constFn_mem_FP _) (constFn_mem_FP _)
theorem canonical_FP : canonical∈FP := mem_FP_pair (mem_FP_pair selectedSource_FP label_FP)
  (mem_FP_pair (constFn_mem_FP _) (mem_FP_pair
    (mem_FP_pair (mem_FP_pair header_FP choice_binary.bits_mem_FP) gamma_FP)
    (mem_FP_pair sideBits_FP FormulaSignSlotRadialExternalContext.ownWord_FP)))
theorem associated_FP : FPPred associated := Brackets.stringEq_fppred id_mem_FP canonical_FP

theorem canonical_eq_packet (ctx : List Bool) : canonical ctx=
    FormulaSignSlotRadialExternalContext.packet (header ctx) (choice ctx) (gamma ctx) (label ctx)
      (FormulaSignSlotRadialExternalContext.side ctx) (FormulaSignSlotRadialExternalContext.ownWord ctx) := by
  by_cases h : positiveSide ctx <;>
    simp only [canonical,selectedSource,sideBits,FormulaSignSlotRadialExternalContext.packet,
      FormulaSignSlotRadialExternalContext.side,positiveSide] at h ⊢ <;> simp [h]

theorem associated_packet (H : List Bool) (K : ℕ) (G l : List Bool) (s : Bool) (w : List Bool) :
    associated (FormulaSignSlotRadialExternalContext.packet H K G l s w) := by
  unfold associated
  rw [canonical_eq_packet]
  cases s <;> simp [header,FormulaSignSlotRadialExternalPrelude.jointHeader,choice,gamma,label,
    FormulaSignSlotRadialExternalContext.side,FormulaSignSlotRadialExternalContext.sideCode,
    FormulaSignSlotRadialExternalContext.gridContext,FormulaSignSlotRadialExternalContext.ownWord,
    FormulaSignSlotRadialExternalContext.metadata,FormulaSignSlotRadialExternalContext.packet,
    ImplicitSourceGramGrid.header,FormulaSignSlotRadialJointStratum.header,
    FormulaSignSlotRadialJointStratum.packet,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem associated_witness (ctx : List Bool) (h : associated ctx) :
    ∃ H K G l s w,ctx=FormulaSignSlotRadialExternalContext.packet H K G l s w :=
  ⟨header ctx,choice ctx,gamma ctx,label ctx,FormulaSignSlotRadialExternalContext.side ctx,
    FormulaSignSlotRadialExternalContext.ownWord ctx,h.trans (canonical_eq_packet ctx)⟩

noncomputable def oldLanguageAt (B : Bank) := IntegralFramedPhysicalCandidateReplayThom.language hn ht ha B
noncomputable def externalLanguageAt (B : Bank) : Language := {q | associated (context q) ∧
  q∈FormulaSignSlotRadialExternalReplay.languageAt B}
noncomputable def languageAt (B : Bank) : Language := {q |
  if FormulaSignSlotRadialExternalContext.external (context q) then q∈externalLanguageAt B else q∈oldLanguageAt B}

theorem deciderAt (B : Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) : SpaceDecider (languageAt B) := by
  have EO := IntegralFramedPhysicalCandidateReplayThom.decider hn ht ha B A T hT hr
  have EE := (SpaceFunction.ofFP _ ((associated_FP.comp FormulaSignSlotRadialExternalReplay.context_FP).flag_mem_FP)).andFlags
    (FormulaSignSlotRadialExternalReplay.deciderAt B A T hT hr).flagEvaluator
  have ES := SpaceFunction.ofFP _
    ((FormulaSignSlotRadialExternalContext.external_FP.comp FormulaSignSlotRadialExternalReplay.context_FP).flag_mem_FP)
  have E := (ES.pairOutputs (EE.pairOutputs EO.flagEvaluator)).postcompose
    (fun z=>if pairFst z=[true] then pairFst (pairSnd z) else pairSnd (pairSnd z))
    ((Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).ite_mem_FP
      (by polytime) (by polytime))
  apply E.decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  by_cases h : FormulaSignSlotRadialExternalContext.external (context q) <;>
    simp [languageAt,externalLanguageAt,oldLanguageAt,h]

theorem external_iff (B : Bank) (q : List Bool)
    (h : FormulaSignSlotRadialExternalContext.external (context q)) :
    q∈languageAt B ↔ associated (context q) ∧ q∈FormulaSignSlotRadialExternalReplay.languageAt B := by
  simp only [languageAt,Set.mem_ofPred_eq,h,ite_true,externalLanguageAt]
theorem old_iff (B : Bank) (q : List Bool)
    (h : ¬FormulaSignSlotRadialExternalContext.external (context q)) :
    q∈languageAt B ↔ q∈IntegralFramedPhysicalCandidateReplayThom.language hn ht ha B := by
  simp only [languageAt,Set.mem_ofPred_eq,h,ite_false,oldLanguageAt]

theorem old_point_eq (B : Bank) (ctx t w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) t w)
    (i : Fin (FormulaSignSlotRadialExternalContext.number ctx)) :
    IntegralFramedPhysicalCandidateReplay.point (n:=CanonicalAuxiliaryCandidateCover.dimension) B ctx t w hw i =
      IntegralFramedPhysicalGridReplay.point B t w hw (4*i.val) := by
  unfold IntegralFramedPhysicalCandidateReplay.point IntegralFramedPhysicalGridReplay.point
  congr 1
  apply Fin.ext
  rw [IntegralFramedPhysicalCandidateReplay.coordinate_packet,IntegralFramedPhysicalGridReplay.coordinate_packet]
  change IntegralFramedPhysicalGridReplay.count B t-1-i.val =
    IntegralFramedPhysicalGridReplay.count B t-1-(4*i.val)/4
  omega

theorem mem_PSPACEAt (B : Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) : languageAt B∈PSPACE :=
  (deciderAt B A T hT hr).mem_PSPACE
end LeanCanny.Encoding.FormulaSignSlotRadialProviderReplay
