/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerNative
public import LeanCanny.Encoding.IntegralFramedPhysicalGridReplayScan
/-! # Native all-coordinate replay of one accepted external own sample

The external own word and the target full physical word stay fixed throughout
both scans. The final specialization constructs the actual n+8 target bank;
the packet interface also supports a native record bank at its literal context.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialExternalReplay
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialJointStratum.source
local notation "AS" => FormulaSignSlotRadialJointStratumNative.access
local notation "positive" => FormulaSignSlotRadialJointStratumSampler.positive
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input

def context (q : List Bool) := pairFst q
def target (q : List Bool) := pairFst (pairSnd q)
def word (q : List Bool) := pairSnd (pairSnd q)
def packet (ctx target word : List Bool) := pair ctx (pair target word)
theorem context_FP : context ∈ FP := pairFst_mem_FP
theorem target_FP : target ∈ FP := by polytime [target]
theorem word_FP : word ∈ FP := by polytime [word]

def fits (ctx : List Bool) : Prop := FormulaSignSlotRadialExternalContext.number ctx=0 ∨
  4*(FormulaSignSlotRadialExternalContext.number ctx-1)+FormulaSignSlotRadialExternalContext.sideNat ctx <
    ImplicitSourceGramGrid.count S (FormulaSignSlotRadialExternalContext.gridContext ctx)
theorem fits_FP : FPPred fits := by
  have HN := BinaryFn.ofUnary FormulaSignSlotRadialExternalContext.number_unary
  have HC : BinaryFn (fun ctx => ImplicitSourceGramGrid.count S (FormulaSignSlotRadialExternalContext.gridContext ctx)) :=
    (BinaryFn.ofUnary (ImplicitSourceGramGrid.count_unary S AS)).comp FormulaSignSlotRadialExternalContext.gridContext_FP
  exact (HN.eq (BinaryFn.const 0)).or
    ((((BinaryFn.const 4).mul (HN.sub (BinaryFn.const 1))).add FormulaSignSlotRadialExternalContext.sideNat_binary).lt HC)

theorem fits_slot (ctx : List Bool) (h : fits ctx) (i : ℕ) (hi : i<FormulaSignSlotRadialExternalContext.number ctx) :
    FormulaSignSlotRadialExternalContext.slot ctx i < (F).count (FormulaSignSlotRadialExternalContext.gridContext ctx) := by
  unfold fits at h
  unfold FormulaSignSlotRadialExternalContext.slot
  rcases h with h | h
  · omega
  · change _ < ImplicitSourceGramGrid.count S (FormulaSignSlotRadialExternalContext.gridContext ctx)
    omega

noncomputable def accepted (ctx : List Bool) : Prop :=
  pair (FormulaSignSlotRadialExternalContext.gridContext ctx) (FormulaSignSlotRadialExternalContext.ownWord ctx) ∈
    FormulaSignSlotRadialJointStratumSampler.language

def probeAt (q : List Bool) (i : ℕ) := IntegralFramedPhysicalGridReplayScan.query (target q) (word q)
  (FormulaSignSlotRadialExternalContext.gridContext (context q))
  (FormulaSignSlotRadialExternalContext.ownWord (context q))
  (FormulaSignSlotRadialExternalContext.slot (context q) i)
def probe (z : List Bool) := probeAt (pairFst z) (pairSnd z).length

theorem probe_FP : probe ∈ FP := by
  have HCtx : (fun z => context (pairFst z)) ∈ FP := mem_FP_comp pairFst_mem_FP context_FP
  have HI : BinaryFn (fun z => (pairSnd z).length) := BinaryFn.ofUnary (UnaryFn.length pairSnd_mem_FP)
  have HS : BinaryFn (fun z => FormulaSignSlotRadialExternalContext.slot (context (pairFst z)) (pairSnd z).length) :=
    ((BinaryFn.const 4).mul HI).add (FormulaSignSlotRadialExternalContext.sideNat_binary.comp HCtx)
  exact mem_FP_pair
    (mem_FP_pair (mem_FP_comp (f := pairFst) (g := target) pairFst_mem_FP target_FP) (mem_FP_comp (f := pairFst) (g := word) pairFst_mem_FP word_FP))
    (mem_FP_pair (mem_FP_pair (mem_FP_comp (f := fun z => context (pairFst z)) (g := FormulaSignSlotRadialExternalContext.gridContext) HCtx FormulaSignSlotRadialExternalContext.gridContext_FP)
      (mem_FP_comp (f := fun z => context (pairFst z)) (g := FormulaSignSlotRadialExternalContext.ownWord) HCtx FormulaSignSlotRadialExternalContext.ownWord_FP)) HS.bits_mem_FP)

noncomputable def agreesAt (B : Bank) (q : List Bool) : Prop :=
  ∀ i<FormulaSignSlotRadialExternalContext.number (context q),
    probeAt q i ∈ IntegralFramedPhysicalGridReplayScan.language S positive B

theorem scanEvaluator (B : Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) :
    SpaceFunction (fun q => [decide (agreesAt B q)]) := by
  have E := ((IntegralFramedPhysicalGridReplayScan.decider S AS positive B A T hT hr).precompose probe probe_FP).flagEvaluator
  refine (E.forall_unary (FormulaSignSlotRadialExternalContext.number_unary.comp context_FP)).congr (funext fun q => ?_)
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [agreesAt,probe,Set.mem_preimage,pairFst_pair,pairSnd_pair,
    List.length_replicate,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def languageAt (B : Bank) : Language := {q |
  FormulaSignSlotRadialExternalContext.external (context q) ∧ fits (context q) ∧ accepted (context q) ∧
    SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) (target q) (word q) ∧ agreesAt B q}

theorem deciderAt (B : Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) : SpaceDecider (languageAt B) := by
  have ES := SpaceFunction.ofFP _
    (((FormulaSignSlotRadialExternalContext.external_FP.and fits_FP).comp context_FP).flag_mem_FP)
  have EA := ((ImplicitSourceComponentSampler.decider S AS positive).precompose
    (fun q => pair (FormulaSignSlotRadialExternalContext.gridContext (context q))
      (FormulaSignSlotRadialExternalContext.ownWord (context q)))
    (mem_FP_pair (mem_FP_comp (f := context) (g := FormulaSignSlotRadialExternalContext.gridContext) context_FP FormulaSignSlotRadialExternalContext.gridContext_FP)
      (mem_FP_comp (f := context) (g := FormulaSignSlotRadialExternalContext.ownWord) context_FP FormulaSignSlotRadialExternalContext.ownWord_FP))).flagEvaluator
  have EV := ((SquareSampleCompleteVertices.decider (IntegralFramedPhysicalGridReplay.input_access B A T hT hr)).precompose
    (fun q => pair (target q) (word q)) (mem_FP_pair target_FP word_FP)).flagEvaluator
  apply (ES.andFlags (EA.andFlags (EV.andFlags (scanEvaluator B A T hT hr)))).decider
    (fun q => decide (q=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [languageAt,accepted,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,Set.mem_preimage,
    pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq,and_assoc]

theorem accepted_valid (ctx : List Bool) (h : accepted ctx) : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx := by
  unfold FormulaSignSlotRadialExternalCoordinates.OwnValid
  simpa only [pairFst_pair,pairSnd_pair] using h.1

private theorem point_eq (B : Bank) (t w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) t w)
    (i j : ℕ) (h : i/4=j/4) :
    IntegralFramedPhysicalGridReplay.point B t w hw i=IntegralFramedPhysicalGridReplay.point B t w hw j := by
  unfold IntegralFramedPhysicalGridReplay.point
  have HC : IntegralFramedPhysicalGridReplay.coordinate B t (ImplicitSourceGramGridReplayDatum.packet [] i 0)=
      IntegralFramedPhysicalGridReplay.coordinate B t (ImplicitSourceGramGridReplayDatum.packet [] j 0) := by
    apply Fin.ext
    rw [IntegralFramedPhysicalGridReplay.coordinate_packet,IntegralFramedPhysicalGridReplay.coordinate_packet,h]
  rw [HC]

theorem slot_div (ctx : List Bool) (i : ℕ) : FormulaSignSlotRadialExternalContext.slot ctx i/4=i := by
  have HS : FormulaSignSlotRadialExternalContext.sideNat ctx ≤ 1 := by
    unfold FormulaSignSlotRadialExternalContext.sideNat
    split_ifs <;> omega
  unfold FormulaSignSlotRadialExternalContext.slot
  omega

theorem probe_iff (B : Bank) (q : List Bool) (hf : fits (context q))
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) (target q) (word q))
    (hv : FormulaSignSlotRadialExternalCoordinates.OwnValid (context q))
    (i : ℕ) (hi : i<FormulaSignSlotRadialExternalContext.number (context q)) :
    probeAt q i ∈ IntegralFramedPhysicalGridReplayScan.language S positive B ↔
      FormulaSignSlotRadialExternalCoordinates.point (context q) hv i =
        IntegralFramedPhysicalGridReplay.point B (target q) (word q) hw (4*i) := by
  let j : Fin ((F).count (FormulaSignSlotRadialExternalContext.gridContext (context q))) :=
    ⟨FormulaSignSlotRadialExternalContext.slot (context q) i,fits_slot (context q) hf i hi⟩
  have H := IntegralFramedPhysicalGridReplayScan.packet S positive B (target q) (word q)
    (FormulaSignSlotRadialExternalContext.gridContext (context q))
    (FormulaSignSlotRadialExternalContext.ownWord (context q)) hw hv j
  have HJ : FormulaSignSlotRadialExternalCoordinates.index (context q) i=j :=
    SquareSampleInput.selected_encode F _ j
  have HP := point_eq B (target q) (word q) hw j.val (4*i) (by dsimp only [j]; rw [slot_div]; omega)
  rw [HP] at H
  simpa only [probeAt,FormulaSignSlotRadialExternalCoordinates.point,HJ] using H

theorem languageAt_iff (B : Bank) (q : List Bool) : q ∈ languageAt B ↔
    FormulaSignSlotRadialExternalContext.external (context q) ∧ fits (context q) ∧
      ∃ ha : accepted (context q),
        ∃ hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) (target q) (word q),
          ∀ i<FormulaSignSlotRadialExternalContext.number (context q),
            FormulaSignSlotRadialExternalCoordinates.point (context q) (accepted_valid _ ha) i =
              IntegralFramedPhysicalGridReplay.point B (target q) (word q) hw (4*i) := by
  constructor
  · rintro ⟨he,hf,ha,hw,hg⟩
    exact ⟨he,hf,ha,hw,fun i hi => (probe_iff B q hf hw (accepted_valid _ ha) i hi).mp (hg i hi)⟩
  · rintro ⟨he,hf,ha,hw,hg⟩
    exact ⟨he,hf,ha,hw,fun i hi => (probe_iff B q hf hw (accepted_valid _ ha) i hi).mpr (hg i hi)⟩

def mainPacket (q : List Bool) := packet (pairFst q) (pair (pairFst q) []) (pairSnd q)
theorem mainPacket_FP : mainPacket ∈ FP := by polytime [mainPacket,packet]
noncomputable def language : Language := mainPacket ⁻¹' languageAt FormulaSignSlotRadialProviderIntegerNative.bank
theorem decider : SpaceDecider language :=
  (deciderAt FormulaSignSlotRadialProviderIntegerNative.bank FormulaSignSlotRadialProviderIntegerNative.bank_access
    FormulaSignSlotRadialProviderIntegerPlan.tables FormulaSignSlotRadialProviderIntegerPlan.tables_native
    FormulaSignSlotRadialProviderIntegerNative.certifiedRepresents).precompose mainPacket mainPacket_FP
theorem mem_PSPACE : language ∈ PSPACE := decider.mem_PSPACE

end LeanCanny.Encoding.FormulaSignSlotRadialExternalReplay
