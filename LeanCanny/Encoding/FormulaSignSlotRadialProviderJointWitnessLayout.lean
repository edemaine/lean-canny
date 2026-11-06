/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderOriginalBudget
public import LeanCanny.Encoding.IntegralMixedRoadmapWordLabel
/-! # One shared sampled stratum and two literal provider seed pairs -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderJointWitness
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def header (q : List Bool) := pairFst q
def data (q : List Bool) := pairSnd q
def kindBits (q : List Bool) := pairFst (data q)
def kind (q : List Bool) := Nat.fromBitsLE (kindBits q)
def gamma (q : List Bool) := pairFst (pairSnd (data q))
def ownWord (q : List Bool) := pairFst (pairSnd (pairSnd (data q)))
def seedTable (q : List Bool) := pairSnd (pairSnd (pairSnd (data q)))
def seedPair (side : Bool) (q : List Bool) := if side then pairSnd (seedTable q) else pairFst (seedTable q)
def oldSeed (side : Bool) (q : List Bool) := pairFst (seedPair side q)
def externalSeed (side : Bool) (q : List Bool) := pairSnd (seedPair side q)
def packet (H : List Bool) (k : ℕ) (Gamma w aL eL aR eR : List Bool) :=
  pair H (pair (BinaryNatCode.encode k) (pair Gamma (pair w (pair (pair aL eL) (pair aR eR)))))

theorem header_FP : header∈FP := pairFst_mem_FP
theorem data_FP : data∈FP := pairSnd_mem_FP
theorem kindBits_FP : kindBits∈FP := by polytime [kindBits,data]
theorem kind_binary : BinaryFn kind := BinaryFn.fromBits kindBits_FP
theorem gamma_FP : gamma∈FP := by polytime [gamma,data]
theorem ownWord_FP : ownWord∈FP := by polytime [ownWord,data]
theorem seedPair_FP (side : Bool) : seedPair side∈FP := by cases side <;> polytime [seedPair,seedTable,data]
theorem oldSeed_FP (side : Bool) : oldSeed side∈FP := mem_FP_comp (seedPair_FP side) pairFst_mem_FP
theorem externalSeed_FP (side : Bool) : externalSeed side∈FP := mem_FP_comp (seedPair_FP side) pairSnd_mem_FP

noncomputable def label (side : Bool) (H : List Bool) :=
  CanonicalAuxiliaryCandidateLabels.candidate (FormulaSignSlotRadialJointLayout.labelQuery side H)
theorem label_FP (side : Bool) : label side∈FP :=
  mem_FP_comp (FormulaSignSlotRadialJointLayout.labelQuery_FP side) CanonicalAuxiliaryCandidateLabels.candidate_FP

def stratum (q : List Bool) := FormulaSignSlotRadialJointStratum.packet (header q) (kind q)
def sampleQuery (q : List Bool) := pair (pair (stratum q) (gamma q)) (ownWord q)
noncomputable def externalProvider (side : Bool) (q : List Bool) :=
  FormulaSignSlotRadialExternalContext.packet (header q) (kind q) (gamma q) (label side (header q)) side (ownWord q)
noncomputable def oldProvider (side : Bool) (q : List Bool) :=
  FormulaSignSlotRadialProviderPair.oldOf (externalProvider side q)

theorem stratum_FP : stratum∈FP := mem_FP_pair header_FP kind_binary.bits_mem_FP
theorem sampleQuery_FP : sampleQuery∈FP := mem_FP_pair (mem_FP_pair stratum_FP gamma_FP) ownWord_FP
theorem externalProvider_FP (side : Bool) : externalProvider side∈FP := by
  unfold externalProvider FormulaSignSlotRadialExternalContext.packet
  exact mem_FP_pair
    (mem_FP_pair (mem_FP_comp (f:=header) (g:=FormulaSignSlotRadialJointLayout.source side) header_FP (FormulaSignSlotRadialJointLayout.source_FP side))
      (mem_FP_comp (f:=header) (g:=label side) header_FP (label_FP side)))
    (mem_FP_pair (constFn_mem_FP [true]) (mem_FP_pair (mem_FP_pair stratum_FP gamma_FP)
      (mem_FP_pair (constFn_mem_FP [side]) ownWord_FP)))
theorem oldProvider_FP (side : Bool) : oldProvider side∈FP :=
  mem_FP_comp (externalProvider_FP side) FormulaSignSlotRadialProviderPair.oldOf_FP

noncomputable def kindWidth (H : List Bool) := (FormulaSignSlotRadialProviderOriginalBudget.featureCount H).size
theorem kindWidth_unary : UnaryFn kindWidth :=
  (UnaryFn.length FormulaSignSlotRadialProviderOriginalBudget.featureCount_binary.bits_mem_FP).of_eq
    (fun _=>BinaryNatCode.length_encode _)
noncomputable def rawBudget (H : List Bool) := 2*kindWidth H+
  2*FormulaSignSlotRadialProviderOriginalBudget.tableBudget H+
  2*FormulaSignSlotRadialProviderOriginalBudget.ownwordBudget H+
  9*FormulaSignSlotRadialProviderOriginalBudget.vertexBudget H+14
theorem rawBudget_unary : UnaryFn rawBudget :=
  (((((UnaryFn.const 2).mul kindWidth_unary).add
    ((UnaryFn.const 2).mul FormulaSignSlotRadialProviderOriginalBudget.tableBudget_unary)).add
    ((UnaryFn.const 2).mul FormulaSignSlotRadialProviderOriginalBudget.ownwordBudget_unary)).add
    ((UnaryFn.const 9).mul FormulaSignSlotRadialProviderOriginalBudget.vertexBudget_unary)).add (UnaryFn.const 14)
noncomputable def width (H : List Bool) := 2*rawBudget H+2
theorem width_unary : UnaryFn width := ((UnaryFn.const 2).mul rawBudget_unary).add (UnaryFn.const 2)

theorem packet_readers (H : List Bool) (k : ℕ) (Gamma w aL eL aR eR : List Bool) :
    header (packet H k Gamma w aL eL aR eR)=H ∧kind (packet H k Gamma w aL eL aR eR)=k ∧
    gamma (packet H k Gamma w aL eL aR eR)=Gamma ∧ownWord (packet H k Gamma w aL eL aR eR)=w ∧
    seedPair false (packet H k Gamma w aL eL aR eR)=pair aL eL ∧
    seedPair true (packet H k Gamma w aL eL aR eR)=pair aR eR := by
  simp only [header,kind,kindBits,data,gamma,ownWord,seedPair,seedTable,packet,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,Bool.false_eq_true,ite_false,ite_true,and_self]

theorem packet_length (H : List Bool) (k : ℕ) (Gamma w aL eL aR eR : List Bool)
    (hk : k≤FormulaSignSlotRadialProviderOriginalBudget.featureCount H)
    (hGamma : Gamma.length≤FormulaSignSlotRadialProviderOriginalBudget.tableBudget H)
    (hw : w.length≤FormulaSignSlotRadialProviderOriginalBudget.ownwordBudget H)
    (haL : aL.length≤FormulaSignSlotRadialProviderOriginalBudget.vertexBudget H)
    (heL : eL.length≤FormulaSignSlotRadialProviderOriginalBudget.vertexBudget H)
    (haR : aR.length≤FormulaSignSlotRadialProviderOriginalBudget.vertexBudget H)
    (heR : eR.length≤FormulaSignSlotRadialProviderOriginalBudget.vertexBudget H) :
    (data (packet H k Gamma w aL eL aR eR)).length≤rawBudget H := by
  have HK:=Nat.size_le_size hk
  simp only [data,packet,pairSnd_pair,pair_length,BinaryNatCode.length_encode]
  unfold rawBudget kindWidth
  omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderJointWitness
