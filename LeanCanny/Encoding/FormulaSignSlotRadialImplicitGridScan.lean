/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridTest
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGeometry
/-! # Every radial grid equation is tested on one unchanged implicit sample -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridScan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
local notation "env" => FormulaSignSlotRadialImplicitGridTest.env

def context (p : List Bool) := pairFst (pairFst p)
def word (p : List Bool) := pairSnd (pairFst p)
def choices (p : List Bool) := pairSnd p
def packet (c w table : List Bool) :=pair (pair c w) table
noncomputable def count (p : List Bool) := FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header (context p))
theorem count_unary : UnaryFn count := FormulaSignSlotRadialJointLayout.spatialCount_unary.comp
  (mem_FP_comp (f:=context) (g:=FormulaSignSlotRadialImplicitGridTest.header)
    (show context∈FP by polytime [context]) FormulaSignSlotRadialImplicitGridTest.header_FP)

def query (r : List Bool) :=pair (pairFst (pairFst r))
  (pair (BinaryNatCode.encode (pairSnd r).length)
    (WordList.reader (pair (choices (pairFst r)) (BinaryNatCode.encode (pairSnd r).length))))
theorem query_FP : query∈FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  (mem_FP_pair (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP
    (mem_FP_comp (g:=WordList.reader) (mem_FP_pair (show (fun r=>choices (pairFst r))∈FP by polytime [choices])
      (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP) WordList.reader_FP))

theorem query_packet (c w table : List Bool) (i : ℕ) :
    query (pair (packet c w table) (List.replicate i true))=
      pair (pair c w) (pair (BinaryNatCode.encode i) (WordList.get table i)) := by
  simp only [query,choices,packet,pairFst_pair,pairSnd_pair,List.length_replicate,WordList.reader_packet]

noncomputable def Holds (p : List Bool) :=∀i<count p,
  query (pair p (List.replicate i true))∈FormulaSignSlotRadialImplicitGridTest.language
theorem holds_evaluator : SpaceFunction (fun p=>[decide (Holds p)]) := by
  have E:=(FormulaSignSlotRadialImplicitGridTest.decider.precompose query query_FP).flagEvaluator.forall_unary count_unary
  exact E.congr (funext fun p=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Holds,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq])
noncomputable def language : Language := {p |SquareSampleCompleteVertices.Valid F (context p) (word p)∧Holds p}
theorem decider : SpaceDecider language := by
  have V:=(SquareSampleCompleteVertices.decider (ImplicitSourceGramGrid.access FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive)).precompose
    pairFst pairFst_mem_FP
  apply (V.flagEvaluator.andFlags holds_evaluator).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro p
  simp only [language,context,word,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,Set.mem_preimage,
    List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE : language∈PSPACE := decider.mem_PSPACE

attribute [local irreducible] FormulaSignSlotRadialJointGridSource.source
  ImplicitSourceGramGrid.input FormulaSignSlotRadialJointStratum.source

/-- A raw scan has literal polynomial semantics on this sample's OWN tuple. -/
theorem holds_packet_iff (c w table : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    Holds (packet c w table) ↔
      ∀i<FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c),
        (FormulaSignSlotRadialJointGridSource.source.polynomial
          (pair (FormulaSignSlotRadialImplicitGridTest.header c) (pair (BinaryNatCode.encode i) (WordList.get table i)))).eval₂ (Int.castRingHom ℝ)
          (fun j=>env c w hw j.val)=0 := by
  unfold Holds
  simp only [count,context,packet,pairFst_pair]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  change query (pair (packet c w table) (List.replicate i true))∈FormulaSignSlotRadialImplicitGridTest.language ↔_
  rw [query_packet c w table i,FormulaSignSlotRadialImplicitGridTest.language_packet_iff _ _ _ hw]
  have HE : FormulaSignSlotRadialImplicitGridTest.read
      (pair c (pair (BinaryNatCode.encode i) (WordList.get table i)))=
      pair (FormulaSignSlotRadialImplicitGridTest.header c) (pair (BinaryNatCode.encode i) (WordList.get table i)) := by
    unfold FormulaSignSlotRadialImplicitGridTest.read
    rw [pairFst_pair,pairSnd_pair]
  exact iff_of_eq (congrArg (fun z=>
    (FormulaSignSlotRadialJointGridSource.source.polynomial z).eval₂ (Int.castRingHom ℝ)
      (fun j=>env c w hw j.val)=0) HE)


private theorem natural_point_heq {a b :ℕ} (h :a=b) (v :ℕ→ℝ) :
    HEq (fun i :Fin a=>v i.val) (fun i :Fin b=>v i.val) :=by cases h;rfl

private theorem coordinate_evaluation_transport (a b :List Bool) (h :a=b)
    (u :Fin (FormulaSignSlotCenteredRadialGraph.d a)→ℝ)
    (v :Fin (FormulaSignSlotCenteredRadialGraph.d b)→ℝ) (hu :HEq u v)
    (i :Fin (FormulaSignSlotCenteredRadialGraph.N a+FormulaSignSlotCenteredRadialGraph.d a+1))
    (j :Fin (FormulaSignSlotCenteredRadialGraph.N b+FormulaSignSlotCenteredRadialGraph.d b+1))
    (hi :i.val=j.val) (r x :ℝ) :
    (FormulaSignSlotRadialParameterEliminant.coordinate a u i).eval₂ (Polynomial.evalRingHom r) x=
      (FormulaSignSlotRadialParameterEliminant.coordinate b v j).eval₂ (Polynomial.evalRingHom r) x := by
  cases h
  have HE :u=v:=eq_of_heq hu
  subst v
  have HI :i=j:=Fin.ext hi
  subst j
  rfl

private theorem radial_packet (H0 :List Bool) (i :ℕ) (tau :List Bool) :
    FormulaSignSlotRadialJointGridLayout.radial (pair H0 (pair (BinaryNatCode.encode i) tau))=
      FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H0) i := by
  unfold FormulaSignSlotRadialJointGridLayout.radial FormulaSignSlotRadialJointGridLayout.sliceContext
  simp only [FormulaSignSlotRadialJointGridLayout.header,FormulaSignSlotRadialJointGridLayout.coordinateWord,
    FormulaSignSlotRadialJointGridLayout.tauInput,pairFst_pair,pairSnd_pair,
    FormulaSignSlotRadialCoordinatePacket.writer_packet]

/-- Selection is a genuine same-center coefficient receipt. Once verified,
the literal feature is exactly the required geometric grid coordinate. -/
theorem selected_evaluation (H0 :List Bool) (i :Fin (FormulaSignSlotRadialJointLayout.spatialCount H0))
    (tau :List Bool) (v :ℕ→ℝ) (D :ℕ)
    (hg :let z:=pair H0 (pair (BinaryNatCode.encode i.val) tau)
      FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialJointGridLayout.radial z)
        (FormulaSignSlotRadialJointGridSource.center z v)
        (Nat.fromBitsLE (FormulaSignSlotRadialJointGridLayout.tauWord z)) D) :
    (FormulaSignSlotRadialJointGridSource.source.polynomial
      (pair H0 (pair (BinaryNatCode.encode i.val) tau))).eval₂ (Int.castRingHom ℝ) (fun j=>v j.val)=
      (FormulaSignSlotRadialParameterEliminant.coordinate (FormulaSignSlotRadialJointLayout.source true H0)
        (FormulaSignSlotRadialJointGeometry.center H0 v) i).eval₂
          (Polynomial.evalRingHom (FormulaSignSlotRadialJointGeometry.parameter H0 v))
          (FormulaSignSlotRadialJointGeometry.spatialPoint H0 v i) := by
  let z:=pair H0 (pair (BinaryNatCode.encode i.val) tau)
  have HR :pairFst (FormulaSignSlotRadialJointGridLayout.radial z)=
      FormulaSignSlotRadialJointLayout.source true H0 := by
    rw [radial_packet H0 i.val tau,FormulaSignSlotRadialCoordinatePacket.root]
  have HC :HEq (FormulaSignSlotRadialJointGridSource.center z v)
      (FormulaSignSlotRadialJointGeometry.center H0 v) := by
    have HA : HEq (FormulaSignSlotRadialJointGridSource.center z v)
        (fun j :Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst (FormulaSignSlotRadialJointGridLayout.radial z)))=>v (4*j.val)) :=by
      unfold FormulaSignSlotRadialJointGridSource.center
      rfl
    have HB : HEq (FormulaSignSlotRadialJointGeometry.center H0 v)
        (fun j :Fin (FormulaSignSlotCenteredRadialGraph.d (FormulaSignSlotRadialJointLayout.source true H0))=>v (4*j.val)) :=by
      unfold FormulaSignSlotRadialJointGeometry.center FormulaSignSlotRadialJointLayout.column
      rfl
    exact HA.trans ((natural_point_heq (congrArg FormulaSignSlotCenteredRadialGraph.d HR) (fun j=>v (4*j))).trans HB.symm)
  have HI :(FormulaSignSlotRadialEliminantInput.coordinate (FormulaSignSlotRadialJointGridLayout.radial z)).val=i.val := by
    rw [radial_packet H0 i.val tau,FormulaSignSlotRadialCoordinatePacket.selected]
    apply Nat.min_eq_left
    have HB:=i.isLt
    change i.val<FormulaSignSlotCenteredRadialGraph.N (FormulaSignSlotRadialJointLayout.source true H0)+
      FormulaSignSlotCenteredRadialGraph.d (FormulaSignSlotRadialJointLayout.source true H0)+1 at HB
    omega
  have HE:=FormulaSignSlotRadialJointGridSource.selected_evaluation z v D hg
  have HS :FormulaSignSlotRadialJointGridLayout.selected z=i.val:=HI
  simp only [z,FormulaSignSlotRadialJointGridLayout.header,pairFst_pair] at HE
  rw [HS] at HE
  exact HE.trans (coordinate_evaluation_transport _ _ HR _ _ HC _ i HI _ _)


noncomputable def Selections (c w table :List Bool) (hw :SquareSampleCompleteVertices.Valid F c w) :Prop :=
  ∀i :Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c)),∃D :ℕ,
    let z:=pair (FormulaSignSlotRadialImplicitGridTest.header c) (pair (BinaryNatCode.encode i.val) (WordList.get table i.val))
    FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialJointGridLayout.radial z)
      (FormulaSignSlotRadialJointGridSource.center z (env c w hw))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointGridLayout.tauWord z)) D

attribute [local irreducible] FormulaSignSlotRadialParameterEliminant.coordinate

/-- Under the genuine same-center selection receipts, all literal native zero
tests are exactly membership in the actual parameter grid. -/
theorem language_grid_iff (c w table :List Bool) (hw :SquareSampleCompleteVertices.Valid F c w)
    (hs :Selections c w table hw) : packet c w table∈language ↔
    FormulaSignSlotRadialJointGeometry.spatialPoint (FormulaSignSlotRadialImplicitGridTest.header c) (env c w hw)∈
      FormulaSignSlotRadialParameterGrid.grid
        (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitGridTest.header c))
        (FormulaSignSlotRadialJointGeometry.center (FormulaSignSlotRadialImplicitGridTest.header c) (env c w hw))
        (FormulaSignSlotRadialJointGeometry.parameter (FormulaSignSlotRadialImplicitGridTest.header c) (env c w hw)) := by
  have HL : packet c w table∈language ↔Holds (packet c w table) :=by
    simp only [language,Set.mem_ofPred_eq,context,word,packet,pairFst_pair,pairSnd_pair,hw,true_and]
  rw [HL,holds_packet_iff c w table hw]
  change (∀i<FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c),
    (FormulaSignSlotRadialJointGridSource.source.polynomial
      (pair (FormulaSignSlotRadialImplicitGridTest.header c) (pair (BinaryNatCode.encode i) (WordList.get table i)))).eval₂
        (Int.castRingHom ℝ) (fun j=>env c w hw j.val)=0) ↔∀i,
    (FormulaSignSlotRadialParameterEliminant.coordinate
      (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitGridTest.header c))
      (FormulaSignSlotRadialJointGeometry.center (FormulaSignSlotRadialImplicitGridTest.header c) (env c w hw)) i).eval₂
      (Polynomial.evalRingHom (FormulaSignSlotRadialJointGeometry.parameter (FormulaSignSlotRadialImplicitGridTest.header c) (env c w hw)))
      (FormulaSignSlotRadialJointGeometry.spatialPoint (FormulaSignSlotRadialImplicitGridTest.header c) (env c w hw) i)=0
  constructor
  · intro HE i
    obtain ⟨D,hD⟩:=hs i
    exact (selected_evaluation _ i _ (env c w hw) D hD).symm.trans (HE i.val i.isLt)
  · intro HE i hi
    obtain ⟨D,hD⟩:=hs ⟨i,hi⟩
    exact (selected_evaluation _ ⟨i,hi⟩ _ (env c w hw) D hD).trans (HE ⟨i,hi⟩)

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridScan
