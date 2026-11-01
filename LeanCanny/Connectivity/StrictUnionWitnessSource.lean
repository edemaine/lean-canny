/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.StrictUnionWitnessSemantics
public import LeanCanny.Encoding.StrictUnionWitnessWriter
public import LeanCanny.Connectivity.ClosedFormulaGateLanguages
/-! # The actual native strict-union source is its component-preserving closed witness -/
@[expose] public section
namespace LeanCanny.Connectivity.StrictUnionWitnessSource
open ETR Set LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open MonotoneGateSource StrictUnionWitnessFormula
open scoped Classical

noncomputable def terms (F : Family) (c : List Bool) (i : Fin (F.count c)) : Term :=
  F.atom (pair c (List.replicate i.val true))

theorem condition_pair (F : Family) (c : List Bool) (i : Fin (F.count c)) :
    StrictUnionWitnessWriter.condition F (pair c (List.replicate i.val true))=
      atomFormula (F.dimension c) (F.count c) (terms F c) i := by
  simp only [StrictUnionWitnessWriter.condition,StrictUnionWitnessWriter.equation,
    StrictUnionWitnessWriter.weightVariable,StrictUnionWitnessWriter.circleVariable,
    atomFormula,atomEquation,squares,weightIndex,circleIndex,terms,dimension,count,index,
    pairFst_pair,pairSnd_pair,List.length_replicate]

theorem source_eq (F : Family) (c : List Bool) : StrictUnionWitnessWriter.source F c=
    lifted (F.dimension c) (F.count c) (terms F c) := by
  have HE : (List.range (F.count c)).map (fun i => StrictUnionWitnessWriter.condition F (pair c (List.replicate i true)))=
      List.ofFn (atomFormula (F.dimension c) (F.count c) (terms F c)) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn]
    · intro i hL hR
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      exact condition_pair F c ⟨i,by simpa only [List.length_ofFn] using hR⟩
  simp only [StrictUnionWitnessWriter.source,lifted,FormulaConjunctionWriter.rangeConjunction,HE]

noncomputable def description (F : Family) (c : List Bool) : Description :=
  ⟨(F.dimension c+F.count c)+2*F.count c,StrictUnionWitnessWriter.source F c⟩

theorem source_closed (F : Family) (c : List Bool) :
    ClosedFormulaWitness.Closed (description F c).formula := by
  rw [description,source_eq]
  exact lifted_closed _ _ _

theorem description_wellFormed (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (description F c).WellFormed := by
  change (StrictUnionWitnessWriter.source F c).arity≤_
  rw [source_eq]
  exact lifted_scope _ _ _ (fun i => ha i.val i.isLt)

theorem description_dim_unary (F : Family) (hF : Access F) : UnaryFn (fun c => (description F c).dimension) :=
  (hF.dimension.add hF.count).add ((UnaryFn.const 2).mul hF.count)

theorem whole_record_FP (F : Family) (hF : Access F) :
    (fun c => (Input.whole (description F c)).encode) ∈ FP := by
  have H := Codec.taggedTwo_mem_FP 1 (Codec.unary_toBits_mem_FP (description_dim_unary F hF))
    (StrictUnionWitnessWriter.source_FP F hF)
  apply mem_FP_of_eq H
  intro c
  exact Codec.taggedTwo_toBits 1 _ _

private theorem disjunction_scope (ps : List Formula) (N : ℕ) (h : ∀ p∈ps,p.arity≤N) :
    (ps.foldr Formula.or .falsum).arity≤N := by
  induction ps with
  | nil => exact Nat.zero_le _
  | cons p ps IH => exact max_le (h p List.mem_cons_self) (IH (fun q hq => h q (List.mem_cons_of_mem p hq)))

theorem original_wellFormed (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (originalDescription (F.dimension c) (F.count c) (terms F c)).WellFormed := by
  apply disjunction_scope
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  simpa only [Formula.arity,Term.arity,Nat.zero_max,terms,originalDescription] using ha i.val i.isLt

theorem connected_iff (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (description F c).Connected ↔ (originalDescription (F.dimension c) (F.count c) (terms F c)).Connected := by
  have HL := description_wellFormed F c ha
  have HO := original_wellFormed F c ha
  simp only [Description.Connected,HL,HO,true_and]
  have HE : description F c=liftedDescription (F.dimension c) (F.count c) (terms F c) := by
    unfold description liftedDescription
    rw [source_eq]
  rw [HE]
  exact lifted_preconnected_iff _ _ _ (fun i => ha i.val i.isLt)

noncomputable def equationWriter (F : Family) (c : List Bool) : List Bool :=
  ClosedFormulaGateTruth.wholeWriter (Input.whole (description F c)).encode

theorem equationWriter_FP (F : Family) (hF : Access F) : equationWriter F ∈ FP :=
  mem_FP_comp (whole_record_FP F hF) ClosedFormulaGateTruth.wholeWriter_FP

theorem equation_language_iff (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    equationWriter F c∈connectedLanguage ↔
      (Input.whole (originalDescription (F.dimension c) (F.count c) (terms F c))).encode∈connectedLanguage := by
  rw [equationWriter,ClosedFormulaGateTruth.canonical_whole_language_iff _ (source_closed F c) (description_wellFormed F c ha)]
  simpa only [whole_encode_mem_iff] using connected_iff F c ha

end LeanCanny.Connectivity.StrictUnionWitnessSource
