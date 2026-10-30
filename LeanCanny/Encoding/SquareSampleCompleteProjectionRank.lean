/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FiniteWordProjectionRank
public import LeanCanny.Encoding.SquareSampleCompleteCoordinateOrder

/-! # Native distinct coordinate ranks in filtered complete square samples

Any native subset of the complete labels may be used, while retaining its
original source context. Coordinate comparisons deduplicate projected values.
The semantic completeness promises supply no additional runtime readers.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteProjectionRank
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] SquareSampleCompleteCoordinateEquality.language SquareSampleCompleteCoordinateOrder.language

noncomputable def valueAt (F : Inputs) (context : List Bool → List Bool)
    (coordinate : (c : List Bool) → Fin (F.count (context c))) (c w : List Bool) : ℝ :=
  if hw : SquareSampleCompleteVertices.Valid F (context c) w then
    (SquareSampleCompleteVertices.candidate F (context c) w hw).val (coordinate c) else 0

def left (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def right (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd q))
theorem left_FP : left ∈ FP := by polytime [left]
theorem right_FP : right ∈ FP := by polytime [right]

def indexWord {F : Inputs} {context : List Bool → List Bool}
    (coordinate : (c : List Bool) → Fin (F.count (context c))) (c : List Bool) : List Bool := BinaryNatCode.encode (coordinate c).val

def query {F : Inputs} (context : List Bool → List Bool)
    (coordinate : (c : List Bool) → Fin (F.count (context c))) (q : List Bool) : List Bool :=
  pair (pair (context (pairFst q)) (pair (pairFst (pairSnd q)) (pairSnd (pairSnd q)))) (indexWord coordinate (pairFst q))

theorem query_FP {F : Inputs} {context : List Bool → List Bool} (hc : context ∈ FP)
    (coordinate : (c : List Bool) → Fin (F.count (context c))) (hi : UnaryFn (fun c => (coordinate c).val)) : query context coordinate ∈ FP := by
  have hI : indexWord coordinate ∈ FP := (BinaryFn.ofUnary hi).bits_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP hc)
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)))
    (mem_FP_comp pairFst_mem_FP hI)

theorem query_packet {F : Inputs} (context : List Bool → List Bool)
    (coordinate : (c : List Bool) → Fin (F.count (context c))) (c w v : List Bool) :
    query context coordinate (pair c (pair w v)) =
      pair (pair (context c) (pair w v)) (BinaryNatCode.encode (coordinate c).val) := by
  simp only [query, pairFst_pair, pairSnd_pair]
  rfl

noncomputable def nativeComparison (ordered : Bool) (F : Inputs) : Language :=
  if ordered then SquareSampleCompleteCoordinateOrder.language F else SquareSampleCompleteCoordinateEquality.language F

noncomputable def comparison (ordered : Bool) (F : Inputs) (context : List Bool → List Bool)
    (coordinate : (c : List Bool) → Fin (F.count (context c))) (allowed : Language) : Language :=
  {q | left q ∈ allowed ∧ right q ∈ allowed ∧ query context coordinate q ∈ nativeComparison ordered F}

theorem comparisonDecider {F : Inputs} (h : F.Access) {context : List Bool → List Bool} (hc : context ∈ FP)
    (coordinate : (c : List Bool) → Fin (F.count (context c))) (hi : UnaryFn (fun c => (coordinate c).val))
    {allowed : Language} (A : SpaceDecider allowed) (ordered : Bool) : SpaceDecider (comparison ordered F context coordinate allowed) := by
  have C : SpaceDecider (nativeComparison ordered F) := by
    cases ordered
    · exact SquareSampleCompleteCoordinateEquality.decider h
    · exact SquareSampleCompleteCoordinateOrder.decider h
  have L := (A.precompose left left_FP).flagEvaluator
  have R := (A.precompose right right_FP).flagEvaluator
  have Q := (C.precompose (query context coordinate) (query_FP hc coordinate hi)).flagEvaluator
  apply (L.andFlags (R.andFlags Q)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [comparison, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem comparison_packet (ordered : Bool) (F : Inputs) (hF : SquareSampleComplete.Complete F)
    (context : List Bool → List Bool) (coordinate : (c : List Bool) → Fin (F.count (context c))) (allowed : Language)
    (good : ∀ c w, pair c w ∈ allowed → SquareSampleCompleteVertices.Valid F (context c) w) (c w v : List Bool) :
    pair c (pair w v) ∈ comparison ordered F context coordinate allowed ↔
      pair c w ∈ allowed ∧ pair c v ∈ allowed ∧
        (if ordered then valueAt F context coordinate c w < valueAt F context coordinate c v
          else valueAt F context coordinate c w = valueAt F context coordinate c v) := by
  simp only [comparison, Set.mem_ofPred_eq, left, right, pairFst_pair, pairSnd_pair, query_packet]
  have H (hw : pair c w ∈ allowed) (hv : pair c v ∈ allowed) :
      pair (pair (context c) (pair w v)) (BinaryNatCode.encode (coordinate c).val) ∈ nativeComparison ordered F ↔
        (if ordered then valueAt F context coordinate c w < valueAt F context coordinate c v
          else valueAt F context coordinate c w = valueAt F context coordinate c v) := by
    have hw' := good c w hw
    have hv' := good c v hv
    have hW : valueAt F context coordinate c w = (SquareSampleCompleteVertices.candidate F (context c) w hw').val (coordinate c) :=
      dite_eq_left hw'
    have hV : valueAt F context coordinate c v = (SquareSampleCompleteVertices.candidate F (context c) v hv').val (coordinate c) :=
      dite_eq_left hv'
    rw [hW, hV]
    cases ordered
    · exact SquareSampleCompleteCoordinateEquality.packet F hF (context c) w v hw' hv' (coordinate c)
    · unfold nativeComparison
      rw [ite_eq_left rfl]
      unfold SquareSampleCompleteCoordinateOrder.language
      simp only [Set.mem_ofPred_eq, SquareSampleCompleteCoordinateEquality.source, SquareSampleCompleteCoordinateEquality.word,
        pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false, ite_true, hw', hv', true_and,
        SquareSampleCompleteCoordinateOrder.packet F hF (context c) w v hw' hv' (coordinate c),
        List.cons.injEq, and_true, decide_eq_true_eq]
  exact ⟨fun ⟨hw, hv, he⟩ => ⟨hw, hv, (H hw hv).mp he⟩,
    fun ⟨hw, hv, he⟩ => ⟨hw, hv, (H hw hv).mpr he⟩⟩

noncomputable def data (F : Inputs) (hF : SquareSampleComplete.Complete F)
    (context : List Bool → List Bool) (coordinate : (c : List Bool) → Fin (F.count (context c))) (allowed : Language)
    (good : ∀ c w, pair c w ∈ allowed → SquareSampleCompleteVertices.Valid F (context c) w) : FiniteWordProjectionRank.Data where
  width c := SquareSampleCompleteVertices.width F (context c)
  valid := allowed
  value := valueAt F context coordinate
  equal := comparison false F context coordinate allowed
  less := comparison true F context coordinate allowed
  valid_length c w hw := (Classical.choose (good c w hw)).1
  equal_iff c w v := comparison_packet false F hF context coordinate allowed good c w v
  less_iff c w v := comparison_packet true F hF context coordinate allowed good c w v

theorem access {F : Inputs} (h : F.Access) (hF : SquareSampleComplete.Complete F)
    {context : List Bool → List Bool} (hc : context ∈ FP)
    (coordinate : (c : List Bool) → Fin (F.count (context c))) (hi : UnaryFn (fun c => (coordinate c).val))
    {allowed : Language} (A : SpaceDecider allowed)
    (good : ∀ c w, pair c w ∈ allowed → SquareSampleCompleteVertices.Valid F (context c) w) :
    (data F hF context coordinate allowed good).Access :=
  ⟨(SquareSampleCompleteVertices.width_unary h).comp hc, A,
    comparisonDecider h hc coordinate hi A false, comparisonDecider h hc coordinate hi A true⟩

theorem rankEvaluator {F : Inputs} (h : F.Access) (hF : SquareSampleComplete.Complete F)
    {context : List Bool → List Bool} (hc : context ∈ FP)
    (coordinate : (c : List Bool) → Fin (F.count (context c))) (hi : UnaryFn (fun c => (coordinate c).val))
    {allowed : Language} (A : SpaceDecider allowed)
    (good : ∀ c w, pair c w ∈ allowed → SquareSampleCompleteVertices.Valid F (context c) w) :
    SpaceFunction (fun q => BinaryNatCode.encode (FiniteWordProjectionRank.rank (data F hF context coordinate allowed good) q)) :=
  FiniteWordProjectionRank.evaluator (access h hF hc coordinate hi A good)

end LeanCanny.Encoding.SquareSampleCompleteProjectionRank
