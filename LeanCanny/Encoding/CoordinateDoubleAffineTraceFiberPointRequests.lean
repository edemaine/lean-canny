/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceHeightRequests
public import LeanCanny.Encoding.CoordinateDoubleAffineCriticalFiberPairs

/-! # Lower-rank point-pair queries in an actual common-height fiber

A native shared-parent and height-equality guard validates a pair of critical
points. The paired child retains both complete points. Its query stores one
child parent word and two original stage references, without requiring the
points to be critical for the next coordinate objective.

This query kind still needs dispatch in the complete recursive connection
algorithm. Its local writer, validity, rank, and original-source size bounds
do not assume an endpoint-connection oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTraceFiberPointRequests
open LeanCanny.Algebra LeanCanny.Computation Turing.MultiTapeTM
open CoordinateDoubleAffineTrace
open CoordinateDoubleAffineTraceHeightRequests (frameGuard frameGuard_fppred samplePacket samplePacket_FP)
open scoped Classical

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def parent (q : List Bool) : List Bool := pairSnd (pairFst q)
def reference (right : Bool) (q : List Bool) : ℕ :=
  Nat.fromBitsLE (if right then pairSnd (pairSnd q) else pairFst (pairSnd q))

def references (d : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (BinaryNatCode.encode (d q)) (BinaryNatCode.encode (d q + 1))

theorem references_FP {d : List Bool → ℕ} (hd : UnaryFn d) : references d ∈ FP :=
  mem_FP_pair (BinaryFn.ofUnary hd).bits_mem_FP
    (BinaryFn.ofUnary (hd.add (UnaryFn.const 1))).bits_mem_FP

noncomputable def ready (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  {q | frameGuard P d old q ∧
    samplePacket q ∈ CoordinateDoubleAffineCriticalPairs.sharedLanguage (readers P) (depth d)
      (objective d old) (levels P d old level) ∧
    samplePacket q ∈ CoordinateDoubleAffineCriticalFiberPairs.language (readers P) (depth d)
      (objective d old) (levels P d old level)}

noncomputable def query (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (append true (pairFst q)) (midpointFrameWord P d old level (samplePacket q)))
    (references (depth d) (pairFst q))

noncomputable def program (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) : SingleCall.Program where
  request q := decide (q ∈ ready P d old level)
  query := query P d old level
  immediate _ := [false]
  finish := pairSnd

theorem ready_decider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceDecider (ready P d old level) := by
  have G := SpaceFunction.ofFP _ (frameGuard_fppred hP hd ho).flag_mem_FP
  have S := ((CoordinateDoubleAffineCriticalPairs.sharedDecider (readers_polyTime hP)
    (depth_unary hd) (objective_unary hd ho) (levels_evaluator hP hd ho hl)
    (fun q => hA (base q))).precompose samplePacket samplePacket_FP).flagEvaluator
  have E := ((CoordinateDoubleAffineCriticalFiberPairs.decider (readers_polyTime hP)
    (depth_unary hd) (objective_unary hd ho) (levels_evaluator hP hd ho hl)
    (fun q => hA (base q))).precompose samplePacket samplePacket_FP).flagEvaluator
  apply (G.andFlags (S.andFlags E)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [ready, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem query_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceFunction (query P d old level) :=
  ((SpaceFunction.ofFP _ (mem_FP_comp pairFst_mem_FP (append_FP true))).pairOutputs
    ((midpointFrameWord_evaluator hP hd ho hl hA).precompose samplePacket samplePacket_FP)).pairOutputs
      (SpaceFunction.ofFP _ (mem_FP_comp pairFst_mem_FP (references_FP (depth_unary hd))))

theorem query_parent_valid (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hq : q ∈ ready P d old level) :
    SquareSampleCompleteVertices.Valid (sampleInput P d old level)
      (source (query P d old level q)) (parent (query P d old level q)) := by
  have hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineCriticalPairs.input (readers P) (depth d) (objective d old) (levels P d old level))
      (pairFst q) (pairSnd q) := by
    simpa only [CoordinateDoubleAffineCriticalPairs.sharedLanguage, SquareSampleCompleteVertices.language,
      Set.mem_ofPred_eq, samplePacket, pairFst_pair, pairSnd_pair] using hq.2.1.1
  simpa only [query, source, parent, samplePacket, pairFst_pair, pairSnd_pair] using
    midpointFrameWord_valid P d old level (pairFst q) (pairSnd q) hq.1.1 hw hq.2.1

theorem query_references (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) :
    reference false (query P d old level q) = depth d (pairFst q) ∧
      reference true (query P d old level q) = depth d (pairFst q) + 1 := by
  simp only [reference, query, references, pairFst_pair, pairSnd_pair, Bool.false_eq_true,
    ite_false, ite_true, BinaryNatCode.encode, Nat.fromBitsLE_bits, and_self]

theorem query_references_lt (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (right : Bool) :
    reference right (query P d old level q) < depth d (source (query P d old level q)) := by
  have h := query_references P d old level q
  have hs : source (query P d old level q) = append true (pairFst q) := by
    simp only [source, query, pairFst_pair]
  rw [hs, depth_append]
  cases right
  · rw [h.1]
    change depth d (pairFst q) < depth d (pairFst q) + 2
    omega
  · rw [h.2]
    change depth d (pairFst q) + 1 < depth d (pairFst q) + 2
    omega

theorem certificates {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    (program P d old level).controller.Certificates
      (encQ := encBits) (encS := SingleCall.encState) := by
  have hr := (ready_decider hP hd ho hl hA).computable
  have hq := (query_evaluator hP hd ho hl hA).computable
  have hreq := hr.comp (.of_tidyPolyTime
    (ComputableTidilyInPolyTime.fst encBits (encPair encBool encBits)))
  have hnot := (ComputableInPolySpace.of_tidyPolyTime
    ComputableTidilyInPolyTime.bool_not).comp hreq
  constructor
  · change ComputableInPolySpace (fun q : List Bool => (q, false, [])) _ _
    fun_prop
  all_goals dsimp only [SingleCall.Program.controller, program, SingleCall.encState]
  all_goals fun_prop

theorem request_rank (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (q child : List Bool)
    (h : (program P d old level).controller.Requests answer budget q child) :
    base (source child) = base (pairFst q) ∧
      Valid P (seedCoordinate d old) (source child) ∧
      rank P (seedCoordinate d old) (source child) < rank P (seedCoordinate d old) (pairFst q) := by
  obtain ⟨hr, rfl⟩ := ((program P d old level).requests_iff answer budget q child).mp h
  have hg : frameGuard P d old q := (of_decide_eq_true hr).1
  simp only [program, query, source, pairFst_pair]
  exact ⟨base_append true _, valid_append true P _ _ hg.2,
    rank_decreases true P _ _ hg.2⟩

theorem query_polynomial {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    ∃ r : Polynomial ℕ, ∀ u trace w,
      pair (frame u trace) w ∈ ready P d old level →
        (query P d old level (pair (frame u trace) w)).length ≤ r.eval u.length := by
  obtain ⟨r, hr⟩ := frame_length_polynomial hP (seedCoordinate d old)
  obtain ⟨v, hv⟩ := width_frame_polynomial hP hd ho hl hA
  obtain ⟨t, ht⟩ := output_length_poly_of_mem_FP (references_FP (depth_unary hd))
  refine ⟨4 * r + 2 * v + t.comp r + 6, ?_⟩
  intro u trace w hready
  have hg := hready.1
  have hvalid : Valid P (seedCoordinate d old) (frame u trace) := by
    simpa only [frameGuard, pairFst_pair] using hg.1
  have ha := valid_append true P (seedCoordinate d old) (frame u trace)
    (by simpa only [frameGuard, pairFst_pair] using hg.2)
  have hpv := query_parent_valid P d old level (pair (frame u trace) w) hready
  simp only [source, parent, query, samplePacket, pairFst_pair, pairSnd_pair] at hpv
  have hlword := FlatAffineCompleteVertices.word_length (inputs P d old level) (cone P d old level)
    (append true (frame u trace)) _ hpv
  have hf := hr u (trace ++ [true]) (by simpa only [append_frame] using ha)
  have hw := hv u (trace ++ [true]) (by simpa only [append_frame] using ha)
  rw [← append_frame true u trace] at hf hw
  rw [← hlword] at hw
  have href := (ht (frame u trace)).trans (t.eval_mono (hr u trace hvalid))
  rw [← Polynomial.eval_comp] at href
  simp only [query, samplePacket, pairFst_pair, pairSnd_pair, pair_length,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  omega

end LeanCanny.Encoding.CoordinateDoubleAffineTraceFiberPointRequests
