/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceFactories
public import LeanCanny.Encoding.CoordinateDoubleAffineTraceBounds
public import LeanCanny.Computation.ControllerRequests

/-! # Guarded lower-rank fixed-height slice requests

An accepted critical sample supplies the parent of its actual fixed-height
child. This controller emits the corresponding query in the same trace
family, rejects malformed samples, and retains no copy of an expanded source.
The query writer is charged in native polynomial space. Its output has one
polynomial bound in the original source size over all valid histories.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTraceHeightRequests
open LeanCanny.Algebra LeanCanny.Computation Turing.MultiTapeTM
open CoordinateDoubleAffineTrace
open scoped Classical

def frameGuard (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ) (q : List Bool) : Prop :=
  Valid P (seedCoordinate d old) (pairFst q) ∧
    coordinate (seedCoordinate d old) (pairFst q) < P.dim (base (pairFst q)) + 3

noncomputable def criticalInput (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) : SquareSampleInput.Inputs :=
  CoordinateDoubleAffineChildRecords.criticalInput (readers P) (depth d) (objective d old) (levels P d old level)

noncomputable def ready (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  {q | frameGuard P d old q ∧ q ∈ SquareSampleCompleteVertices.language (criticalInput P d old level)}

def samplePacket (q : List Bool) : List Bool := pair (pairFst q) (pairSnd q)

theorem samplePacket_FP : samplePacket ∈ FP := mem_FP_pair pairFst_mem_FP pairSnd_mem_FP

noncomputable def query (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (append false (pairFst q)) (heightFrameWord P d old level (samplePacket q))

noncomputable def program (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) : SingleCall.Program where
  request q := decide (q ∈ ready P d old level)
  query := query P d old level
  immediate _ := [false]
  finish := pairSnd

theorem frameGuard_fppred {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} (hd : UnaryFn d) (ho : UnaryFn old) :
    FPPred (frameGuard P d old) := by
  have hseed := seedCoordinate_unary hd ho
  exact ((valid_fppred hP hseed).comp pairFst_mem_FP).and
    (FPPred.lt ((coordinate_unary hseed).comp pairFst_mem_FP)
      (((hP.dim.comp pairFst_mem_FP).comp pairFst_mem_FP).add (UnaryFn.const 3)))

theorem criticalAccess {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    (criticalInput P d old level).Access :=
  FlatAffinePowerSampleInput.access
    (CoordinateDoubleAffinePrefix.access (readers_polyTime hP)
      ((depth_unary hd).add (UnaryFn.const 1)) (objective_unary hd ho)
      (levels_evaluator hP hd ho hl) (fun q => hA (base q)))
    (CoordinateDoubleAffinePrefix.coneCertificate (readers P)
      (fun q => depth d q + 1) (objective d old) (levels P d old level))

theorem ready_decider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceDecider (ready P d old level) := by
  have G := SpaceFunction.ofFP _ (frameGuard_fppred hP hd ho).flag_mem_FP
  have V := (SquareSampleCompleteVertices.decider (criticalAccess hP hd ho hl hA)).flagEvaluator
  apply (G.andFlags V).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [ready, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq]

theorem query_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceFunction (query P d old level) :=
  (SpaceFunction.ofFP _ (mem_FP_comp pairFst_mem_FP (append_FP false))).pairOutputs
    ((heightFrameWord_evaluator hP hd ho hl hA).precompose samplePacket samplePacket_FP)

/-- Every emitted parent label is accepted by the actual child sampler. -/
theorem query_valid (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hq : q ∈ ready P d old level) :
    SquareSampleCompleteVertices.Valid (sampleInput P d old level)
      (pairFst (query P d old level q)) (pairSnd (query P d old level q)) := by
  have hw : SquareSampleCompleteVertices.Valid (criticalInput P d old level)
      (pairFst q) (pairSnd q) := hq.2
  simpa only [query, samplePacket, pairFst_pair, pairSnd_pair] using
    heightFrameWord_valid P d old level (pairFst q) (pairSnd q) hq.1.1 hw

theorem certificates {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    (program P d old level).controller.Certificates
      (encQ := encBits) (encS := SingleCall.encState) := by
  have hr := (ready_decider hP hd ho hl hA).computable
  have hq := (query_evaluator hP hd ho hl hA).computable
  have hreq := hr.comp (.of_polyTime
    (ComputableTidilyInPolyTime.fst encBits (encPair encBool encBits)))
  have hnot := (ComputableTidilyInPolySpace.of_polyTime
    ComputableTidilyInPolyTime.bool_not).comp hreq
  constructor
  · change ComputableTidilyInPolySpace (fun q : List Bool => (q, false, [])) _ _
    fun_prop
  all_goals dsimp only [SingleCall.Program.controller, program, SingleCall.encState]
  all_goals fun_prop

theorem request_rank (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (q child : List Bool)
    (h : (program P d old level).controller.Requests answer budget q child) :
    base (pairFst child) = base (pairFst q) ∧
      Valid P (seedCoordinate d old) (pairFst child) ∧
      rank P (seedCoordinate d old) (pairFst child) <
        rank P (seedCoordinate d old) (pairFst q) := by
  obtain ⟨hr, rfl⟩ := ((program P d old level).requests_iff answer budget q child).mp h
  have hg : frameGuard P d old q := (of_decide_eq_true hr).1
  simp only [program, query, pairFst_pair]
  exact ⟨base_append false _, valid_append false P _ _ hg.2,
    rank_decreases false P _ _ hg.2⟩

theorem query_polynomial {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    ∃ r : Polynomial ℕ, ∀ u trace w,
      pair (frame u trace) w ∈ ready P d old level →
        (query P d old level (pair (frame u trace) w)).length ≤ r.eval u.length := by
  obtain ⟨r, hr⟩ := frame_length_polynomial hP (seedCoordinate d old)
  obtain ⟨v, hv⟩ := width_frame_polynomial hP hd ho hl hA
  refine ⟨2 * r + 2 + v, ?_⟩
  intro u trace w hready
  have hg : frameGuard P d old (pair (frame u trace) w) := hready.1
  have hsample : SquareSampleCompleteVertices.Valid (criticalInput P d old level) (frame u trace) w := by
    simpa only [SquareSampleCompleteVertices.language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair]
      using hready.2
  have hn : coordinate (seedCoordinate d old) (frame u trace) < P.dim u + 3 := by
    simpa only [frameGuard, pairFst_pair, base_frame] using hg.2
  have ha := valid_append false P (seedCoordinate d old) (frame u trace) (by simpa only [base_frame] using hn)
  have hword := heightFrameWord_valid P d old level (frame u trace) w
    (by simpa only [frameGuard, pairFst_pair] using hg.1) hsample
  have hlword := FlatAffineCompleteVertices.word_length (inputs P d old level) (cone P d old level)
    (append false (frame u trace)) _ hword
  have hf := hr u (trace ++ [false]) (by simpa only [append_frame] using ha)
  have hw := hv u (trace ++ [false]) (by simpa only [append_frame] using ha)
  rw [← append_frame false u trace] at hf hw
  rw [← hlword] at hw
  simp only [query, samplePacket, pairFst_pair, pairSnd_pair, pair_length, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat]
  omega

end LeanCanny.Encoding.CoordinateDoubleAffineTraceHeightRequests
