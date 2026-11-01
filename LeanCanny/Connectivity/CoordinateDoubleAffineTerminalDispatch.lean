/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CoordinateDoubleAffineRetainedTerminalTrace
public import LeanCanny.Computation.PSPACEBoolean

/-! # Tagged native terminal queries for fresh and retained point labels

Tag `false` uses the existing two-child-label terminal API. Tag `true` uses
two retained-stage references and its actual terminal-child membership
search. The payload layouts remain distinct. This is a native rank-zero
leaf; nonterminal recursive graph assembly remains a separate obligation.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateDoubleAffineTerminalDispatch
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM
open scoped Classical

def pack (retained : Bool) (q : List Bool) : List Bool := retained :: q
def payload (q : List Bool) : List Bool := q.drop 1
def kind (retained : Bool) (q : List Bool) : Prop := q.take 1 = [retained]
def source (q : List Bool) : List Bool := FlatAffineRetainedPointChildMatch.source (payload q)

theorem pack_FP (retained : Bool) : pack retained ∈ FP := cons_mem_FP retained
theorem payload_FP : payload ∈ FP := drop_mem_FP id_mem_FP (UnaryFn.const 1)
theorem kind_fppred (retained : Bool) : FPPred (kind retained) :=
  Brackets.stringEq_fppred (take_mem_FP id_mem_FP (UnaryFn.const 1)) (constFn_mem_FP [retained])
theorem source_FP : source ∈ FP := mem_FP_comp payload_FP FlatAffineRetainedPointChildMatch.source_FP

@[simp] theorem payload_pack (retained : Bool) (q : List Bool) : payload (pack retained q) = q := rfl
@[simp] theorem pack_length (retained : Bool) (q : List Bool) : (pack retained q).length = q.length + 1 := by
  simp only [pack, List.length_cons]
theorem source_pack (retained : Bool) (q : List Bool) :
    source (pack retained q) = FlatAffineRetainedPointChildMatch.source q := rfl

noncomputable def language (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  {q | (kind false q ∧ payload q ∈ CoordinateDoubleAffineTerminalReachability.language P depth objective level) ∨
    (kind true q ∧ payload q ∈ CoordinateDoubleAffineRetainedTerminalReachability.language P depth objective level)}

private theorem guarded {L : Language} {p : List Bool → Prop}
    (hp : FPPred p) (D : SpaceDecider L) : SpaceDecider {q | p q ∧ q ∈ L} := by
  have G := SpaceFunction.ofFP _ hp.flag_mem_FP
  apply (G.andFlags D.flagEvaluator).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq]

theorem decider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceDecider (language P depth objective level) := by
  have F := guarded (kind_fppred false)
    ((CoordinateDoubleAffineTerminalReachability.decider hP hd ho hl hA).precompose payload payload_FP)
  have R := guarded (kind_fppred true)
    ((CoordinateDoubleAffineRetainedTerminalReachability.decider hP hd ho hl hA).precompose payload payload_FP)
  exact (F.union R).congr (Set.ext fun _ => Iff.rfl)

theorem fresh_iff (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) :
    pack false q ∈ language P depth objective level ↔
      q ∈ CoordinateDoubleAffineTerminalReachability.language P depth objective level := by
  simp [language, kind, pack, payload]

theorem retained_iff (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) :
    pack true q ∈ language P depth objective level ↔
      q ∈ CoordinateDoubleAffineRetainedTerminalReachability.language P depth objective level := by
  simp [language, kind, pack, payload]

def rank (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ) (q : List Bool) : ℕ :=
  P.dim (source q) + 3 - objective (FlatAffineFullSourceTower.stage (source q) (depth (source q)))

theorem rank_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} (hd : UnaryFn depth) (ho : UnaryFn objective) : UnaryFn (rank P depth objective) := by
  have S : (fun q => FlatAffineFullSourceTower.stage (source q) (depth (source q))) ∈ FP :=
    mem_FP_pair source_FP (BinaryFn.ofUnary (hd.comp source_FP)).bits_mem_FP
  exact ((hP.dim.comp source_FP).add (UnaryFn.const 3)).sub (ho.comp S)

theorem rank_zero_of_mem (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) {q : List Bool} (hq : q ∈ language P depth objective level) :
    rank P depth objective q = 0 := by
  have ht : CoordinateDoubleAffineTerminalReachability.terminal P depth objective (payload q) := by
    rcases hq with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h.1
  exact Nat.sub_eq_zero_of_le ht

theorem trace_rank (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (q : List Bool) : rank (CoordinateDoubleAffineTrace.readers P) (CoordinateDoubleAffineTrace.depth d)
      (CoordinateDoubleAffineTrace.objective d old) q =
      CoordinateDoubleAffineTrace.rank P (CoordinateDoubleAffineTrace.seedCoordinate d old) (source q) := by
  unfold rank
  rw [CoordinateDoubleAffineTrace.objective_current]
  rfl

theorem tagged_query_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceFunction (fun q => pack true (CoordinateDoubleAffineTraceFiberPointRequests.query P d old level q)) :=
  (CoordinateDoubleAffineTraceFiberPointRequests.query_evaluator hP hd ho hl hA).postcompose
    (pack true) (pack_FP true)

theorem tagged_request_rank (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (q child : List Bool)
    (h : (CoordinateDoubleAffineTraceFiberPointRequests.program P d old level).controller.Requests
      answer budget q child) :
    rank (CoordinateDoubleAffineTrace.readers P) (CoordinateDoubleAffineTrace.depth d)
      (CoordinateDoubleAffineTrace.objective d old) (pack true child) <
        CoordinateDoubleAffineTrace.rank P (CoordinateDoubleAffineTrace.seedCoordinate d old) (LeanCanny.pairFst q) := by
  have H := CoordinateDoubleAffineTraceFiberPointRequests.request_rank P d old level answer budget q child h
  rw [trace_rank, source_pack]
  exact H.2.2

noncomputable def program (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : SingleCall.Program where
  request _ := false
  query := id
  immediate q := [decide (q ∈ language P depth objective level)]
  finish := LeanCanny.pairSnd

theorem certificates {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    (program P depth objective level).controller.Certificates
      (encQ := encBits) (encS := SingleCall.encState) :=
  (program P depth objective level).certificates_of_space (constFn_mem_FP [false]) id_mem_FP
    (decider hP hd ho hl hA).flagEvaluator.computable (.of_polyTime pairSnd_mem_FP)

theorem no_requests (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (answer : List Bool → List Bool) (budget : List Bool → ℕ)
    (q child : List Bool) : ¬ (program P depth objective level).controller.Requests answer budget q child := by
  intro h
  have hr := ((program P depth objective level).requests_iff answer budget q child).mp h
  exact Bool.false_ne_true hr.1

theorem tagged_query_polynomial {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    ∃ r : Polynomial ℕ, ∀ u trace w,
      LeanCanny.pair (CoordinateDoubleAffineTrace.frame u trace) w ∈
        CoordinateDoubleAffineTraceFiberPointRequests.ready P d old level →
      (pack true (CoordinateDoubleAffineTraceFiberPointRequests.query P d old level
        (LeanCanny.pair (CoordinateDoubleAffineTrace.frame u trace) w))).length ≤ r.eval u.length := by
  obtain ⟨r, hr⟩ := CoordinateDoubleAffineTraceFiberPointRequests.query_polynomial hP hd ho hl hA
  refine ⟨r + 1, ?_⟩
  intro u trace w hq
  simp only [pack_length, Polynomial.eval_add, Polynomial.eval_one]
  exact Nat.add_le_add_right (hr u trace w hq) 1

end LeanCanny.Connectivity.CoordinateDoubleAffineTerminalDispatch
