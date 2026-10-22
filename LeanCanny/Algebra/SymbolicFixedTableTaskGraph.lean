/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableTreeSource
public import LeanCanny.Algebra.BerkowitzTaskReachability
public import LeanCanny.Algebra.BerkowitzTaskMetadata
public import LeanCanny.Algebra.CannyBalancedTaskAddresses
public import LeanCanny.Algebra.SymbolicFixedTableInputEnvelope

/-! # Reachability and source address bounds for symbolic table coefficients -/

@[expose] public section
set_option maxRecDepth 256
namespace LeanCanny.Computation.SingleCall.Program
theorem query_context_iterate (P : SingleCall.Program) (answer : List Bool → List Bool) (p : List Bool) (t : ℕ) :
    P.controller.query ((P.controller.reference answer)^[t] (P.controller.initial p)) = P.query p := by
  change P.query (((P.controller.reference answer)^[t] (SingleCall.Program.initial p)).1) = _
  rw [P.context_iterate]
end LeanCanny.Computation.SingleCall.Program

namespace LeanCanny.Algebra.SymbolicFixedTableTreeSource
open LeanCanny.Encoding LeanCanny.Computation
open Polynomial SymbolicScaledSquarefree SymbolicFixedTableEntryBits
open SymbolicFixedTableTaskRouting BerkowitzPolynomial.TaskDispatch

variable (L : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
  (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)

noncomputable def tasks : List Bool → List Bool → Prop :=
  Reachable (access L E hL) (program L E hL).controller (fun _ => 1)

theorem tasks_root (q : List Bool) : tasks L E hL q q := .refl

theorem tasks_closed : QueriesClosed (access L E hL) (program L E hL).controller (fun _ => 1) (tasks L E hL) :=
  reachable_closed _ _ _

theorem tasks_ranked : RankedQueries (access L E hL) (program L E hL).controller (fun _ => 1)
    (tasks L E hL) (levelRank level) :=
  ranked_queries_of_source_levels _ _ _ _ _ (tasks_closed L E hL) (source_levels L E hL _)

theorem reachable_rank_bound (root q : List Bool) (hq : tasks L E hL root q) :
    levelRank level q ≤ 5 * root.length + 4 :=
  (reachable_rank_le _ _ _ _ (tasks_ranked L E hL) root q hq).trans
    (levelRank_le level root root.length (origin_level_le_length root))

theorem reachable_level_bound (root q : List Bool) (hq : tasks L E hL root q) : level (origin q) ≤ root.length := by
  have hr := reachable_rank_bound L E hL root q hq
  cases q with
  | nil => simp only [origin_zero, level_zero]; exact Nat.zero_le _
  | cons b q =>
    have hz : isZero (b :: q) = false := rfl
    have hp := priority_pos (b :: q) hz
    simp only [levelRank, hz, Bool.false_eq_true, ite_false] at hr
    omega

theorem request_source (q child : List Bool)
    (h : Requests (access L E hL) (program L E hL).controller (fun _ => 1) q child)
    (hs : SelectedSource q) :
    isLeaf (pairFst (payload q)) = false ∧
    CannyResultantBits.RecursiveStage.request (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) (payload q)) = true ∧
    child = if CannyResultantBits.RecursiveStage.selectRight (source L).access
        (sourceInput (fun q => BinaryNatCode.encode (radix E q)) (payload q)) then
      coefficientTask true (CannyResultantBits.RecursiveStage.rightQuery
        (sourceInput (fun q => BinaryNatCode.encode (radix E q)) (payload q)))
      else coefficientTask false (CannyResultantBits.RecursiveStage.leftQuery (source L).access
        (sourceInput (fun q => BinaryNatCode.encode (radix E q)) (payload q))) := by
  obtain ⟨t, _, _, hn, he⟩ := h
  obtain ⟨hz, hd, hf, hm⟩ := hs
  rw [needs_iterate] at hn
  simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false] at hn
  change (program L E hL).request
    ((((program L E hL).controller.reference (answer (access L E hL)))^[t]
      (SingleCall.Program.initial (payload q))).1) = true at hn
  rw [SingleCall.Program.context_iterate] at hn
  have hl := SymbolicFixedTableMixedSource.request_nonleaf (source L) _ _ _ (payload q) hn
  have hh : high E (pairFst (payload q)) = false := by
    cases hh : high E (pairFst (payload q)) with
    | false => rfl
    | true =>
      have hf : false = true := by
        simpa only [program, SymbolicFixedTableMixedSource.program, SingleCall.Program.withLeaf,
          SymbolicFixedTableMixedSource.entrySelect, hh, ite_true] using hn
      cases hf
  refine ⟨hl, ?_, ?_⟩
  · simpa only [program, SymbolicFixedTableMixedSource.program, SingleCall.Program.withLeaf,
      SymbolicFixedTableMixedSource.entrySelect, hh, hl, Bool.false_eq_true, ite_false,
      Family.sourceProgram, SingleCall.Program.reindex, CannyResultantBits.RecursiveStage.program] using hn
  · rw [he, query_iterate]
    simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false]
    rw [SingleCall.Program.query_context_iterate]
    exact SymbolicFixedTableMixedSource.query_eq _ _ _ _ _

theorem request_measure_le (measure : List Bool → ℕ) (hz : ∀ c, measure [] ≤ measure c)
    (hl : ∀ p, isLeaf (pairFst p) = false → measure (origin (coefficientTask false
      (CannyResultantBits.RecursiveStage.leftQuery (source L).access
        (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))) ≤ measure (pairFst p))
    (hr : ∀ p, isLeaf (pairFst p) = false → measure (origin (coefficientTask true
      (CannyResultantBits.RecursiveStage.rightQuery
        (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))) ≤ measure (pairFst p))
    (q child : List Bool)
    (h : Requests (access L E hL) (program L E hL).controller (fun _ => 1) q child) :
    measure (origin child) ≤ measure (origin q) := by
  by_cases hs : SelectedSource q
  · obtain ⟨hn, _, he⟩ := request_source L E hL q child h hs
    obtain ⟨hz, hd, hf, hm⟩ := hs
    have ho : origin q = pairFst (payload q) := by
      simp only [origin, hz, hd, hf, hm, Bool.false_eq_true, ite_false]
    rw [ho, he]
    split_ifs
    · exact hr _ hn
    · exact hl _ hn
  · obtain ⟨t, _, _, hn, he⟩ := h
    rcases internal_query_origin _ _ _ q t hn hs with he0 | heo
    · rw [he, he0, origin_zero]
      exact hz _
    · rw [he, heo]

theorem reachable_measure_le (measure : List Bool → ℕ) (hz : ∀ c, measure [] ≤ measure c)
    (hl : ∀ p, isLeaf (pairFst p) = false → measure (origin (coefficientTask false
      (CannyResultantBits.RecursiveStage.leftQuery (source L).access
        (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))) ≤ measure (pairFst p))
    (hr : ∀ p, isLeaf (pairFst p) = false → measure (origin (coefficientTask true
      (CannyResultantBits.RecursiveStage.rightQuery
        (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))) ≤ measure (pairFst p))
    (root q : List Bool) (hq : tasks L E hL root q) : measure (origin q) ≤ measure (origin root) := by
  change Relation.ReflTransGen _ root q at hq
  induction hq with
  | refl => exact le_refl _
  | @tail q child _ hstep ih => exact (request_measure_le L E hL measure hz hl hr q child hstep).trans ih

theorem leftQuery_node (p : List Bool) :
    nodeContext (origin (coefficientTask false (CannyResultantBits.RecursiveStage.leftQuery (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))) =
      BalancedParameterContext.child false (nodeContext (pairFst p)) := by
  simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket,
    nodeContext, pairFst_pair]
  rw [← nodeContext, sourceNode_leftQuery]

theorem rightQuery_node (p : List Bool) :
    nodeContext (origin (coefficientTask true (CannyResultantBits.RecursiveStage.rightQuery
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))) =
      BalancedParameterContext.child true (nodeContext (pairFst p)) := by
  simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket,
    nodeContext, pairFst_pair]
  rw [← nodeContext, sourceNode_rightQuery]

theorem reachable_node_length_le (root q : List Bool) (hq : tasks L E hL root q) :
    (nodeContext (origin q)).length ≤ 5 * root.length + 4 := by
  have hm := reachable_measure_le L E hL (fun c => BalancedParameterContext.footprint (nodeContext c))
    (fun c => by apply BalancedParameterContext.footprint_ge_four)
    (fun p hh => by rw [leftQuery_node]; exact BalancedParameterContext.child_footprint_le _ _ ((isLeaf_false_iff _).mp hh))
    (fun p hh => by rw [rightQuery_node]; exact BalancedParameterContext.child_footprint_le _ _ ((isLeaf_false_iff _).mp hh))
    root q hq
  have hp : (nodeContext (origin q)).length ≤ BalancedParameterContext.footprint (nodeContext (origin q)) := Nat.le_max_left _ _
  have hr : (nodeContext (origin root)).length ≤ root.length :=
    ((pairFst_length_le _).trans (pairFst_length_le _)).trans (origin_length_le root)
  exact (hp.trans hm).trans ((BalancedParameterContext.footprint_le _).trans (by omega))

end LeanCanny.Algebra.SymbolicFixedTableTreeSource
