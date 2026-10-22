/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyBalancedTaskRouting
public import LeanCanny.Algebra.BerkowitzTaskReachability
public import LeanCanny.Algebra.BerkowitzTaskMetadata

/-! # A common rank bound for the concrete balanced coefficient graph

Actual query reachability supplies closure. The unary address height and
internal stage priorities give rank at most `5*root.length+4` for every reachable
task, on all input words. Native FP controls supply the metadata bound. The
uniform reader below therefore needs only child semantics and quantitative
word/reply bounds, with no separate task closure, rank, or source-level hypotheses.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyBalancedTaskRouting
open LeanCanny.Encoding LeanCanny.Computation
open BerkowitzPolynomial.TaskDispatch

variable (L : SeparableBits.Family) {F : CannyResultantBits.Family} {leftOrder rightOrder : List Bool → ℕ}
  (a : CannyResultantBits.Access F leftOrder rightOrder)

def tasks : List Bool → List Bool → Prop :=
  Reachable (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf)
    (CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf (coefficientTask false) (coefficientTask true)).controller (fun _ => 1)

theorem tasks_root (q : List Bool) : tasks L a q q := .refl

theorem tasks_closed :
    QueriesClosed (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf)
      (CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf (coefficientTask false) (coefficientTask true)).controller
      (fun _ => 1) (tasks L a) := reachable_closed _ _ _

theorem tasks_ranked :
    RankedQueries (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf)
      (CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf (coefficientTask false) (coefficientTask true)).controller
      (fun _ => 1) (tasks L a) (levelRank level) :=
  ranked_queries_of_source_levels _ _ _ _ _ (tasks_closed L a) (source_levels L a (tasks L a))

theorem reachable_rank_bound (root q : List Bool) (hq : tasks L a root q) :
    levelRank level q ≤ 5 * root.length + 4 :=
  (reachable_rank_le _ _ _ _ (tasks_ranked L a) root q hq).trans
    (levelRank_le level root root.length (origin_level_le_length root))

theorem reachable_level_bound (root q : List Bool) (hq : tasks L a root q) : level (origin q) ≤ root.length := by
  have hr := reachable_rank_bound L a root q hq
  cases q with
  | nil => simp only [origin_zero, level_zero]; exact Nat.zero_le _
  | cons b q =>
    have hz : isZero (b :: q) = false := rfl
    have hp := priority_pos (b :: q) hz
    simp only [levelRank, hz, Bool.false_eq_true, ite_false] at hr
    omega

theorem rankBound_unary : UnaryFn (fun root : List Bool => 5 * root.length + 4) :=
  ((UnaryFn.const 5).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 4)

/-- The concrete balanced address routing supplies task closure and every
rank/level bound. FP controls supply the common metadata bound. Child semantic
identities and word/reply bounds remain explicit, as do the original leaf readers. -/
theorem evaluator (A : SeparableBits.Readers L) (ha : a.ControlsPolyTime)
    (hl : ∀ p, answer (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf) (coefficientTask false p) = a.leftCoefficient p)
    (hr : ∀ p, answer (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf) (coefficientTask true p) = a.rightCoefficient p)
    (K : List Bool → ℕ) (hK : UnaryFn K)
    (hword : ∀ root q, tasks L a root q → q.length ≤ K root)
    (hanswer : ∀ root q, tasks L a root q →
      (answer (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf) q).length ≤ K root) :
    SpaceFunction (CannyResultantBits.WithSquarefreeLeaves.family L (F := F) isLeaf leftOrder rightOrder).value := by
  obtain ⟨M, hM, hb⟩ := commonMetadata_bound (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf)
    (CannyResultantBits.WithSquarefreeLeaves.controls L a isLeaf ha isLeaf_FP) K hK
  have hp (root q : List Bool) (hq : tasks L a root q) : (payload q).length ≤ K root := by
    simp only [payload, List.length_drop]
    exact (Nat.sub_le _ _).trans (hword root q hq)
  exact CannyResultantBits.WithSquarefreeLeaves.evaluator L a isLeaf A ha isLeaf_FP
    (coefficientTask false) (coefficientTask true) (coefficientTask_FP false) (coefficientTask_FP true) hl hr
    (tasks L a) level List.length K M (UnaryFn.length id_mem_FP) hK hM
    (tasks_root L a) (reachable_level_bound L a) hword hanswer (tasks_closed L a)
    (source_levels L a (tasks L a))
    (fun root q hq _ => (hb root (payload q) (hp root q hq)).1)
    (fun root q hq _ => (hb root (payload q) (hp root q hq)).2)

end LeanCanny.Algebra.CannyBalancedTaskRouting
