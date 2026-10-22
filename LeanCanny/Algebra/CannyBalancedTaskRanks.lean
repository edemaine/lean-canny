/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyBalancedTaskRouting
public import LeanCanny.Algebra.BerkowitzTaskReachability

/-! # A common rank bound for the concrete balanced coefficient graph

Actual query reachability supplies closure. The unary address height and
internal stage priorities give rank at most `5*root.length+4` for every reachable
task, on all input words. The uniform reader below therefore needs only child
semantics and quantitative word/reply/metadata bounds, with no separate task
closure, rank, or source-level hypotheses.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyBalancedTaskRouting
open LeanCanny.Encoding LeanCanny.Computation
open BerkowitzPolynomial.TaskDispatch

variable (L : SeparableBits.Family) {F : CannyResultantBits.Family} (a : CannyResultantBits.Access F)

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
rank/level bound. Child semantic identities and quantitative graph bounds
remain explicit, as do the original leaf readers and FP metadata. -/
theorem evaluator (A : SeparableBits.Readers L) (ha : a.ControlsPolyTime)
    (hl : ∀ p, answer (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf) (coefficientTask false p) = a.leftCoefficient p)
    (hr : ∀ p, answer (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf) (coefficientTask true p) = a.rightCoefficient p)
    (K M : List Bool → ℕ) (hK : UnaryFn K) (hM : UnaryFn M)
    (hword : ∀ root q, tasks L a root q → q.length ≤ K root)
    (hanswer : ∀ root q, tasks L a root q →
      (answer (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf) q).length ≤ K root)
    (hdet : ∀ root q, tasks L a root q → SelectedDeterminant q →
      determinantFields (F := CannyResultantBits.WithSquarefreeLeaves.family L (F := F) isLeaf) (payload q) ≤ M root)
    (hmoment : ∀ root q, tasks L a root q → SelectedMoment q →
      momentFields (F := CannyResultantBits.WithSquarefreeLeaves.family L (F := F) isLeaf) (payload q) ≤ M root) :
    SpaceFunction (CannyResultantBits.WithSquarefreeLeaves.family L (F := F) isLeaf).value :=
  CannyResultantBits.WithSquarefreeLeaves.evaluator L a isLeaf A ha isLeaf_FP
    (coefficientTask false) (coefficientTask true) (coefficientTask_FP false) (coefficientTask_FP true) hl hr
    (tasks L a) level List.length K M (UnaryFn.length id_mem_FP) hK hM
    (tasks_root L a) (reachable_level_bound L a) hword hanswer (tasks_closed L a)
    (source_levels L a (tasks L a)) hdet hmoment

end LeanCanny.Algebra.CannyBalancedTaskRouting
