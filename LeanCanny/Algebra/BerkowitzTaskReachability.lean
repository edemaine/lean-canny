/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskLevels
public import Mathlib.Logic.Relation

/-! # The actual query-reachable determinant task graph

Reachability includes precisely finite chains of active oracle-run requests
within their logical budgets. Closure is automatic, and every ranked query
contract bounds reachable ranks by the root rank. No child computation or
execution-clock certificate is involved in this proof-only graph.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Computation

variable {F : ModularFamily} (a : ModularAccess F)
variable {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)

def Requests (sourceBudget : List Bool → ℕ) (q child : List Bool) : Prop :=
  ∃ t, t ≤ budget (F := F) sourceBudget q ∧
    (controller a source).halted (((controller a source).reference (answer a))^[t] ((controller a source).initial q)) = false ∧
    (controller a source).needs (((controller a source).reference (answer a))^[t] ((controller a source).initial q)) = true ∧
    child = (controller a source).query (((controller a source).reference (answer a))^[t] ((controller a source).initial q))

def Reachable (sourceBudget : List Bool → ℕ) : List Bool → List Bool → Prop :=
  Relation.ReflTransGen (Requests a source sourceBudget)

theorem reachable_root (sourceBudget : List Bool → ℕ) (q : List Bool) : Reachable a source sourceBudget q q :=
  .refl

theorem reachable_closed (sourceBudget : List Bool → ℕ) :
    QueriesClosed a source sourceBudget (Reachable a source sourceBudget) := by
  intro root q t hq ht hh hn
  exact hq.tail ⟨t, ht, hh, hn, rfl⟩

theorem reachable_rank_le (sourceBudget : List Bool → ℕ) (rank : List Bool → ℕ)
    (hgraph : RankedQueries a source sourceBudget (Reachable a source sourceBudget) rank)
    (root q : List Bool) (hq : Reachable a source sourceBudget root q) : rank q ≤ rank root := by
  induction hq with
  | refl => exact le_refl _
  | @tail q child hq hstep ih =>
    obtain ⟨t, ht, hh, hn, he⟩ := hstep
    have hr := (hgraph root q t hq ht hh hn).2
    rw [← he] at hr
    exact hr.le.trans ih

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
