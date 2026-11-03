/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutScan
/-! # Original-only native tests of a single full physical replay

Original-coordinate Thom matching, every critical correlation and every
chronological cut share the literal full sample. The full-row cost is derived
from the original marked plan, rather than supplied as an evaluator premise.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalReplayNative
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

theorem thom_decider : SpaceDecider (IntegralMixedPhysicalReplayThom.language hn ht ha hR outer) :=
  IntegralMixedPhysicalReplayThom.decider hn ht ha hR outer
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)

theorem marked_replay_decider : SpaceDecider (IntegralMixedPhysicalReplayRelation.language hn ht ha hR outer) :=
  IntegralMixedPhysicalReplayRelation.decider hn ht ha hR outer
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)

theorem correlation_decider : SpaceDecider (IntegralMixedPhysicalGuardScan.language hn ht ha hR outer) :=
  IntegralMixedPhysicalGuardScan.decider hn ht ha hR outer
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)

theorem correlated_replay_decider : SpaceDecider (IntegralMixedPhysicalGuardScan.relation hn ht ha hR outer) :=
  IntegralMixedPhysicalGuardScan.relation_decider hn ht ha hR outer
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)

theorem cuts_decider : SpaceDecider (IntegralMixedPhysicalTraceCutScan.language hn ht ha hR outer) :=
  IntegralMixedPhysicalTraceCutScan.decider hn ht ha hR outer
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)

theorem decider : SpaceDecider (IntegralMixedPhysicalTraceCutScan.relation hn ht ha hR outer) :=
  IntegralMixedPhysicalTraceCutScan.relation_decider hn ht ha hR outer
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)

theorem mem_PSPACE : IntegralMixedPhysicalTraceCutScan.relation hn ht ha hR outer∈PSPACE :=
  (decider hn ht ha hR outer).mem_PSPACE

end LeanCanny.Encoding.IntegralMixedPhysicalReplayNative
