/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateAtRadius
public import LeanCanny.Algebra.IntegralMixedSourceIntegerScalarOnly
public import LeanCanny.Geometry.IntegralMixedRealizedCompleteVertex

/-! # A filtered candidate's complete marked prelude retains one joint vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateVertex
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedAuxiliaryMarkedIntegerPlan (parameters plan spatial)
open IntegralMixedAuxiliaryMarkedCandidateAtRadius (context replayState replayValues native_radius_le)
open LeanCanny.Connectivity.AuxiliaryCandidateComponentCover (Good)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem scalarOnly {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (ctx : List Bool) :
    IntegralHistorySampler.ScalarOnly (replayState hn ht ha R ctx).sampler := by
  let P:=parameters hn ht ha
  let D:=plan hn ht ha R
  let hq:=fun c=>(IntegralMixedFramedHistoryFamilyBits.initial P D c).critical_cap
  exact IntegralMixedSourceIntegerPrelude.scalarOnly P (spatial n t R) hq
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (fun c=>number n c+8)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) ctx
    (IntegralMixedFramedHistoryFamilyBits.initial P D ctx) (IntegralHistorySampler.base_scalarOnly _ _)
    (by rw [IntegralMixedSourceIntegerPrelude.commands_length]; change _+8≤_+8+2+1+1; omega)

theorem canonical {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (ctx : List Bool) :
    IntegralMixedHistory.Canonical (replayState hn ht ha R ctx) :=
  IntegralMixedFramedHistoryScript.run_canonical _ (fun i=>Fin.elim0 i) _ _

theorem exists_vertex {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (u label outer : List Bool) (hg : Good hn ht ha u label)
    (F : SquareSampleInput.Inputs) (hF : SquareSampleComplete.Complete F) (c : List Bool)
    (hm : F.count c=((plan hn ht ha (IntegralMixedAuxiliaryMarkedIntegerPlan.radius hn ht ha)).rules
      (context u label outer)).length)
    (hr : HEq (F.system c)
      (replayState hn ht ha (IntegralMixedAuxiliaryMarkedIntegerPlan.radius hn ht ha) (context u label outer)).sampler.scalarPrefix.rows) :
    ∃w : List Bool,∃hw : SquareSampleCompleteVertices.Valid F c w,
      w.length=SquareSampleCompleteVertices.width F c ∧ ∀i,
        IntegralMixedCanonicalBankPoint.point
          (replayState hn ht ha (IntegralMixedAuxiliaryMarkedIntegerPlan.radius hn ht ha) (context u label outer))
          (IntegralMixedCanonicalCompleteVertex.tuple F c w hw hm) i=
        replayValues hn ht ha (IntegralMixedAuxiliaryMarkedIntegerPlan.radius hn ht ha) u label outer hg
          (native_radius_le hn ht ha u label outer) i.val :=
  IntegralMixedRealizedCompleteVertex.exists_vertex _
    (canonical hn ht ha _ _) (scalarOnly hn ht ha _ _) F hF c hm hr _
    (IntegralMixedAuxiliaryMarkedCandidateAtRadius.realizes_native hn ht ha u label outer hg)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateVertex
