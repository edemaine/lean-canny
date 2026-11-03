/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerCertified
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Budget planning preserves the actual marked replay rows and bank

These projections expose exactly the data needed by one joint-tuple complete
vertex. They do not identify separately sampled roots or packed task words.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPlannedObservation
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedNormalizationBits (planned plannedPlan plannedData)
set_option backward.isDefEq.respectTransparency false

theorem rows (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) :
    HEq (((IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
      (plannedData P D J L F C)).state key).sampler.scalarPrefix.rows)
      (((IntegralMixedFramedHistoryFamilyBits.family P D J).state key).sampler.scalarPrefix.rows) := HEq.rfl

theorem bank (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) :
    IntegralMixedFramedBankObservation.ofState ((IntegralMixedFramedHistoryFamilyBits.family
      (planned P L F C) (plannedPlan P D L F C) (plannedData P D J L F C)).state key)=
    IntegralMixedFramedBankObservation.ofState ((IntegralMixedFramedHistoryFamilyBits.family P D J).state key) := rfl
end LeanCanny.Algebra.IntegralMixedFramedPlannedObservation

namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
set_option backward.isDefEq.respectTransparency false

theorem certified_rows {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (key : List Bool) :
    HEq (((IntegralMixedFramedHistoryFamilyBits.family (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (certifiedData hn ht ha hR)).state key).sampler.scalarPrefix.rows)
      (((IntegralMixedFramedHistoryFamilyBits.family (parameters hn ht ha) (plan hn ht ha R)
        (data hn ht ha R)).state key).sampler.scalarPrefix.rows) :=
  IntegralMixedFramedPlannedObservation.rows (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR) key

theorem certified_bank {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (key : List Bool) :
    IntegralMixedFramedBankObservation.ofState ((IntegralMixedFramedHistoryFamilyBits.family
      (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)).state key)=
    IntegralMixedFramedBankObservation.ofState ((IntegralMixedFramedHistoryFamilyBits.family
      (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)).state key) :=
  IntegralMixedFramedPlannedObservation.bank (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR) key

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
