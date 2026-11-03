/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerUniformSpace
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQBankProductPlannedSpace
/-! # Actual marked-prelude leading and bank products at arbitrary caller moduli

The current-Q controller is rebuilt from original syntax after modulus lifting
and planning. Every retained denominator is charged through its actual creator.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem leading_evaluator {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    SpaceFunction (IntegralMixedFramedLeadingBits.value (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)) :=
  IntegralMixedFramedCurrentQLeadingPlannedBits.evaluator (parameters hn ht ha) (access hn ht ha)
    (plan hn ht ha R) (data hn ht ha R) (liftedData hn ht ha R)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR∘pairFst) (BinaryFn.const 1) (BinaryFn.const 1)
    ((seed_binary hn ht ha hR).comp pairFst_mem_FP) (uniformControls hn ht ha hR) (uniformBounds hn ht ha hR)

theorem denominator_evaluator {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    SpaceFunction (IntegralMixedFramedBankDenominatorBits.value (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)) :=
  IntegralMixedFramedCurrentQBankProductPlannedBits.denominator_evaluator (parameters hn ht ha) (access hn ht ha)
    (plan hn ht ha R) (data hn ht ha R) (liftedData hn ht ha R)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR∘pairFst) (BinaryFn.const 1) (BinaryFn.const 1)
    ((seed_binary hn ht ha hR).comp pairFst_mem_FP) (uniformControls hn ht ha hR) (uniformBounds hn ht ha hR)

theorem product_evaluator {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) (skip : List Bool → ℕ) (hk : BinaryFn skip) :
    SpaceFunction (IntegralMixedFramedBankProductBits.value (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) skip) :=
  IntegralMixedFramedCurrentQBankProductPlannedBits.evaluator (parameters hn ht ha) (access hn ht ha)
    (plan hn ht ha R) (data hn ht ha R) (liftedData hn ht ha R)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR∘pairFst) (BinaryFn.const 1) (BinaryFn.const 1)
    ((seed_binary hn ht ha hR).comp pairFst_mem_FP) (uniformControls hn ht ha hR) (uniformBounds hn ht ha hR) skip hk

theorem common_evaluator {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    SpaceFunction (fun q=>residueBits
      (IntegralMixedHistory.commonDenominator
        (IntegralMixedFramedBankDenominatorBits.state (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) q) :
          ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
  IntegralMixedFramedCurrentQBankProductPlannedBits.common_evaluator (parameters hn ht ha) (access hn ht ha)
    (plan hn ht ha R) (data hn ht ha R) (liftedData hn ht ha R)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR∘pairFst) (BinaryFn.const 1) (BinaryFn.const 1)
    ((seed_binary hn ht ha hR).comp pairFst_mem_FP) (uniformControls hn ht ha hR) (uniformBounds hn ht ha hR)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
