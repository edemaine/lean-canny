/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankOrderLanguage
public import LeanCanny.Encoding.IntegralFramedBankOrderKey
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyBankTermTest
/-! # Original-only retained-quotient order queries on actual auxiliary prefixes

Original syntax constructs the whole changing-source sampler. The remaining
inputs are native binary labels/births and a native context writer. Every
comparison uses one complete joint-prefix vertex, with invalid labels zero.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
open scoped Classical
variable {n : List Bool→ℕ} {t : List Bool→Term}

noncomputable def orderValue (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP)
    (ha : ∀ q,(t q).arity≤n q) (birth : List Bool→ℕ) (context : List Bool→List Bool)
    (left right : List Bool→ℕ) :=
  IntegralFramedBankOrderTest.value (parameters n t) (plan hn ht ha) (data hn ht ha) (termSyntax hn ht ha)
    (familyInputs hn ht ha) (IntegralFramedBankOrderKey.key birth context)
    (IntegralFramedBankOrderKey.positive (parameters n t) (plan hn ht ha) (data hn ht ha) birth context) left right

theorem order_evaluator (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP)
    (ha : ∀ q,(t q).arity≤n q) (birth : List Bool→ℕ) (hb : BinaryFn birth)
    (context : List Bool→List Bool) (hc : context∈FP)
    (left right : List Bool→ℕ) (hl : BinaryFn left) (hr : BinaryFn right) :
    SpaceFunction (orderValue hn ht ha birth context left right) :=
  IntegralFramedBankOrderTest.evaluator (parameters n t) (access hn ht) (plan hn ht ha) (data hn ht ha)
    (termSyntax hn ht ha) (familyInputs hn ht ha) (description hn ht ha).factor_positive (fun _=>Nat.le_refl 1)
    (IntegralFramedBankOrderKey.key birth context) (IntegralFramedBankOrderKey.key_FP birth hb context hc)
    (IntegralFramedBankOrderKey.positive (parameters n t) (plan hn ht ha) (data hn ht ha) birth context) left right hl hr

theorem order_decider (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP)
    (ha : ∀ q,(t q).arity≤n q) (birth : List Bool→ℕ) (hb : BinaryFn birth)
    (context : List Bool→List Bool) (hc : context∈FP)
    (left right : List Bool→ℕ) (hl : BinaryFn left) (hr : BinaryFn right) (sign : SignType) :
    SpaceDecider (IntegralFramedBankOrderTest.language (parameters n t) (plan hn ht ha) (data hn ht ha)
      (termSyntax hn ht ha) (familyInputs hn ht ha) (IntegralFramedBankOrderKey.key birth context)
      (IntegralFramedBankOrderKey.positive (parameters n t) (plan hn ht ha) (data hn ht ha) birth context) left right sign) :=
  IntegralFramedBankOrderTest.decider (parameters n t) (access hn ht) (plan hn ht ha) (data hn ht ha)
    (termSyntax hn ht ha) (familyInputs hn ht ha) (description hn ht ha).factor_positive (fun _=>Nat.le_refl 1)
    (IntegralFramedBankOrderKey.key birth context) (IntegralFramedBankOrderKey.key_FP birth hb context hc)
    (IntegralFramedBankOrderKey.positive (parameters n t) (plan hn ht ha) (data hn ht ha) birth context) left right hl hr sign

end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
