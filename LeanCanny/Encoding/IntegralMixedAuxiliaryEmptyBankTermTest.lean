/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankTermZero
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyCompanionSpace
/-! # Original-only term tests on actual empty-prelude joint vertices

The original dimension, term and arity scope derive all sampling and test
coefficient readers, including arbitrary caller moduli. The test term word
is read at the complete original root of the saved prefix.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryParameters
open scoped Classical
variable {n : List Bool→ℕ} {t : List Bool→Term}

noncomputable def termSyntax (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) :=
  IntegralMixedEmptyTiltedNative.inputSyntax (parameters n t) (access hn ht) (description hn ht ha)
    (ambient_positive n t) (auxiliary_cap n t) (room n t) (source_width n t)

noncomputable def termValue (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool)
    (hpos : ∀ c,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key c))
    (word : List Bool→List Bool) :=
  IntegralFramedBankTermTest.value (parameters n t) (plan hn ht ha) (data hn ht ha) (termSyntax hn ht ha)
    (familyInputs hn ht ha) key
    (fun c=>(hpos c).trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth (parameters n t)
      (plan hn ht ha) (data hn ht ha) (key c)).symm) word

theorem term_evaluator (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ c,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key c))
    (word : List Bool→List Bool) (hw : word∈FP) : SpaceFunction (termValue hn ht ha key hpos word) :=
  IntegralFramedBankTermTest.evaluator (parameters n t) (access hn ht) _ _ (termSyntax hn ht ha)
    (familyInputs hn ht ha) (description hn ht ha).factor_positive (fun _=>Nat.le_refl 1) key hk _ word hw

noncomputable def termZeroLanguage (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool)
    (hpos : ∀ c,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key c))
    (word : List Bool→List Bool) :=
  IntegralFramedBankTermTest.zeroLanguage (parameters n t) (plan hn ht ha) (data hn ht ha) (termSyntax hn ht ha)
    (familyInputs hn ht ha) key
    (fun c=>(hpos c).trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth (parameters n t)
      (plan hn ht ha) (data hn ht ha) (key c)).symm) word

theorem term_zero_decider (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ c,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key c))
    (word : List Bool→List Bool) (hw : word∈FP) : SpaceDecider (termZeroLanguage hn ht ha key hpos word) :=
  IntegralFramedBankTermTest.zero_decider (parameters n t) (access hn ht) _ _ (termSyntax hn ht ha)
    (familyInputs hn ht ha) (description hn ht ha).factor_positive (fun _=>Nat.le_refl 1) key hk _ word hw

end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
