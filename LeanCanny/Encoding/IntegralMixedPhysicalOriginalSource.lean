/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedOriginalRegularSource
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedPlan
/-! # Marked and outer replay instructions have one original spatial source

Planning and saved-prefix lookup preserve the literal original regular
source, including default instructions. Histories, banks, words and producer
roots are not equated by these source identities.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalOriginalSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (instruction family keyAt)
open IntegralMixedOriginalRegularSource (radius radius_binary context canonical source)
open IntegralMixedAuxiliaryMarkedIntegerSource (original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0) (outer : Bool)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) outer

theorem snapshot : BoundedRegularFramedOriginalBits.Snapshot (B).parameters (B).plan
    (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t (radius R0)) :=by
  cases outer
  · exact IntegralMixedAuxiliaryMarkedRecordPlan.certifiedSnapshot hn ht ha (radius_binary hR0)
  · exact IntegralMixedAuxiliaryOuterRecordPlan.certifiedSnapshot hn ht ha (radius_binary hR0)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

theorem instruction_source (key : List Bool) :
    HEq (instruction (B).parameters (B).plan key).source (source n t R0 (original (pairFst key))) :=
  (snapshot hn ht ha hR0 outer).source key

theorem family_source (key : List Bool) :
    HEq ((family (B).parameters (B).plan (B).data).spatial key)
      (source n t R0 (original (pairFst key))) :=
  instruction_source hn ht ha hR0 outer key

theorem instruction_packet (input label tail saved : List Bool) (birth : ℕ) :
    HEq (instruction (B).parameters (B).plan (keyAt (context input label tail) birth saved)).source
      (source n t R0 input) :=by
  refine (instruction_source hn ht ha hR0 outer _).trans
    (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ ?_)
  simp only [keyAt,pairFst_pair,IntegralMixedOriginalRegularSource.original_context]

theorem family_packet (input label tail saved : List Bool) (birth : ℕ) :
    HEq ((family (B).parameters (B).plan (B).data).spatial (keyAt (context input label tail) birth saved))
      (source n t R0 input) :=by
  refine (family_source hn ht ha hR0 outer _).trans
    (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ ?_)
  simp only [keyAt,pairFst_pair,IntegralMixedOriginalRegularSource.original_context]

theorem instruction_context (input label tail saved : List Bool) (birth : ℕ)
    (label' tail' saved' : List Bool) (birth' : ℕ) :
    HEq (instruction (B).parameters (B).plan (keyAt (context input label tail) birth saved)).source
      (instruction (B).parameters (B).plan (keyAt (context input label' tail') birth' saved')).source :=
  (instruction_packet hn ht ha hR0 outer input label tail saved birth).trans
    (instruction_packet hn ht ha hR0 outer input label' tail' saved' birth').symm

theorem family_context (input label tail saved : List Bool) (birth : ℕ)
    (label' tail' saved' : List Bool) (birth' : ℕ) :
    HEq ((family (B).parameters (B).plan (B).data).spatial (keyAt (context input label tail) birth saved))
      ((family (B).parameters (B).plan (B).data).spatial (keyAt (context input label' tail') birth' saved')) :=
  (family_packet hn ht ha hR0 outer input label tail saved birth).trans
    (family_packet hn ht ha hR0 outer input label' tail' saved' birth').symm

theorem instruction_canonical (input label tail saved : List Bool) (birth : ℕ) :
    HEq (instruction (B).parameters (B).plan (keyAt (context input label tail) birth saved)).source
      (instruction (B).parameters (B).plan (keyAt (canonical input) 0 [])).source :=
  instruction_context hn ht ha hR0 outer input label tail saved birth [] [] [] 0

theorem family_modes (outer' : Bool) (input label tail saved : List Bool) (birth : ℕ)
    (label' tail' saved' : List Bool) (birth' : ℕ) :
    HEq ((family (B).parameters (B).plan (B).data).spatial (keyAt (context input label tail) birth saved))
      ((family (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) outer').parameters
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) outer').plan
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) outer').data).spatial
          (keyAt (context input label' tail') birth' saved')) :=
  (family_packet hn ht ha hR0 outer input label tail saved birth).trans
    (family_packet hn ht ha hR0 outer' input label' tail' saved' birth').symm

theorem initial_source (root : List Bool) :
    HEq ((B).plan.initialSource root) (source n t R0 (original root)) :=by
  unfold IntegralMixedPhysicalMarkedPlan.bank
  cases outer <;> rfl
end LeanCanny.Encoding.IntegralMixedPhysicalOriginalSource
