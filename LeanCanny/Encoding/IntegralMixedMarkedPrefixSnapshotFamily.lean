/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotFamily
/-! # Actual marked saved keys recover the exact original-source prefix algebra -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "H"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha (radius_binary hR0)

theorem instruction_initial (key : List Bool) :
    (instruction P D key).source=(D).initialSource (pairFst key):=by
 rw [IntegralMixedFramedNormalizationBits.planned_instruction]
 exact IntegralMixedAuxiliaryMarkedRecordPlan.instruction_source hn ht ha (radius R0) key

theorem family_keyAt (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) (aux : List Bool) :
    IntegralMixedPrefixSnapshot.ofState ((family P D H).state (keyAt root (number n root+8+j) aux))=
      snapshot hn ht ha hR0 root j hj:=by
 have HF:=IntegralMixedPrefixSnapshot.family_eq_original P D H (keyAt root (number n root+8+j) aux)
   (instruction_initial hn ht ha hR0 _)
 have HK:=IntegralMixedPrefixSnapshot.original_keyAt P D root aux (number n root+8+j)
   (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j hj)
 exact HF.trans HK

end LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot
