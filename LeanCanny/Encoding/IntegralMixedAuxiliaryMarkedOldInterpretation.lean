/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateContextInterpretation
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource

/-! # The marked replay's outer-context key interprets its literal old candidate -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedOldInterpretation
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate original oldKey)
open IntegralMixedAuxiliaryCandidateInterpretation (parameters key)
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open IntegralMixedFramedSlackMatrixBits (elementAt commonAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem old_prefix (n : List Bool→ℕ) (t : List Bool→Term) (ctx : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (oldKey n t ctx)=number n ctx+1 := by
  apply IntegralMixedFramedHistoryFamilyBits.keyAt_prefix
  have H:=Nat.succ_le_succ (IntegralMixedAuxiliaryParameters.original_coordinates (dimension n) (term t)
    (IntegralMixedAuxiliaryCandidate.source n t (candidate ctx)))
  simpa only [dimension,IntegralMixedAuxiliaryCandidate.source_input,number,original] using H

theorem same_prefix (n : List Bool→ℕ) (t : List Bool→Term) (ctx : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key n t (candidate ctx))=
      IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (oldKey n t ctx) := by
  rw [old_prefix,key,IntegralMixedAuxiliaryPositivePrefix.key_prefix]
  simp only [dimension,id_eq,IntegralMixedAuxiliaryCandidate.source_input,number,original]

theorem same_root (n : List Bool→ℕ) (t : List Bool→Term) (ctx : List Bool) :
    pairFst (key n t (candidate ctx))=pairFst (oldKey n t ctx) := by
  simp only [key,IntegralMixedAuxiliaryPositivePrefix.key,oldKey,IntegralMixedFramedHistoryFamilyBits.keyAt_root,id_eq]

theorem count_at (n : List Bool→ℕ) (t : List Bool→Term) (ctx : List Bool) :
    IntegralMixedAuxiliarySlackMatrix.count n (oldKey n t ctx)=number n ctx := by
  simp only [IntegralMixedAuxiliarySlackMatrix.count,IntegralMixedAuxiliarySlackMatrix.original,oldKey,
    IntegralMixedFramedHistoryFamilyBits.keyAt_root,IntegralMixedAuxiliaryCandidate.source_input,number,original]

theorem charge_at (n : List Bool→ℕ) (t : List Bool→Term) (ctx : List Bool) :
    IntegralMixedAuxiliarySlackMatrix.charge t (oldKey n t ctx)=
      LeanCanny.Geometry.AuxiliaryCandidateRegularLift.allowance t (original ctx) := by
  simp only [IntegralMixedAuxiliarySlackMatrix.charge,IntegralMixedAuxiliarySlackMatrix.original,oldKey,
    IntegralMixedFramedHistoryFamilyBits.keyAt_root,IntegralMixedAuxiliaryCandidate.source_input,original]

attribute [local irreducible] IntegralMixedAuxiliaryParameters.parameters
  IntegralMixedAuxiliaryParameters.scalarWidth IntegralMixedAuxiliaryParameters.scalarCeiling
  IntegralMixedAuxiliaryParameters.spatialDegree IntegralMixedAuxiliaryParameters.degreeCharge
  IntegralMixedAuxiliaryParameters.augmented planAt dataAt
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point
  IntegralMixedAuxiliaryCandidate.bankData IntegralMixedAuxiliaryCandidate.joint pair
  IntegralMixedFramedHistoryFamilyBits.family oldKey

theorem exists_interpretation {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (ctx : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate ctx)) :
    ∃φ : ((IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)).state
      (oldKey n t ctx)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀i : Fin (number n ctx),φ (elementAt (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
        (oldKey n t ctx) (number n ctx-i.val))=(commonAt (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
          (oldKey n t ctx) : ℝ)*IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hq i :=
  IntegralMixedAuxiliaryCandidateContextInterpretation.exists_at_sibling hn ht ha (candidate ctx) hq
    (oldKey n t ctx) (same_root n t ctx) (same_prefix n t ctx)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedOldInterpretation
