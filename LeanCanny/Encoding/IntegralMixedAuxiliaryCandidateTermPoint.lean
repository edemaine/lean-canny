/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidatePointSampling
public import LeanCanny.Geometry.IntegralMixedFramedBankTermObservation
/-! # The native original-term filter reads the literal candidate point

Only original coordinates are compared. The positive prefix has one extra
default birth; its coordinate is outside the original term's arity.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliaryRecipeRoot
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open scoped Classical

noncomputable def termTuple {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : Valid hn ht ha q) :
    Fin (IntegralMixedFramedBankSnapshotBits.atKey (parameters (dimension n) (term t))
      (planAt hn ht ha) (dataAt hn ht ha)
      (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id (source n t q))).count→ℝ :=
  fun j=>joint hn ht ha q hq j.val

attribute [local irreducible] parameters scalarWidth scalarCeiling spatialDegree degreeCharge augmented
  planAt dataAt input source vertex bankData joint point termTuple

theorem term_point {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : Valid hn ht ha q) (i : Fin (n (pairFst q))) :
    LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point
      (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha)
      (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id (source n t q))
      (termTuple hn ht ha q hq) i.val=
        point hn ht ha q hq i := by
  let P := parameters (dimension n) (term t)
  let D := planAt hn ht ha
  let H := dataAt hn ht ha
  let key := IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id (source n t q)
  have HC : (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count=n (pairFst q)+1 := by
    change (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key=_
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    rw [IntegralMixedAuxiliaryPositivePrefix.key_prefix]
    exact congrArg (fun j=>n j+1) (source_input n t q)
  have HI : i.val<(IntegralMixedFramedBankSnapshotBits.atKey P D H key).count := by rw [HC]; omega
  have HR : IntegralMixedFramedBankTermBits.reverseIndex P D H key i.val=n (pairFst q)-i.val := by
    unfold IntegralMixedFramedBankTermBits.reverseIndex
    rw [HC]
    omega
  unfold termTuple
  change LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point P D H key
    (fun j=>joint hn ht ha q hq j.val) i.val=_
  rw [LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point_observation P D H key _ _ HI,HR]
  unfold point bankData
  rfl

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
