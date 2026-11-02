/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateSampling

/-! # Every valid candidate has one actual joint-root bank point

Only the original coordinates are retained, at newest-first indices n-i.
Validity does not assert that these coordinates satisfy the original equation.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliaryRecipeRoot
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open IntegralMixedFramedBankObservation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def bankData {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (packed : List Bool) : IntegralMixedFramedBankObservation.Data :=
  ofState ((IntegralMixedFramedHistoryFamilyBits.family (parameters (dimension n) (term t))
    (planAt hn ht ha) (dataAt hn ht ha)).state
    (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id packed))

noncomputable def joint {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : Valid hn ht ha q) : ℕ→ℝ :=
  extend (SquareSampleCompleteVertices.candidate (input hn ht ha) (source n t q) (vertex hn ht ha q) hq.2).val

noncomputable def point {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : Valid hn ht ha q) : Fin (n (pairFst q))→ℝ :=
  fun i=>(bankData hn ht ha (source n t q)).point (joint hn ht ha q hq) (n (pairFst q)-i.val)

attribute [local irreducible] parameters scalarWidth scalarCeiling spatialDegree degreeCharge augmented root planAt bankData positiveInput positiveState source vertex input pair

theorem bankData_recipe {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original)→ℕ×ℕ) (advice : List Bool) :
    bankData hn ht ha (root original labels advice)=ofState (positiveState hn ht ha (root original labels advice)) := by
  have HL:=script_length hn ht ha original labels advice
  have HR:=(planAt hn ht ha).room (root original labels advice)
  have HM : n original≤(parameters (dimension n) (term t)).cap (root original labels advice) := by omega
  have HK : IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id (root original labels advice)=
      IntegralMixedFramedHistoryFamilyBits.keyAt (root original labels advice) (n original+1) [] := by
    unfold IntegralMixedAuxiliaryPositivePrefix.key dimension
    simp only [id_eq,root_original]

  unfold bankData
  rw [HK]
  unfold positiveState
  exact IntegralMixedFramedBankObservation.terminal _ _ (dataAt hn ht ha) _ _ HM HL

private theorem extend_cast {a b : ℕ} (h : a=b) (z : Fin a→ℝ) :
    extend z=extend (z ∘ Fin.cast h.symm) := by
  cases h
  rfl

private theorem candidate_joint_congr (F G : SquareSampleInput.Inputs) (hF : F=G) (a b x y : List Bool)
    (hx : SquareSampleCompleteVertices.Valid F a x) (hy : SquareSampleCompleteVertices.Valid G b y)
    (hab : a=b) (hxy : x=y) :
    extend (SquareSampleCompleteVertices.candidate F a x hx).val=
      extend (SquareSampleCompleteVertices.candidate G b y hy).val := by
  cases hF
  cases hab
  cases hxy
  rfl

private theorem tuple_extend (F : SquareSampleInput.Inputs) (u w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid F u w) {m : ℕ} (hm : F.count u=m) :
    extend (SquareSampleCompleteVertices.candidate F u w hv).val=
      extend (LeanCanny.Geometry.IntegralMixedCanonicalCompleteVertex.tuple F u w hv hm) :=
  extend_cast hm _

theorem joint_recipe {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : Valid hn ht ha q)
    (original : List Bool) (labels : Fin (n original)→ℕ×ℕ) (advice w : List Bool)
    (hs : source n t q=root original labels advice) (hw : vertex hn ht ha q=w)
    (hv : SquareSampleCompleteVertices.Valid (positiveInput hn ht ha) (root original labels advice) w) :
    joint hn ht ha q hq=extend (LeanCanny.Geometry.IntegralMixedCanonicalCompleteVertex.tuple
      (positiveInput hn ht ha) (root original labels advice) w hv (positive_count hn ht ha original labels advice)) := by
  exact (candidate_joint_congr (input hn ht ha) (positiveInput hn ht ha) (candidate_input_eq hn ht ha)
    (source n t q) (root original labels advice) (vertex hn ht ha q) w hq.2 hv hs hw).trans
      (tuple_extend (positiveInput hn ht ha) (root original labels advice) w hv
        (positive_count hn ht ha original labels advice))

theorem point_recipe {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original label : List Bool) (hq : Valid hn ht ha (pair original label))
    (labels : Fin (n original)→ℕ×ℕ) (advice w : List Bool)
    (hs : source n t (pair original label)=root original labels advice)
    (hw : vertex hn ht ha (pair original label)=w)
    (hv : SquareSampleCompleteVertices.Valid (positiveInput hn ht ha) (root original labels advice) w)
    (i : Fin (n original)) (j : Fin (((planAt hn ht ha).rules (root original labels advice)).length+1))
    (hj : j.val=n original-i.val) :
    point hn ht ha (pair original label) hq ⟨i.val,by simpa only [pairFst_pair] using i.isLt⟩=
      LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point (positiveState hn ht ha (root original labels advice))
        (LeanCanny.Geometry.IntegralMixedCanonicalCompleteVertex.tuple (positiveInput hn ht ha)
          (root original labels advice) w hv (positive_count hn ht ha original labels advice)) j := by
  unfold point
  rw [hs,bankData_recipe,joint_recipe hn ht ha _ hq original labels advice w hs hw hv]
  simp only [pairFst_pair,←hj]
  exact point_ofState _ _ j
end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
