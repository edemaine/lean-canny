/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryPositiveNativeSquare
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeNativeRealization
public import LeanCanny.Encoding.IntegralFramedCompleteTerminalRows
public import LeanCanny.Geometry.IntegralMixedDefaultCompleteVertex

/-! # Packed component samples are vertices of the actual positive prefix

The native input uses n+1 births. Its joint rows are the literal packed run
followed by the existing integer-X default. Every original coordinate is
read at its shifted newest-first index from the same bank point.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open LeanCanny.Geometry LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def positiveInput {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedAuxiliaryPositivePrefix.input (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
    (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q=>ha (pairFst q)) id

noncomputable def positiveState {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (packed : List Bool) :=
  run (IntegralMixedFramedHistoryFamilyBits.initial (parameters (dimension n) (term t)) (planAt hn ht ha) packed)
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction (parameters (dimension n) (term t)) (planAt hn ht ha) packed::
      (planAt hn ht ha).rules packed)
    (by have H:=(planAt hn ht ha).room packed; simp only [List.length_cons]; omega)

theorem positive_native_access {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    (positiveInput hn ht ha).Access :=
  IntegralMixedAuxiliaryPositivePrefix.native_access (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
    (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q=>ha (pairFst q)) id id_mem_FP

attribute [local irreducible] parameters scalarWidth scalarCeiling spatialDegree degreeCharge augmented root planAt
  IntegralMixedAuxiliaryPositivePrefix.key IntegralMixedEmptyUnitPlan.records IntegralMixedEmptyUnitPlan.count pair

theorem positive_count {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original)→ℕ×ℕ) (advice : List Bool) :
    (positiveInput hn ht ha).count (root original labels advice)=
      ((planAt hn ht ha).rules (root original labels advice)).length+1 := by
  have H:=IntegralMixedAuxiliaryPositivePrefix.count_eq
    (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn) (IntegralMixedAuxiliaryPreparedRoot.term_FP ht)
    (fun q=>ha (pairFst q)) id (root original labels advice)
  change (positiveInput hn ht ha).count (root original labels advice)=dimension n (root original labels advice)+1 at H
  exact H.trans (congrArg (fun k:ℕ=>k+1)
    ((congrArg n (root_original original labels advice)).trans (script_length hn ht ha original labels advice).symm))

theorem positive_rows {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original)→ℕ×ℕ) (advice : List Bool) :
    HEq ((positiveInput hn ht ha).system (root original labels advice))
      (positiveState hn ht ha (root original labels advice)).sampler.scalarPrefix.rows := by
  have HM : dimension n (root original labels advice)≤
      (parameters (dimension n) (term t)).cap (root original labels advice) := by
    have HR:=(planAt hn ht ha).room (root original labels advice)
    have HL:=script_length hn ht ha original labels advice
    change n (pairFst (root original labels advice))≤_
    rw [root_original]
    omega
  have HL:=(script_length hn ht ha original labels advice).trans
    (congrArg n (root_original original labels advice)).symm
  unfold planAt at HL
  unfold positiveInput IntegralMixedAuxiliaryPositivePrefix.input IntegralMixedAuxiliaryEmptyPlan.squareInput positiveState planAt
  have Hresult:=IntegralFramedCompleteSquare.rows_after_script
    (parameters (dimension n) (term t))
    (IntegralMixedAuxiliaryEmptyPlan.plan (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
      (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q=>ha (pairFst q)))
    (IntegralMixedAuxiliaryEmptyPlan.data (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
      (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q=>ha (pairFst q)))
    (fun _=>1) (factor (dimension n) (term t)) (seed (dimension n) (term t))
    (IntegralMixedAuxiliaryEmptyPlan.familyInputs (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
      (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q=>ha (pairFst q)))
    (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id)
    (fun u=>(IntegralMixedAuxiliaryPositivePrefix.key_positive (dimension n) (term t) id u).trans_eq
      (IntegralMixedFramedHistoryFamilyBits.family_birth (parameters (dimension n) (term t))
        (IntegralMixedAuxiliaryEmptyPlan.plan (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
          (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q=>ha (pairFst q)))
        (IntegralMixedAuxiliaryEmptyPlan.data (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
          (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q=>ha (pairFst q)))
        (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id u)).symm)
    (root original labels advice) (root original labels advice) (dimension n (root original labels advice)) HM
    HL (by unfold IntegralMixedAuxiliaryPositivePrefix.key; rfl)
  exact Hresult

theorem positive_vertex_of_realization {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original)→ℕ×ℕ) (advice : List Bool)
    (p : Fin (n original)→ℝ) (hp : OriginalRealization (nativeRun hn ht ha original labels advice) p) :
    let F:=positiveInput hn ht ha
    let packed:=root original labels advice
    ∃ w : List Bool, ∃ hw : SquareSampleCompleteVertices.Valid F packed w,
      w.length=SquareSampleCompleteVertices.width F packed ∧
      ∀ i : Fin (n original),∃ j : Fin (((planAt hn ht ha).rules packed).length+1),j.val=n original-i.val ∧
        p i=IntegralMixedCanonicalBankPoint.point (positiveState hn ht ha packed)
          (IntegralMixedCanonicalCompleteVertex.tuple F packed w hw (positive_count hn ht ha original labels advice)) j := by
  have Hroom:=(planAt hn ht ha).room (root original labels advice)
  obtain ⟨w,hw,hlen,_,hread⟩:=default_complete_vertex
    (IntegralMixedFramedHistoryFamilyBits.initial (parameters (dimension n) (term t)) (planAt hn ht ha) (root original labels advice))
    ((planAt hn ht ha).rules (root original labels advice)) (by omega) (by omega)
    (rules_noncritical hn ht ha original labels advice) p hp
    (positiveInput hn ht ha)
    (IntegralMixedAuxiliaryPositivePrefix.complete (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
      (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q=>ha (pairFst q)) id)
    (root original labels advice) (positive_count hn ht ha original labels advice)
    (positive_rows hn ht ha original labels advice)
  exact ⟨w,hw,hlen,hread⟩

end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
