/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
/-! # The actual packed family uses exactly the seeded geometric sources -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem source_heq {N N' K K' D D' M M' B B' G G' : ℕ} {a a' : Term}
    (ha : (AuxiliaryTiltedTerm.term N a).degreeBound≤D)
    (ha' : (AuxiliaryTiltedTerm.term N' a').degreeBound≤D')
    (hN : N=N') (hK : K=K') (hD : D=D') (hT : a=a') (hM : M=M') (hB : B=B') (hG : G=G') :
    HEq (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.source K D a ha M B G)
      (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.source K' D' a' ha' M' B' G') := by
  cases hN
  cases hK
  cases hD
  cases hT
  cases hM
  cases hB
  cases hG
  rfl

theorem recipeCap (n : List Bool → ℕ) (t : List Bool → Term) (original : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap (n original+3)
      (FixedLeadingTiltedSource.degree (degreeCharge n t original))≤2^scalarWidth n t original := by
  unfold scalarWidth scalarCeiling spatialDegree
  exact (Nat.lt_size_self _).le

noncomputable def currentSource {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) (birth : ℕ) :=
  IntegralMixedCanonicalUnitSourceBits.source (parameters (dimension n) (term t))
    (IntegralMixedAuxiliaryEmptyPlan.originals (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
      (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q => ha (pairFst q)))
    (root original labels advice) birth

theorem currentSource_recipe {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) (j : Fin (n original)) :
    HEq (currentSource hn ht ha original labels advice j.val)
      (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.recipeSource (n:=n original) (S:=n original+3)
        (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
        (ht:=(augmented n t original).degreeBound_le_dataSize) (seed n t original+1) j.val) := by
  have HD : degreeCharge (dimension n) (term t) (root original labels advice)=degreeCharge n t original := by
    simp only [degreeCharge,augmented,dimension,term,root_original]
  have HB : scalarWidth (dimension n) (term t) (root original labels advice)=scalarWidth n t original := by
    simp only [scalarWidth,scalarCeiling,spatialDegree,HD,dimension,root_original]
  have HC : seed (dimension n) (term t) (root original labels advice)=seed n t original := by
    simp only [seed,HD,dimension,term,root_original]
  have HG:=root_height n t original labels advice j.val
  rw [HD,HB,HC] at HG
  have HS:=IntegralMixedAuxiliaryEmptyPlan.source_geometry
    (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn) (IntegralMixedAuxiliaryPreparedRoot.term_FP ht)
    (fun q => ha (pairFst q)) (root original labels advice) j.val
  refine (heq_of_eq HS).trans ?_
  apply source_heq
    ((augmented (dimension n) (term t) (root original labels advice)).degreeBound_le_dataSize)
    ((augmented n t original).degreeBound_le_dataSize)
  · simp only [dimension,root_original]
  · exact root_frozen n original labels advice j
  · exact HD
  · simp only [term,root_original]
  · rfl
  · exact HB
  · exact HG
theorem currentSource_recipe_le {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) (birth : ℕ) (hb : birth≤n original) :
    HEq (currentSource hn ht ha original labels advice birth)
      (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.recipeSource (n:=n original) (S:=n original+3)
        (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
        (ht:=(augmented n t original).degreeBound_le_dataSize) (seed n t original+1) birth) := by
  have HD : degreeCharge (dimension n) (term t) (root original labels advice)=degreeCharge n t original := by
    simp only [degreeCharge,augmented,dimension,term,root_original]
  have HB : scalarWidth (dimension n) (term t) (root original labels advice)=scalarWidth n t original := by
    simp only [scalarWidth,scalarCeiling,spatialDegree,HD,dimension,root_original]
  have HC : seed (dimension n) (term t) (root original labels advice)=seed n t original := by
    simp only [seed,HD,dimension,term,root_original]
  have HG:=root_height n t original labels advice birth
  rw [HD,HB,HC] at HG
  have HS:=IntegralMixedAuxiliaryEmptyPlan.source_geometry
    (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn) (IntegralMixedAuxiliaryPreparedRoot.term_FP ht)
    (fun q => ha (pairFst q)) (root original labels advice) birth
  refine (heq_of_eq HS).trans ?_
  apply source_heq
    ((augmented (dimension n) (term t) (root original labels advice)).degreeBound_le_dataSize)
    ((augmented n t original).degreeBound_le_dataSize)
  · simp only [dimension,root_original]
  · unfold frozen
    simp only [dimension,root_original]
    exact min_eq_left hb
  · exact HD
  · simp only [term,root_original]
  · rfl
  · exact HB
  · exact HG
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
