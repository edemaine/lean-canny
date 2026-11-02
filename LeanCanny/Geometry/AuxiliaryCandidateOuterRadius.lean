/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.AuxiliaryCandidateRegularLift

/-! # The same original candidate is bounded at every larger outer radius -/
@[expose] public section
namespace LeanCanny.Geometry.AuxiliaryCandidateOuterRadius
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open LeanCanny.Connectivity.AuxiliaryCandidateComponentCover (Good)
open scoped Classical
attribute [local irreducible] AuxiliaryCandidateRegularLift.original IntegralMixedAuxiliaryCandidate.pointAt

theorem radiusSquared_mono {a b : ℕ} (h : a≤b) :
    (BoundedZeroSource.radiusSquared a : ℝ)≤(BoundedZeroSource.radiusSquared b : ℝ) := by
  simp only [BoundedZeroSource.radiusSquared,Int.cast_pow,Int.cast_ofNat]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (Nat.mul_le_mul_left 2 h)

noncomputable def boundedPoint {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (u label : List Bool) (hg : Good hn ht ha u label) (R : ℕ)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R) :
    BoundedZeroSource.Bounded (n := n u) (AuxiliaryCandidateRegularLift.original n t u) R :=
  ⟨(AuxiliaryCandidateRegularLift.boundedPoint hn ht ha u label hg).val,
    (AuxiliaryCandidateRegularLift.boundedPoint hn ht ha u label hg).property.1,
    (AuxiliaryCandidateRegularLift.boundedPoint hn ht ha u label hg).property.2.trans (radiusSquared_mono hR)⟩

theorem coordinate {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (u label : List Bool) (hg : Good hn ht ha u label) (R : ℕ)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R) (i : Fin (n u)) :
    (boundedPoint hn ht ha u label hg R hR).val i=
      IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label (Classical.choose hg) i := rfl

end LeanCanny.Geometry.AuxiliaryCandidateOuterRadius
