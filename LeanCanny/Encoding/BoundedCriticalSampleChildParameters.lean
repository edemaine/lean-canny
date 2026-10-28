/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildCoordinates

/-! # Exact parameter encodings of regular child candidates

The joint equations and Jacobian condition select precisely the regular
candidates among the child parameter roots. The correspondence is bijective,
including when there are no regular candidates. Native filtering and
selection of the actual parent root remain separate obligations.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildParameters
open LeanCanny.Algebra LeanCanny.Geometry
open BoundedCriticalSampleChildSource (Inputs)
open BoundedCriticalSampleChildCoordinates (parameter coordinate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleJointSource.system parameter coordinate

noncomputable def decode (F : Inputs) (u : List Bool) (theta : ℝ) :
    Fin (BoundedCriticalSampleChildSource.count F u) → ℝ :=
  fun i => (coordinate F (pair u (BinaryNatCode.encode i.val))).eval theta

noncomputable def system (F : Inputs) (u : List Bool) :=
  BoundedCriticalSampleJointSource.system F.parent F.term F.offset F.dim F.directionWidth F.direction u (F.pivot u)

abbrev Candidates (F : Inputs) (u : List Bool) :=
  BoundedCriticalSampleJointGeometry.RegularCandidates F.parent F.term F.offset F.dim F.directionWidth F.direction u (F.pivot u)

def RegularParameters (F : Inputs) (u : List Bool) :=
  {theta : ℝ // (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
    (∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0) ∧
    (fderiv ℝ (fun z => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) z) (decode F u theta)).IsInvertible}

noncomputable def candidate (F : Inputs) (u : List Bool) (theta : RegularParameters F u) : Candidates F u :=
  ⟨⟨decode F u theta.val, theta.property.2.1⟩, theta.property.2.2⟩

theorem candidate_injective (F : Inputs) (u : List Bool) : Function.Injective (candidate F u) := by
  intro theta theta' he
  apply Subtype.ext
  apply BoundedCriticalSampleChildCoordinates.parameter_roots_ext F u theta.val theta'.val theta.property.1 theta'.property.1
  intro i
  exact congrFun (congrArg (fun z : Candidates F u => z.val.val) he) i

theorem candidate_surjective (F : Inputs) (u : List Bool) : Function.Surjective (candidate F u) := by
  intro z
  obtain ⟨theta, ht, hx⟩ := BoundedCriticalSampleChildCoordinates.regular_candidate_complete F u z
  have he : decode F u theta = z.val.val := funext fun i => (hx i).2
  have hz : ∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0 := by
    rw [he]
    exact z.val.property
  have hr : (fderiv ℝ (fun y => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) y)
      (decode F u theta)).IsInvertible := by rw [he]; exact z.property
  refine ⟨⟨theta, ht, hz, hr⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he

noncomputable def regularEquiv (F : Inputs) (u : List Bool) : RegularParameters F u ≃ Candidates F u :=
  Equiv.ofBijective (candidate F u) ⟨candidate_injective F u, candidate_surjective F u⟩

theorem finite_regular_parameters (F : Inputs) (u : List Bool) :
    Finite (RegularParameters F u) ∧ Nat.card (RegularParameters F u) ≤
      2 ^ BoundedCriticalSampleJointSource.labelWidth F.parent F.term F.dim u := by
  have H := BoundedCriticalSampleJointGeometry.finite_regular_candidates F.parent F.term F.offset F.dim F.directionWidth
    F.direction u (F.pivot u)
  let _ : Finite (Candidates F u) := H.1
  exact ⟨Finite.of_injective (candidate F u) (candidate_injective F u),
    (Nat.card_congr (regularEquiv F u)).trans_le H.2⟩

end LeanCanny.Encoding.BoundedCriticalSampleChildParameters
