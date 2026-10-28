/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleJointCoefficient
public import LeanCanny.Geometry.RegularAffineRootCount
public import LeanCanny.Geometry.RegularAffineSubsetCount

/-! # Roots and regularity of the joint child-sample candidate system

At an actual parent sample, the joint roots are exactly the block critical
points. Parent separability reduces joint regularity to spatial regularity.
The regular candidate subset is finite with the constructed label allowance,
even when other candidate fibers contain positive-dimensional root families.
A separate all-fiber regularity premise gives the same bound for every root.
Good-direction selection and completeness for intended children remain open.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleJointGeometry
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MvPolynomial
open BoundedCriticalSampleJointSource
open scoped Classical
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter
  BoundedCriticalSampleBlockTerm.polynomial BoundedCriticalSampleBlockCriticalSource.polynomial

noncomputable def spatial (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) (t : ℝ) :
    Fin (k u) → MvPolynomial (Fin (k u)) ℝ :=
  ProjectionCriticalFamily.spatialEquation
    (ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) t
      (BoundedCriticalSampleBlockTerm.polynomial P read o k u)) b
    (fun j => (BoundedCriticalSampleBlockCriticalSource.direction k w bits u j : ℝ))

theorem root_iff (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) (t : ℝ) (y : Fin (k u) → ℝ) :
    (∀ i, (system P read o k w bits u b i).eval₂ (Int.castRingHom ℝ) (Fin.cons t y) = 0) ↔
      (BoundedCriticalRationalCoordinates.parameter P (pairFst u)).eval₂ (Int.castRingHom ℝ) t = 0 ∧
        ∀ i, (spatial P read o k w bits u b t i).eval y = 0 := by
  rw [system, RetainedParameterSystem.zero_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  rw [← ParameterSpatialSpecialization.eval_specialize,
    BoundedCriticalSampleBlockCriticalSource.specialize_polynomial]
  rfl

theorem sample_packet (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (b : Fin (k (pair c r))) (y : Fin (k (pair c r)) → ℝ) :
    (∀ i, (system P read o k w bits (pair c r) b i).eval₂ (Int.castRingHom ℝ)
      (Fin.cons (BoundedCriticalSampleLabels.parameter P c x).val y) = 0) ↔
        ∀ i, (ProjectionCriticalFamily.spatialEquation
          (BoundedCriticalSampleBlockCriticalGeometry.samplePolynomial P read o k c r x) b
          (fun j => (BoundedCriticalSampleBlockCriticalSource.direction k w bits (pair c r) j : ℝ)) i).eval y = 0 := by
  have ht := ((BoundedCriticalSampleLabels.mem_rootSet P c _).mp
    (BoundedCriticalSampleLabels.parameter P c x).property).1
  rw [root_iff, pairFst_pair, and_iff_right ht]
  rfl

theorem regular_at_parameter_root (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) (t : ℝ) (y : Fin (k u) → ℝ)
    (ht : (BoundedCriticalRationalCoordinates.parameter P (pairFst u)).eval₂ (Int.castRingHom ℝ) t = 0) :
    (fderiv ℝ (fun z => fun i => (system P read o k w bits u b i).eval₂ (Int.castRingHom ℝ) z)
      (Fin.cons t y)).IsInvertible ↔
        (fderiv ℝ (fun z => fun i => (spatial P read o k w bits u b t i).eval z) y).IsInvertible := by
  have H := RetainedParameterSystem.regular_iff (BoundedCriticalRationalCoordinates.parameter P (pairFst u))
    (fun i => BoundedCriticalSampleBlockCriticalSource.polynomial P read o k w bits u b i) t y
    (BoundedCriticalRationalCoordinates.parameter_derivative_ne_zero P (pairFst u) t ht)
  simpa only [system, spatial, BoundedCriticalSampleBlockCriticalSource.specialize_polynomial] using H

theorem finite_card_le (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u))
    (hregular : ∀ (t : ℝ) (y : Fin (k u) → ℝ),
      (BoundedCriticalRationalCoordinates.parameter P (pairFst u)).eval₂ (Int.castRingHom ℝ) t = 0 →
        (∀ i, (spatial P read o k w bits u b t i).eval y = 0) →
          (fderiv ℝ (fun z => fun i => (spatial P read o k w bits u b t i).eval z) y).IsInvertible) :
    Finite (Geometry.RegularAffineRootCount.Roots (system P read o k w bits u b)) ∧
      Nat.card (Geometry.RegularAffineRootCount.Roots (system P read o k w bits u b)) ≤
        2 ^ labelWidth P read k u := by
  apply Geometry.RegularAffineRootCount.finite_card_le_uniform (system P read o k w bits u b) (degree P read u)
    (polynomial_degree P read o k w bits u b) (degree_pos P read u)
  intro z
  let t := z.val 0
  let y := fun i : Fin (k u) => z.val i.succ
  have he : Fin.cons t y = z.val := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hz : ∀ i, (system P read o k w bits u b i).eval₂ (Int.castRingHom ℝ) (Fin.cons t y) = 0 := by
    rw [he]
    exact z.property
  have H := (root_iff P read o k w bits u b t y).mp hz
  have hr := (regular_at_parameter_root P read o k w bits u b t y H.1).mpr (hregular t y H.1 H.2)
  simpa only [he] using hr

/-- Regular candidates are finite even if extraneous parent fibers contain
singular or positive-dimensional sets. Good directions are needed later to
show that all intended child critical points belong to this family. -/
abbrev RegularCandidates (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) :=
  Geometry.RegularAffineRootCount.RegularRoots (system P read o k w bits u b)

theorem finite_regular_candidates (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) :
    Finite (RegularCandidates P read o k w bits u b) ∧
      Nat.card (RegularCandidates P read o k w bits u b) ≤ 2 ^ labelWidth P read k u :=
  Geometry.RegularAffineRootCount.finite_regular_card_le_uniform (system P read o k w bits u b) (degree P read u)
    (polynomial_degree P read o k w bits u b) (degree_pos P read u)

theorem regular_candidate_at_sample (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (b : Fin (k (pair c r))) (y : Fin (k (pair c r)) → ℝ)
    (hy : ∀ i, (spatial P read o k w bits (pair c r) b (BoundedCriticalSampleLabels.parameter P c x).val i).eval y = 0)
    (hregular : (fderiv ℝ (fun z => fun i =>
      (spatial P read o k w bits (pair c r) b (BoundedCriticalSampleLabels.parameter P c x).val i).eval z) y).IsInvertible) :
    ∃ z : RegularCandidates P read o k w bits (pair c r) b,
      z.val.val = Fin.cons (BoundedCriticalSampleLabels.parameter P c x).val y := by
  have ht := ((BoundedCriticalSampleLabels.mem_rootSet P c _).mp
    (BoundedCriticalSampleLabels.parameter P c x).property).1
  have ht' : (BoundedCriticalRationalCoordinates.parameter P (pairFst (pair c r))).eval₂ (Int.castRingHom ℝ)
      (BoundedCriticalSampleLabels.parameter P c x).val = 0 := by rw [pairFst_pair]; exact ht
  have hz := (root_iff P read o k w bits (pair c r) b _ y).mpr ⟨ht', hy⟩
  have hr := (regular_at_parameter_root P read o k w bits (pair c r) b _ y ht').mpr hregular
  exact ⟨⟨⟨_, hz⟩, hr⟩, rfl⟩

end LeanCanny.Encoding.BoundedCriticalSampleJointGeometry
