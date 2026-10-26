/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.BoundedZeroSource
public import LeanCanny.Geometry.CircleSublevelLift

/-! # Component preservation for the bounded polynomial source

The source zero set projects onto the original polynomial zeros in a closed
ball. Explicit coordinate and subtype homeomorphisms identify its fibers
with circles, including singleton boundary fibers. Its quotient projection
therefore preserves components and whole-space preconnectedness.
-/

@[expose] public section
namespace LeanCanny.Geometry.BoundedZeroSource
open MvPolynomial Set

variable {n : ℕ}

noncomputable def coordinates : (Fin n → ℝ) × ℂ ≃ₜ (Fin (n + 2) → ℝ) :=
  ((Homeomorph.refl (Fin n → ℝ)).prodCongr
    (Complex.equivRealProdCLM.toHomeomorph.trans (Homeomorph.finTwoArrow (X := ℝ)).symm)).trans
    (Fin.appendHomeomorph n 2)

theorem coordinates_apply (p : (Fin n → ℝ) × ℂ) :
    coordinates p = Fin.append p.1 ![p.2.re, p.2.im] := rfl

theorem radial_coordinates (p : (Fin n → ℝ) × ℂ) :
    radial (coordinates p) = radial p.1 + Complex.normSq p.2 := by
  simp [radial, coordinates_apply, Fin.sum_univ_add, Complex.normSq_apply, pow_two]

theorem power_sum_coordinates (N : ℕ) (p : (Fin n → ℝ) × ℂ) :
    (∑ i : Fin (n + 2), coordinates p i ^ N) = (∑ i : Fin n, p.1 i ^ N) + p.2.re ^ N + p.2.im ^ N := by
  change (∑ i : Fin (n + 2), Fin.append p.1 ![p.2.re, p.2.im] i ^ N) = _
  rw [Fin.sum_univ_add (a := n) (b := 2)]
  simp [Fin.sum_univ_two, add_assoc]

noncomputable def Original (q : MvPolynomial (Fin n) ℤ) := {x : Fin n → ℝ | q.eval₂ (Int.castRingHom ℝ) x = 0}
noncomputable def Zeros (q : MvPolynomial (Fin n) ℤ) (R : ℕ) :=
  {w : Fin (n + 2) → ℝ | (polynomial q R).eval₂ (Int.castRingHom ℝ) w = 0}
noncomputable def Bounded (q : MvPolynomial (Fin n) ℤ) (R : ℕ) :=
  {x : Fin n → ℝ | q.eval₂ (Int.castRingHom ℝ) x = 0 ∧ radial x ≤ (radiusSquared R : ℝ)}
noncomputable def radialOn (q : MvPolynomial (Fin n) ℤ) (x : Original q) : ℝ := radial x.val
noncomputable def Joint (q : MvPolynomial (Fin n) ℤ) (R : ℕ) :=
  {p : (Fin n → ℝ) × ℂ | q.eval₂ (Int.castRingHom ℝ) p.1 = 0 ∧
    radial p.1 + Complex.normSq p.2 = (radiusSquared R : ℝ)}

theorem continuous_radialOn (q : MvPolynomial (Fin n) ℤ) : Continuous (radialOn q) :=
  (continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)).comp continuous_subtype_val

theorem zero_coordinates (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (p : (Fin n → ℝ) × ℂ) :
    coordinates p ∈ Zeros q R ↔ p ∈ Joint q R := by
  change (polynomial q R).eval₂ (Int.castRingHom ℝ) (coordinates p) = 0 ↔ _
  rw [zero_iff, radial_coordinates]
  simp only [coordinates_apply, Fin.append_left]
  rfl

noncomputable def jointHomeomorph (q : MvPolynomial (Fin n) ℤ) (R : ℕ) :
    Joint q R ≃ₜ CircleSublevelLift.Total (radialOn q) (radiusSquared R : ℝ) where
  toFun p := ⟨(⟨p.val.1, p.property.1⟩, p.val.2), p.property.2⟩
  invFun p := ⟨(p.val.1.val, p.val.2), p.val.1.property, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)

noncomputable def zeroHomeomorph (q : MvPolynomial (Fin n) ℤ) (R : ℕ) :
    Zeros q R ≃ₜ CircleSublevelLift.Total (radialOn q) (radiusSquared R : ℝ) :=
  (coordinates.symm.sets (by
    ext w
    change (w ∈ Zeros q R) ↔ coordinates.symm w ∈ Joint q R
    have h := zero_coordinates q R (coordinates.symm w)
    simpa only [Homeomorph.apply_symm_apply] using h)).trans (jointHomeomorph q R)

noncomputable def baseHomeomorph (q : MvPolynomial (Fin n) ℤ) (R : ℕ) :
    CircleSublevelLift.Base (radialOn q) (radiusSquared R : ℝ) ≃ₜ Bounded q R where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

noncomputable def projection (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (w : Zeros q R) : Bounded q R :=
  baseHomeomorph q R (CircleSublevelLift.projection (radialOn q) (radiusSquared R : ℝ) (zeroHomeomorph q R w))

noncomputable def sectionMap (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (x : Bounded q R) : Zeros q R :=
  (zeroHomeomorph q R).symm (CircleSublevelLift.sectionMap (radialOn q) (radiusSquared R : ℝ)
    ((baseHomeomorph q R).symm x))

theorem projection_section (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (x : Bounded q R) :
    projection q R (sectionMap q R x) = x := by
  simp only [projection, sectionMap, Homeomorph.apply_symm_apply, CircleSublevelLift.projection_section]

theorem quotient_projection (q : MvPolynomial (Fin n) ℤ) (R : ℕ) :
    Topology.IsQuotientMap (projection q R) :=
  (baseHomeomorph q R).isQuotientMap.comp
    ((CircleSublevelLift.quotient_projection (radialOn q) (continuous_radialOn q) (radiusSquared R : ℝ)).comp
      (zeroHomeomorph q R).isQuotientMap)

theorem fiber_connected (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (x : Bounded q R) :
    IsConnected ((projection q R) ⁻¹' {x}) := by
  have he : (projection q R) ⁻¹' {x} = (zeroHomeomorph q R) ⁻¹'
      ((CircleSublevelLift.projection (radialOn q) (radiusSquared R : ℝ)) ⁻¹' {(baseHomeomorph q R).symm x}) := by
    ext w
    change (baseHomeomorph q R) (CircleSublevelLift.projection _ _ (zeroHomeomorph q R w)) = x ↔ _
    constructor
    · intro h
      apply (baseHomeomorph q R).injective
      simpa only [Homeomorph.apply_symm_apply] using h
    · intro h
      rw [show CircleSublevelLift.projection _ _ (zeroHomeomorph q R w) = (baseHomeomorph q R).symm x from h,
        Homeomorph.apply_symm_apply]
  rw [he]
  exact (zeroHomeomorph q R).isConnected_preimage.mpr (CircleSublevelLift.fiber_connected _ _ _)

theorem component_preimage (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (w : Zeros q R) :
    (projection q R) ⁻¹' connectedComponent (projection q R w) = connectedComponent w :=
  (quotient_projection q R).isCoinducing.preimage_connectedComponent (fiber_connected q R) w

theorem section_component_iff (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (x y : Bounded q R) :
    sectionMap q R y ∈ connectedComponent (sectionMap q R x) ↔
      y.val ∈ connectedComponentIn (Bounded q R) x.val := by
  rw [← component_preimage, mem_preimage, projection_section, projection_section,
    connectedComponentIn_eq_image x.property]
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨z, hz, he⟩
    exact (Subtype.ext he : z = y) ▸ hz

theorem preconnected_iff (q : MvPolynomial (Fin n) ℤ) (R : ℕ) :
    IsPreconnected (Zeros q R) ↔ IsPreconnected (Bounded q R) := by
  rw [isPreconnected_iff_preconnectedSpace, isPreconnected_iff_preconnectedSpace,
    preconnectedSpace_iff_connectedComponent, preconnectedSpace_iff_connectedComponent]
  constructor
  · intro h x
    apply eq_univ_of_univ_subset
    intro y _
    have hm : sectionMap q R y ∈ connectedComponent (sectionMap q R x) := by rw [h _]; exact mem_univ _
    have ht : projection q R (sectionMap q R y) ∈ connectedComponent (projection q R (sectionMap q R x)) := by
      rw [← mem_preimage, component_preimage]
      exact hm
    simpa only [projection_section] using ht
  · intro h w
    apply eq_univ_of_univ_subset
    intro v _
    rw [← component_preimage]
    change projection q R v ∈ connectedComponent (projection q R w)
    rw [h _]
    exact mem_univ _

end LeanCanny.Geometry.BoundedZeroSource
