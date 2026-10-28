/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinateBlockSpecialization
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Compactness and properness of contained coordinate blocks

The free coordinates project continuously from the ambient coordinates.
Every slice preimage lies in the projection of the ambient compact preimage.
Closedness of polynomial preimages therefore transfers compactness, without
any bound on the frozen values or any regularity premise.
-/

@[expose] public section
namespace LeanCanny.Geometry.CoordinateBlockCompactness
open LeanCanny.Algebra MvPolynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {n : ℕ}

theorem compact_preimage (φ : R →+* ℝ) (frozen : ℕ → ℝ) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) (hfit : offset + dim ≤ n) (K : Set ℝ)
    (hK : IsClosed K) (hp : IsCompact ((fun x : Fin n → ℝ => p.eval₂ φ x) ⁻¹' K)) :
    IsCompact ((fun y : Fin dim → ℝ => (CoordinateBlockSpecialization.finite φ frozen offset dim p).eval y) ⁻¹' K) := by
  let project : (Fin n → ℝ) → (Fin dim → ℝ) := fun x i => x ⟨offset + i.val, by omega⟩
  let insert : (Fin dim → ℝ) → (Fin n → ℝ) := fun y i =>
    if hi : offset ≤ i.val ∧ i.val < offset + dim then y ⟨i.val - offset, by omega⟩ else frozen i.val
  have hproject : Continuous project := continuous_pi fun _ => continuous_apply _
  have hleft (y : Fin dim → ℝ) : project (insert y) = y := by
    funext i
    have hi : offset ≤ offset + i.val ∧ offset + i.val < offset + dim := by omega
    dsimp only [project, insert]
    rw [dite_eq_left hi]
    apply congrArg y
    exact Fin.ext (Nat.add_sub_cancel_left _ _)
  have hclosed : IsClosed ((fun y : Fin dim → ℝ =>
      (CoordinateBlockSpecialization.finite φ frozen offset dim p).eval y) ⁻¹' K) :=
    hK.preimage (MvPolynomial.continuous_eval _)
  apply (hp.image hproject).of_isClosed_subset hclosed
  intro y hy
  refine ⟨insert y, ?_, hleft y⟩
  change p.eval₂ φ (insert y) ∈ K
  rw [← CoordinateBlockSpecialization.eval_finite φ frozen offset dim p y]
  exact hy

theorem proper_finite (φ : R →+* ℝ) (frozen : ℕ → ℝ) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) (hfit : offset + dim ≤ n)
    (hp : IsProperMap (fun x : Fin n → ℝ => p.eval₂ φ x)) :
    IsProperMap (fun y : Fin dim → ℝ => (CoordinateBlockSpecialization.finite φ frozen offset dim p).eval y) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨MvPolynomial.continuous_eval _, ?_⟩
  intro K hK
  exact compact_preimage φ frozen offset dim p hfit K hK.isClosed (hp.isCompact_preimage hK)

end LeanCanny.Geometry.CoordinateBlockCompactness
