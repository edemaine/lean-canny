/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleCoordinates
public import LeanCanny.Geometry.RegularAffineSubsetCount

/-! # Exact regular-root parameters for the complete flat tower

The primitive parameter contains coordinate-root tuples that need not solve
the flat equations. Requiring those equations and an invertible Jacobian
selects precisely the regular roots. Padding introduces no extra accepted
point: projection gives a bijection with regular roots of the original tower.
The number of accepted parameters has a native polynomial label-width bound.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleParameters
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatFullSourceTower (Inputs)
open FlatFullSourceSampleCoordinates (parameter coordinate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourcePositive.system FlatFullSourceTower.system parameter coordinate

noncomputable def decode (F : Inputs) (u : List Bool) (theta : ℝ) :
    Fin (FlatFullSourceSampleSource.count F u) → ℝ :=
  fun i => (coordinate F (pair u (BinaryNatCode.encode i.val))).eval theta

abbrev Candidates (F : Inputs) (u : List Bool) :=
  RegularAffineRootCount.RegularRoots (FlatFullSourcePositive.system F u)
abbrev OriginalCandidates (F : Inputs) (u : List Bool) :=
  RegularAffineRootCount.RegularRoots (FlatFullSourceTower.system F u)

def RegularParameters (F : Inputs) (u : List Bool) :=
  {theta : ℝ // (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
    (∀ i, (FlatFullSourcePositive.system F u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0) ∧
    (fderiv ℝ (fun z => fun i => (FlatFullSourcePositive.system F u i).eval₂ (Int.castRingHom ℝ) z)
      (decode F u theta)).IsInvertible}

noncomputable def candidate (F : Inputs) (u : List Bool) (theta : RegularParameters F u) : Candidates F u :=
  ⟨⟨decode F u theta.val, theta.property.2.1⟩, theta.property.2.2⟩

theorem candidate_injective (F : Inputs) (u : List Bool) : Function.Injective (candidate F u) := by
  intro theta theta' he
  apply Subtype.ext
  apply FlatFullSourceSampleCoordinates.parameter_roots_ext F u theta.val theta'.val theta.property.1 theta'.property.1
  intro i
  exact congrFun (congrArg (fun z : Candidates F u => z.val.val) he) i

theorem candidate_surjective (F : Inputs) (u : List Bool) : Function.Surjective (candidate F u) := by
  intro z
  obtain ⟨theta, ht, hx⟩ := FlatFullSourceSampleCoordinates.regular_root_complete F u z.val.val z.val.property z.property
  have he : decode F u theta = z.val.val := funext fun i => (hx i).2
  have hz : ∀ i, (FlatFullSourcePositive.system F u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0 := by
    rw [he]
    exact z.val.property
  have hr : (fderiv ℝ (fun y => fun i => (FlatFullSourcePositive.system F u i).eval₂ (Int.castRingHom ℝ) y)
      (decode F u theta)).IsInvertible := by rw [he]; exact z.property
  refine ⟨⟨theta, ht, hz, hr⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he

noncomputable def regularEquiv (F : Inputs) (u : List Bool) : RegularParameters F u ≃ Candidates F u :=
  Equiv.ofBijective (candidate F u) ⟨candidate_injective F u, candidate_surjective F u⟩

noncomputable def padded (F : Inputs) (u : List Bool) (z : OriginalCandidates F u) : Candidates F u := by
  have he : PositivePolynomialSystem.extend z.val.val ∘ Fin.castSucc = z.val.val :=
    funext (PositivePolynomialSystem.extend_old z.val.val)
  refine ⟨⟨PositivePolynomialSystem.extend z.val.val,
    (FlatFullSourcePositive.roots_extend_iff (Int.castRingHom ℝ) F u z.val.val).mpr z.val.property⟩, ?_⟩
  apply (FlatFullSourcePositive.analytic_regular_iff F u (PositivePolynomialSystem.extend z.val.val)).mpr
  have hr := z.property
  rw [← he] at hr
  exact hr

noncomputable def unpadded (F : Inputs) (u : List Bool) (z : Candidates F u) : OriginalCandidates F u :=
  ⟨⟨z.val.val ∘ Fin.castSucc, (FlatFullSourcePositive.roots_iff (Int.castRingHom ℝ) F u z.val.val).mp z.val.property |>.1⟩,
    (FlatFullSourcePositive.analytic_regular_iff F u z.val.val).mp z.property⟩

noncomputable def paddingEquiv (F : Inputs) (u : List Bool) : OriginalCandidates F u ≃ Candidates F u where
  toFun := padded F u
  invFun := unpadded F u
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact PositivePolynomialSystem.extend_old z.val.val i
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact FlatFullSourcePositive.extension_unique (Int.castRingHom ℝ) F u z.val.val z.val.property

noncomputable def originalEquiv (F : Inputs) (u : List Bool) : RegularParameters F u ≃ OriginalCandidates F u :=
  (regularEquiv F u).trans (paddingEquiv F u).symm

noncomputable def labelWidth (F : Inputs) (u : List Bool) : ℕ :=
  RegularAffineRootCount.labelWidth (FlatFullSourcePositive.count F u) (FlatFullSourceTower.degree F u)

theorem labelWidth_unary {F : Inputs} (h : F.Access) : UnaryFn (labelWidth F) :=
  ((FlatFullSourcePositive.count_unary h).mul ((FlatFullSourcePositive.count_unary h).add (UnaryFn.const 1))).mul
    (FlatFullSourcePositiveCoordinate.width_unary h)

theorem finite_regular_parameters (F : Inputs) (u : List Bool) :
    Finite (RegularParameters F u) ∧ Nat.card (RegularParameters F u) ≤ 2 ^ labelWidth F u := by
  have H := RegularAffineRootCount.finite_regular_card_le_uniform (FlatFullSourcePositive.system F u)
    (FlatFullSourceTower.degree F u) (FlatFullSourcePositive.polynomial_degree F u) (FlatFullSourceTower.degree_pos F u)
  let _ : Finite (Candidates F u) := H.1
  exact ⟨Finite.of_injective (candidate F u) (candidate_injective F u),
    (Nat.card_congr (regularEquiv F u)).trans_le H.2⟩

end LeanCanny.Encoding.FlatFullSourceSampleParameters
