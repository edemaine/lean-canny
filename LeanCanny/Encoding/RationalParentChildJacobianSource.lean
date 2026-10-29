/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildParameters
public import LeanCanny.Algebra.MvDeterminantBounds
public import LeanCanny.Geometry.PolynomialSystemRegularity
public import LeanCanny.Algebra.PartialDerivativeDegree

/-! # The joint Jacobian polynomial and its native bounds

All variables, including the retained parent parameter, are differentiated.
The determinant tests regularity of the actual joint system. Its degree,
coefficient mass, and exponent width are derived from the original source.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildJacobianSource
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation MvPolynomial
open RationalParentChildSource (Inputs count)
open RationalParentChildParameters (system)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentJointSource.system RationalParentJointSource.degree
  RationalParentJointSource.massExponent

noncomputable def matrix (F : Inputs) (u : List Bool) :
    Matrix (Fin (count F u)) (Fin (count F u)) (MvPolynomial (Fin (count F u)) ℤ) :=
  fun i j => pderiv j (system F u i)

noncomputable def polynomial (F : Inputs) (u : List Bool) : MvPolynomial (Fin (count F u)) ℤ := (matrix F u).det
noncomputable def degree (F : Inputs) (u : List Bool) : ℕ := count F u * RationalParentJointSource.degree F.joint u
noncomputable def entryMass (F : Inputs) (u : List Bool) : ℕ :=
  (RationalParentJointSource.degree F.joint u).size +
    RationalParentJointSource.massExponent F.joint F.directionWidth u
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ := (count F u).size * count F u + count F u * entryMass F u
noncomputable def width (F : Inputs) (u : List Bool) : ℕ := (degree F u).size

theorem source_degree (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    (system F u i).totalDegree ≤ RationalParentJointSource.degree F.joint u :=
  RationalParentJointSource.polynomial_degree _ _ _ _ _ _

theorem entry_degree (F : Inputs) (u : List Bool) (i j : Fin (count F u)) :
    (matrix F u i j).totalDegree ≤ RationalParentJointSource.degree F.joint u :=
  (PartialDerivativeDegree.degree_le _ _).trans ((Nat.sub_le _ _).trans (source_degree F u i))

theorem polynomial_degree (F : Inputs) (u : List Bool) : (polynomial F u).totalDegree ≤ degree F u := by
  simpa only [Fintype.card_fin, polynomial, degree] using MvDeterminantBounds.degree_le _ _ (entry_degree F u)

theorem entry_mass (F : Inputs) (u : List Bool) (i j : Fin (count F u)) :
    MvMass.mass (matrix F u i j) ≤ 2 ^ entryMass F u := by
  apply (MvMass.pderiv_le _ _).trans
  apply (Nat.mul_le_mul (source_degree F u i)
    (RationalParentJointSource.polynomial_mass F.joint F.directionWidth F.direction u (F.pivot u) i)).trans
  exact (Nat.mul_le_mul_right _ (Nat.lt_size_self _).le).trans_eq (pow_add _ _ _).symm

theorem polynomial_mass (F : Inputs) (u : List Bool) : MvMass.mass (polynomial F u) ≤ 2 ^ mass F u := by
  simpa only [Fintype.card_fin, polynomial, mass] using MvDeterminantBounds.mass_le_pow _ _ (entry_mass F u)

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) :=
  (BinaryFn.ofUnary (RationalParentChildSource.count_unary h)).mul
    (RationalParentJointSource.degree_binary h.joint)
theorem entryMass_binary {F : Inputs} (h : F.Access) : BinaryFn (entryMass F) :=
  (RationalParentJointSource.degree_binary h.joint).size.add
    (RationalParentJointSource.massExponent_binary h.joint h.directionWidth)
theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) :=
  let hn := BinaryFn.ofUnary (RationalParentChildSource.count_unary h)
  (hn.size.mul hn).add (hn.mul (entryMass_binary h))
theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  (UnaryFn.length (degree_binary h).bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (degree F u))

theorem degree_lt_width (F : Inputs) (u : List Bool) : degree F u < 2 ^ width F u := Nat.lt_size_self _
theorem source_degree_lt_width (F : Inputs) (u : List Bool) :
    RationalParentJointSource.degree F.joint u < 2 ^ width F u := by
  have hn : 1 ≤ count F u := by unfold count; omega
  have hd : RationalParentJointSource.degree F.joint u ≤ degree F u := by
    simpa only [one_mul, degree] using Nat.mul_le_mul_right (RationalParentJointSource.degree F.joint u) hn
  exact hd.trans_lt (degree_lt_width F u)

theorem eval_ne_zero_iff (F : Inputs) (u : List Bool) (x : Fin (count F u) → ℝ) :
    (polynomial F u).eval₂ (Int.castRingHom ℝ) x ≠ 0 ↔
      (fderiv ℝ (fun y => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) y) x).IsInvertible := by
  rw [PolynomialSystemRegularity.isInvertible_iff (Int.castRingHom ℝ) (system F u) x]
  change (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x) (matrix F u).det ≠ 0 ↔ _
  rw [RingHom.map_det]
  rfl

end LeanCanny.Encoding.RationalParentChildJacobianSource
