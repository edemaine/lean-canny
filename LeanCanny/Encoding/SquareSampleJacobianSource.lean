/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleParameters
public import LeanCanny.Algebra.MvDeterminantBounds
public import LeanCanny.Geometry.PolynomialSystemRegularity
public import LeanCanny.Algebra.PartialDerivativeDegree

/-! # The square system Jacobian and its native bounds

Every system variable is differentiated.
The determinant tests regularity of the actual square system. Its degree,
coefficient mass, and exponent width are derived from the system budgets.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleJacobianSource
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation MvPolynomial
open SquareSampleInput (Inputs)
open SquareSampleSource (count)

open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable def matrix (F : Inputs) (u : List Bool) :
    Matrix (Fin (count F u)) (Fin (count F u)) (MvPolynomial (Fin (count F u)) ℤ) :=
  fun i j => pderiv j (F.system u i)

noncomputable def polynomial (F : Inputs) (u : List Bool) : MvPolynomial (Fin (count F u)) ℤ := (matrix F u).det
noncomputable def degree (F : Inputs) (u : List Bool) : ℕ := count F u * F.degree u
noncomputable def entryMass (F : Inputs) (u : List Bool) : ℕ :=
  (F.degree u).size +
    F.mass u
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ := (count F u).size * count F u + count F u * entryMass F u
noncomputable def width (F : Inputs) (u : List Bool) : ℕ := (degree F u).size

theorem source_degree (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    (F.system u i).totalDegree ≤ F.degree u :=
  F.system_degree u i

theorem entry_degree (F : Inputs) (u : List Bool) (i j : Fin (count F u)) :
    (matrix F u i j).totalDegree ≤ F.degree u :=
  (PartialDerivativeDegree.degree_le _ _).trans ((Nat.sub_le _ _).trans (source_degree F u i))

theorem polynomial_degree (F : Inputs) (u : List Bool) : (polynomial F u).totalDegree ≤ degree F u := by
  simpa only [Fintype.card_fin, polynomial, degree] using MvDeterminantBounds.degree_le _ _ (entry_degree F u)

theorem entry_mass (F : Inputs) (u : List Bool) (i j : Fin (count F u)) :
    MvMass.mass (matrix F u i j) ≤ 2 ^ entryMass F u := by
  apply (MvMass.pderiv_le _ _).trans
  apply (Nat.mul_le_mul (source_degree F u i)
    (F.system_mass u i)).trans
  exact (Nat.mul_le_mul_right _ (Nat.lt_size_self _).le).trans_eq (pow_add _ _ _).symm

theorem polynomial_mass (F : Inputs) (u : List Bool) : MvMass.mass (polynomial F u) ≤ 2 ^ mass F u := by
  simpa only [Fintype.card_fin, polynomial, mass] using MvDeterminantBounds.mass_le_pow _ _ (entry_mass F u)

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) :=
  (BinaryFn.ofUnary (SquareSampleSource.count_unary h)).mul
    (h.degree)
theorem entryMass_binary {F : Inputs} (h : F.Access) : BinaryFn (entryMass F) :=
  (h.degree).size.add
    (h.mass)
theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) :=
  let hn := BinaryFn.ofUnary (SquareSampleSource.count_unary h)
  (hn.size.mul hn).add (hn.mul (entryMass_binary h))
theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  (UnaryFn.length (degree_binary h).bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (degree F u))

theorem degree_lt_width (F : Inputs) (u : List Bool) : degree F u < 2 ^ width F u := Nat.lt_size_self _
theorem source_degree_lt_width (F : Inputs) (u : List Bool) :
    F.degree u < 2 ^ width F u := by
  have hn : 1 ≤ count F u := SquareSampleSource.count_pos F u
  have hd : F.degree u ≤ degree F u := by
    simpa only [one_mul, degree] using Nat.mul_le_mul_right (F.degree u) hn
  exact hd.trans_lt (degree_lt_width F u)

theorem eval_ne_zero_iff (F : Inputs) (u : List Bool) (x : Fin (count F u) → ℝ) :
    (polynomial F u).eval₂ (Int.castRingHom ℝ) x ≠ 0 ↔
      (fderiv ℝ (fun y => fun i => (F.system u i).eval₂ (Int.castRingHom ℝ) y) x).IsInvertible := by
  rw [PolynomialSystemRegularity.isInvertible_iff (Int.castRingHom ℝ) (F.system u) x]
  change (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x) (matrix F u).det ≠ 0 ↔ _
  rw [RingHom.map_det]
  rfl

end LeanCanny.Encoding.SquareSampleJacobianSource
