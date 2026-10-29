/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineRingGramBounds
public import LeanCanny.Algebra.AffineConstantParameterShift
public import LeanCanny.Geometry.PolynomialCoordinateProper
public import LeanCanny.Geometry.SquarefreeRootFamily
public import LeanCanny.Geometry.SymbolicUnivariateRootFamily
public import LeanCanny.Geometry.PolynomialGridValues

/-! # Proper coordinate grids for varying affine heights

Shifting constants of positive-degree rows preserves infinity exclusion.
The complete Gram coordinate equations consequently have nonvanishing leading
coefficients at every real parameter. Their grid projection is proper and
captures all roots of the shifted original system, including singular roots.
-/

@[expose] public section
namespace LeanCanny.Geometry.AffineShiftCoordinates
open LeanCanny.Algebra MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def coordinate (p : Fin n → MvPolynomial (Fin n) ℤ)
    (c : Fin n → Polynomial ℤ) (d : Fin n → ℕ) (i : Fin n) : Polynomial (Polynomial ℤ) :=
  AffineRingCoordinates.annihilator (AffineConstantParameterShift.system p c) d i

lemma coordinate_degree_le (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (d : Fin n → ℕ) (i : Fin n) :
    (coordinate p c d i).natDegree ≤ AffineRingCoordinates.dimension d + 1 :=
  AffineRingCoordinates.degree_le _ d i

lemma coordinate_parameter_degree_le (p : Fin n → MvPolynomial (Fin n) ℤ)
    (c : Fin n → Polynomial ℤ) (d : Fin n → ℕ) (E : ℕ)
    (hc : ∀ i, (c i).natDegree ≤ E) (i : Fin n) (k : ℕ) :
    ((coordinate p c d i).coeff k).natDegree ≤ AffineRingCoordinates.dimension d * E := by
  apply AffineRingCoordinates.annihilator_inner_degree
  intro j e
  exact (AffineConstantParameterShift.parameter_degree_le p c j e).trans (hc j)

noncomputable def rows (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (i : Fin n) : MvPolynomial (Fin n) (Polynomial ℝ) :=
  (AffineConstantParameterShift.system p c i).map (Polynomial.mapRingHom (Int.castRingHom ℝ))

lemma positive_leading (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (hp : AffineFiniteCoordinates.NoInfinity p d)
    (i : Fin n) (t : ℝ) :
    0 < SymbolicScaledSquarefree.scalarEvaluation t (coordinate p c d i).leadingCoeff := by
  exact (AffineRingCoordinates.exact_degree_and_positive_leading
    (SymbolicScaledSquarefree.scalarEvaluation t) (AffineConstantParameterShift.system p c) d hd
    (AffineConstantParameterShift.noInfinity p c d hd hp _) i).2

lemma coordinate_ne_zero (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (hp : AffineFiniteCoordinates.NoInfinity p d)
    (i : Fin n) : coordinate p c d i ≠ 0 := by
  intro hz
  have h := positive_leading p c d hd hp i 0
  rw [hz, Polynomial.leadingCoeff_zero, map_zero] at h
  exact (lt_irrefl 0) h

lemma proper (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (hp : AffineFiniteCoordinates.NoInfinity p d) :
    IsProperMap (RootProjection.projection (SquarefreeRootFamily.value (coordinate p c d))) := by
  apply PolynomialCoordinateProper.proper (fun i => SquarefreeRootFamily.realPolynomial (coordinate p c d i))
  intro i t
  have h := positive_leading p c d hd hp i t
  rw [SquarefreeRootFamily.realPolynomial, Polynomial.leadingCoeff_map_of_injective
    (Polynomial.map_injective _ (Int.cast_injective (α := ℝ)))]
  change ((coordinate p c d i).leadingCoeff.map (Int.castRingHom ℝ)).eval t ≠ 0
  rw [Polynomial.eval_map]
  exact ne_of_gt h

lemma value_rows (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    PolynomialGridValues.value (rows p c) (t, x) i =
      (p i).eval₂ (Int.castRingHom ℝ) x - SymbolicScaledSquarefree.scalarEvaluation t (c i) := by
  change ((AffineConstantParameterShift.system p c i).map _).eval₂ (Polynomial.evalRingHom t) x = _
  rw [MvPolynomial.eval₂_map, SymbolicUnivariateRootFamily.evaluation_comp,
    AffineConstantParameterShift.eval]

lemma roots_iff (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (t : ℝ) (x : Fin n → ℝ) :
    PolynomialGridValues.value (rows p c) (t, x) = 0 ↔
      ∀ i, (p i).eval₂ (Int.castRingHom ℝ) x = SymbolicScaledSquarefree.scalarEvaluation t (c i) := by
  simp only [funext_iff, value_rows, Pi.zero_apply, sub_eq_zero]

lemma capture (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (d : Fin n → ℕ) (hdeg : ∀ i, (p i).totalDegree ≤ d i) (t : ℝ) (x : Fin n → ℝ)
    (hx : PolynomialGridValues.value (rows p c) (t, x) = 0) :
    SquarefreeRootFamily.value (coordinate p c d) (t, x) = 0 := by
  funext i
  rw [SquarefreeRootFamily.value_apply, Pi.zero_apply]
  apply AffineRingCoordinates.eval_eq_zero _ _ _ (AffineConstantParameterShift.degree_le p c d hdeg)
  intro j
  have h := congrFun hx j
  change ((AffineConstantParameterShift.system p c j).map _).eval₂ (Polynomial.evalRingHom t) x = 0 at h
  rwa [MvPolynomial.eval₂_map, SymbolicUnivariateRootFamily.evaluation_comp] at h

end LeanCanny.Geometry.AffineShiftCoordinates
