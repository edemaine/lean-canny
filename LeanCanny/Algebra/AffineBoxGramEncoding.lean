/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineBoxGramEliminant
public import LeanCanny.Algebra.PolynomialReflectSpace

/-! # Encoding the reciprocal Gram determinant in the existing backend

The univariate reciprocal parameter occupies the outer parameter of the
canonical nested determinant. The inner parameter is constant. Fixed-degree
reflection transports native coefficient access to the all-root annihilator.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineBoxGramEliminant
open ProjectiveGramEliminant
open LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def liftParameter : Polynomial ℤ →+* Polynomial (Polynomial ℤ) :=
  Polynomial.mapRingHom Polynomial.C

noncomputable def liftedSystem (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (coordinate : Fin (n + 1)) (j : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) (Polynomial (Polynomial ℤ)) :=
  (system H coordinate j).map liftParameter

lemma polynomial_lift (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    ProjectiveBoxGramEliminant.polynomial (liftedSystem H coordinate) (degrees d) W =
      liftParameter (polynomial H d W coordinate) := by
  rw [ProjectiveBoxGramEliminant.polynomial]
  change (gram (MacaulayFullBox.matrix (fun j => (system H coordinate j).map liftParameter) (degrees d) W)).det = _
  rw [← MacaulayFullBox.matrix_map, ← gram_map]
  exact (RingHom.map_det liftParameter _).symm

lemma lift_coefficient (p : Polynomial ℤ) (u v : ℕ) :
    ((liftParameter p).coeff v).coeff u = if u = 0 then p.coeff v else 0 := by
  simp only [liftParameter, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_C]

lemma coefficient_eq_nested (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) (j : ℕ) :
    (annihilator H d W coordinate).coeff j =
      if 0 < j ∧ j ≤ dimension n W + 1 then
        ((ProjectiveBoxGramEliminant.polynomial (liftedSystem H coordinate) (degrees d) W).coeff
          (dimension n W + 1 - j)).coeff 0 else 0 := by
  rw [polynomial_lift, lift_coefficient, ite_eq_left rfl]
  exact PolynomialReflectBits.coefficient_eq _ _ (degree_le H d W coordinate) j

/-- The backend's auxiliary parameter has degree zero in every source entry. -/
lemma inner_degree (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (coordinate : Fin (n + 1)) (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) (v : ℕ) :
    (((liftedSystem H coordinate j).coeff e).coeff v).natDegree ≤ 0 := by
  simp only [liftedSystem, MvPolynomial.coeff_map, liftParameter, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map, Polynomial.natDegree_C, le_refl]

/-- Once the canonical Gram reader is built from its source rows, reflection
adds only FP packet handling. All original coefficient-reader costs remain. -/
theorem annihilator_evaluator (n : List Bool → ℕ)
    (H : (c : List Bool) → Fin (n c) → MvPolynomial (Fin (n c + 1)) ℤ)
    (d : (c : List Bool) → Fin (n c) → ℕ) (W : List Bool → ℕ)
    (coordinate : (c : List Bool) → Fin (n c + 1))
    (hN : BinaryFn (fun c => dimension (n c) (W c)))
    (E : SpaceFunction (PrimitivePairBits.coefficient (fun c => polynomial (H c) (d c) (W c) (coordinate c)))) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => annihilator (H c) (d c) (W c) (coordinate c))) :=
  PolynomialReflectBits.evaluator (fun c => polynomial (H c) (d c) (W c) (coordinate c))
    (fun c => dimension (n c) (W c)) (fun c => degree_le (H c) (d c) (W c) (coordinate c)) hN E

end LeanCanny.Algebra.AffineBoxGramEliminant
