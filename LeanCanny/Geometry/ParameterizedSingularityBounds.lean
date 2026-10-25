/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerParameterFlatten
public import LeanCanny.Geometry.SingularParameterBounds

/-! # Bounded regularity factors over the integer parameter ring

Replacing the retained parameter with one integer polynomial variable
transfers the exceptional-factor construction to the original parameter-ring
equations and their formal spatial Jacobian. The supplied qualitative factor
needs no degree or coefficient bound.
-/

@[expose] public section
namespace LeanCanny.Geometry.ParameterizedSingularityBounds
open scoped Classical
open MvPolynomial LeanCanny.Algebra
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

noncomputable def jacobian (q : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) :
    MvPolynomial (Fin n) (Polynomial ℤ) := Matrix.det (fun i j => pderiv j (q i))

theorem eval_jacobian (q : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (z : Fin (n + 1) → ℝ) :
    (SingularParameterBounds.jacobian (fun i => IntegerParameterFlatten.flatten (q i))).eval₂
        (Int.castRingHom ℝ) z =
      (jacobian q).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (z 0)) (fun i => z i.succ) := by
  rw [SingularParameterBounds.jacobian, ← IntegerParameterFlatten.flatten_det_pderiv,
    IntegerParameterFlatten.eval_flatten]
  rfl

def degreeBound (n D E : ℕ) : ℕ :=
  CoerciveCoordinateEliminant.columnBound (n + 1) (2 * SingularParameterBounds.systemDegree n (E + D))

def massExponent (n D E b : ℕ) : ℕ :=
  SingularParameterBounds.factorMassExponent n (E + D) (IntegerParameterFlatten.massExponent n D b)

theorem exists_bounded (q : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (D E b : ℕ)
    (hD : ∀ i, (q i).totalDegree ≤ D)
    (hE : ∀ i e, ((q i).coeff e).natDegree ≤ E)
    (hb : ∀ i e, coefficientMass ((q i).coeff e) ≤ 2 ^ b)
    (d : Polynomial ℤ) (hd : d ≠ 0)
    (hgeneric : ∀ (t : ℝ) (x : Fin n → ℝ),
      (∀ j, (q j).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) x = 0) →
      d.eval₂ (Int.castRingHom ℝ) t ≠ 0 →
        (jacobian q).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) x ≠ 0) :
    ∃ r : Polynomial ℤ, r ≠ 0 ∧ r.natDegree ≤ degreeBound n D E ∧
      coefficientMass r < 2 ^ massExponent n D E b ∧
      ∀ (t : ℝ) (x : Fin n → ℝ),
        (∀ j, (q j).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) x = 0) →
        r.eval₂ (Int.castRingHom ℝ) t ≠ 0 →
          (jacobian q).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) x ≠ 0 := by
  let Q := fun i => IntegerParameterFlatten.flatten (q i)
  have hQD (i : Fin n) : (Q i).totalDegree ≤ E + D :=
    IntegerParameterFlatten.flatten_degree (q i) D E (hD i) (hE i)
  have hQb (i : Fin n) : MvMass.mass (Q i) ≤ 2 ^ IntegerParameterFlatten.massExponent n D b :=
    IntegerParameterFlatten.flatten_mass_pow (q i) D b (hD i) (hb i)
  have hdR : d.map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)).mpr hd
  have hgood (z : Fin (n + 1) → ℝ)
      (hz : ∀ j, (Q j).eval₂ (Int.castRingHom ℝ) z = 0)
      (hdz : (d.map (Int.castRingHom ℝ)).eval (z 0) ≠ 0) :
      (SingularParameterBounds.jacobian Q).eval₂ (Int.castRingHom ℝ) z ≠ 0 := by
    rw [eval_jacobian]
    apply hgeneric
    · intro j
      simpa only [Q, IntegerParameterFlatten.eval_flatten] using hz j
    · simpa only [Polynomial.eval_map] using hdz
  obtain ⟨r, hr, hdeg, hmass, hregular⟩ := SingularParameterBounds.exists_bounded Q (E + D)
    (IntegerParameterFlatten.massExponent n D b) hQD hQb (d.map (Int.castRingHom ℝ)) hdR hgood
  refine ⟨r, hr, hdeg, hmass, ?_⟩
  intro t x hx hrt
  have hz (j : Fin n) : (Q j).eval₂ (Int.castRingHom ℝ) (Fin.cons t x) = 0 := by
    simpa only [Q, IntegerParameterFlatten.eval_flatten, Fin.cons_zero, Fin.cons_succ] using hx j
  have h := hregular (Fin.cons t x) hz hrt
  simpa only [Q, eval_jacobian, Fin.cons_zero, Fin.cons_succ] using h

end LeanCanny.Geometry.ParameterizedSingularityBounds
