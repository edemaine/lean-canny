/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalQuotient
public import LeanCanny.Algebra.MacaulayCharacteristicQuotient

/-! # Specializing the universal quotient to characteristic determinants

The universal integer polynomial evaluated on the shifted input system is
the canonical characteristic quotient. Evaluating its parameter at zero
recovers the universal polynomial value on the original inputs. These
identities hold over every commutative ring, including inputs with zero
extraneous determinant.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem polynomialValue_subtractiveSystem (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) :
    polynomialValue d W hdegree hW (Macaulay.subtractiveSystem p d) = Macaulay.characteristicQuotient p d W := by
  have he := polynomialValue_factorization d W hdegree hW (Macaulay.subtractiveSystem p d)
    (Macaulay.subtractiveSystem_homogeneous p d hp) hd
  rw [Macaulay.activeMinor_subtractiveSystem, Macaulay.extraneousMinor_subtractiveSystem] at he
  exact (AffineCharacteristic.quotientPolynomial_eq_of_factorization _ _ _ he).symm

theorem subtractiveSystem_eval_zero (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (d : Fin (n + 1) → ℕ) :
    (fun i => (Macaulay.subtractiveSystem p d i).map (Polynomial.evalRingHom (0 : R))) = p := by
  funext i
  ext m
  simp [Macaulay.subtractiveSystem, MvPolynomial.coeff_map]

theorem subtractiveSystem_eval (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (d : Fin (n + 1) → ℕ) (s : R) :
    (fun i => (Macaulay.subtractiveSystem p d i).map (Polynomial.evalRingHom s)) =
      (fun i => p i - MvPolynomial.monomial (Finsupp.single i (d i)) s) := by
  funext i
  ext m
  simp [Macaulay.subtractiveSystem, MvPolynomial.coeff_map, MvPolynomial.coeff_monomial]

theorem eval_characteristicQuotient (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hd : ∀ i, 0 < d i) (s : R) :
    Polynomial.eval s (Macaulay.characteristicQuotient p d W) =
      polynomialValue d W hdegree hW (fun i => p i - MvPolynomial.monomial (Finsupp.single i (d i)) s) := by
  have he := polynomialValue_map (Polynomial.evalRingHom s) d W hdegree hW (Macaulay.subtractiveSystem p d)
  rw [polynomialValue_subtractiveSystem d W hdegree hW p hp hd, subtractiveSystem_eval] at he
  exact he

theorem polynomialValue_eq_eval_zero (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) :
    polynomialValue d W hdegree hW p = Polynomial.eval 0 (Macaulay.characteristicQuotient p d W) := by
  have he := polynomialValue_map (Polynomial.evalRingHom (0 : R)) d W hdegree hW (Macaulay.subtractiveSystem p d)
  rw [polynomialValue_subtractiveSystem d W hdegree hW p hp hd, subtractiveSystem_eval_zero] at he
  exact he.symm

theorem polynomialValue_powers (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) (hd : ∀ i, 0 < d i) :
    polynomialValue (R := R) d W hdegree hW (Macaulay.powers d) = 1 := by
  have he := polynomialValue_factorization d W hdegree hW (Macaulay.powers (R := R) d)
    (KoszulWeighted.powers_homogeneous d) hd
  rw [← Macaulay.eligibilityMinor_det_one, ← Macaulay.eligibilityMinor_det_two,
    Macaulay.eligibilityMinor_powers, Macaulay.eligibilityMinor_powers, Matrix.det_one, Matrix.det_one, one_mul] at he
  exact he.symm

end LeanCanny.Algebra.MacaulayUniversal
