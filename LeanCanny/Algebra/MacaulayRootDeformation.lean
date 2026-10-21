/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayRootModel
public import Mathlib.LinearAlgebra.Matrix.Polynomial

/-! # Deforming a common-root system in a nonsingular direction

Adding a parameter times a second homogeneous system preserves any common
root shared by the two systems. A nonzero extraneous determinant of the
direction gives a nonzero determinant polynomial. Polynomial factorization
and specialization then prove quotient vanishing for the original system.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def rootDeformation (p q : Fin n → MvPolynomial (Fin n) R) :
    Fin n → MvPolynomial (Fin n) (Polynomial R) :=
  fun i => (p i).map Polynomial.C + MvPolynomial.C Polynomial.X * (q i).map Polynomial.C

theorem rootDeformation_homogeneous (p q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hq : ∀ i, (q i).IsHomogeneous (d i)) (i : Fin n) :
    (rootDeformation p q i).IsHomogeneous (d i) :=
  ((hp i).map Polynomial.C).add (((hq i).map Polynomial.C).C_mul Polynomial.X)

theorem eval_map_C (x : Fin n → R) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.eval (fun i => Polynomial.C (x i)) (p.map Polynomial.C) = Polynomial.C (MvPolynomial.eval x p) := by
  have he := MvPolynomial.eval₂_comp (Polynomial.C : R →+* Polynomial R) x p
  simpa only [MvPolynomial.eval_map, Function.comp_def] using he.symm

theorem eval_rootDeformation (p q : Fin n → MvPolynomial (Fin n) R) (x : Fin n → R)
    (hp : ∀ i, MvPolynomial.eval x (p i) = 0) (hq : ∀ i, MvPolynomial.eval x (q i) = 0) (i : Fin n) :
    MvPolynomial.eval (fun j => Polynomial.C (x j)) (rootDeformation p q i) = 0 := by
  simp only [rootDeformation, map_add, map_mul, MvPolynomial.eval_C, eval_map_C, hp i, hq i,
    map_zero, mul_zero, add_zero]

theorem rootDeformation_eval_zero (p q : Fin n → MvPolynomial (Fin n) R) :
    (fun i => (rootDeformation p q i).map (Polynomial.evalRingHom (0 : R))) = p := by
  funext i
  ext m
  simp [rootDeformation, MvPolynomial.coeff_map]

theorem rowPolynomial_rootDeformation (p q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (r : Index n W) (hr : (FixedWidthPolynomial.vector n W r).degree = level d) :
    rowPolynomial (rootDeformation p q) d W r hr = (rowPolynomial p d W r hr).map Polynomial.C +
      MvPolynomial.C Polynomial.X * (rowPolynomial q d W r hr).map Polynomial.C := by
  simp only [rowPolynomial, rootDeformation, map_mul, MvPolynomial.map_monomial, map_one]
  ring

theorem extraneousMinor_rootDeformation (p q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    extraneousMinor (rootDeformation p q) d W =
      (Polynomial.X : Polynomial R) • (extraneousMinor q d W).map Polynomial.C + (extraneousMinor p d W).map Polynomial.C := by
  funext r s
  have hr := (mem_extraneousIndices d W r.val).mp r.property
  change matrix (rootDeformation p q) d W r.val s.val = Polynomial.X * Polynomial.C (matrix q d W r.val s.val) +
    Polynomial.C (matrix p d W r.val s.val)
  rw [matrix, dite_eq_left hr.1, rowPolynomial_rootDeformation, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, MvPolynomial.coeff_map, matrix, dite_eq_left hr.1, matrix, dite_eq_left hr.1, add_comm]

theorem rootDeformation_extraneous_det_ne_zero (p q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hq : (extraneousMinor q d W).det ≠ 0) : (extraneousMinor (rootDeformation p q) d W).det ≠ 0 := by
  rw [extraneousMinor_rootDeformation]
  intro hz
  have he := Polynomial.coeff_det_X_add_C_card (extraneousMinor q d W) (extraneousMinor p d W)
  rw [hz, Polynomial.coeff_zero] at he
  exact hq he.symm

end LeanCanny.Algebra.Macaulay

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {K : Type*} [CommRing K] [IsDomain K]

theorem polynomialValue_eq_zero_of_root_preserving_direction (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p q : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hq : ∀ i, (q i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (x : Fin (n + 1) → K) (hpx : ∀ i, MvPolynomial.eval x (p i) = 0)
    (hqx : ∀ i, MvPolynomial.eval x (q i) = 0) (hnz : ∃ j, x j ≠ 0)
    (he : (Macaulay.extraneousMinor q d W).det ≠ 0) : polynomialValue d W hdegree hW p = 0 := by
  have hy : ∃ j, Polynomial.C (x j) ≠ 0 := by
    obtain ⟨j, hj⟩ := hnz
    exact ⟨j, Polynomial.C_ne_zero.mpr hj⟩
  have hz := polynomialValue_eq_zero_of_common_root_of_extraneous_ne_zero d W hdegree hW
    (Macaulay.rootDeformation p q) (Macaulay.rootDeformation_homogeneous p q d hp hq) hd
    (fun j => Polynomial.C (x j)) (Macaulay.eval_rootDeformation p q x hpx hqx) hy
    (Macaulay.rootDeformation_extraneous_det_ne_zero p q d W he)
  have hs := polynomialValue_map (Polynomial.evalRingHom (0 : K)) d W hdegree hW (Macaulay.rootDeformation p q)
  rw [hz, map_zero, Macaulay.rootDeformation_eval_zero] at hs
  exact hs.symm

theorem polynomialValue_eq_zero_of_last_coordinate_ne_zero (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (x : Fin (n + 1) → K) (hx : ∀ i, MvPolynomial.eval x (p i) = 0) (hlast : x (Fin.last n) ≠ 0) :
    polynomialValue d W hdegree hW p = 0 :=
  polynomialValue_eq_zero_of_root_preserving_direction d W hdegree hW p (Macaulay.rootModel d x) hp
    (Macaulay.rootModel_homogeneous d x) hd x hx (Macaulay.eval_rootModel d x) ⟨Fin.last n, hlast⟩
    (Macaulay.rootModel_extraneous_det_ne_zero d W hd x hlast)

end LeanCanny.Algebra.MacaulayUniversal
