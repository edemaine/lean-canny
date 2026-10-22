/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayRootDeformation
public import LeanCanny.Algebra.MacaulayQuotientPermutation

/-! # Projective common roots annihilate the polynomial quotient

Every nonzero common homogeneous root over a domain annihilates the
normalized polynomial Macaulay quotient, without restrictions on the
extraneous determinant. Move a nonzero coordinate to the last position,
apply the root-preserving deformation there, and transport the universal
polynomial value back. Coefficient specialization gives the same result
for roots in an extension domain and for characteristic-quotient roots.
The converse over algebraically closed fields is proved in
`MacaulayProjectiveCriterion`; multivariate-resultant identification remains open.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {K : Type*} [CommRing K] [IsDomain K]

theorem polynomialValue_eq_zero_of_common_root (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (x : Fin (n + 1) → K) (hx : ∀ i, MvPolynomial.eval x (p i) = 0) (hnz : ∃ j, x j ≠ 0) :
    polynomialValue d W hdegree hW p = 0 := by
  obtain ⟨j, hj⟩ := hnz
  let π : Equiv.Perm (Fin (n + 1)) := Equiv.swap (Fin.last n) j
  let q := fun i => MvPolynomial.rename π.symm (p (π i))
  let y := fun i => x (π i)
  have hπ : Macaulay.level (d ∘ π) < 2 ^ W := by rwa [level_comp_perm]
  have hq : ∀ i, (q i).IsHomogeneous ((d ∘ π) i) := fun i => (hp (π i)).rename_isHomogeneous
  have hxy : y ∘ π.symm = x := by funext i; simp only [y, Function.comp_apply, Equiv.apply_symm_apply]
  have hroot : ∀ i, MvPolynomial.eval y (q i) = 0 := by
    intro i
    dsimp only [q]
    rw [MvPolynomial.eval_rename, hxy]
    exact hx (π i)
  have hlast : y (Fin.last n) ≠ 0 := by simpa only [y, π, Equiv.swap_apply_left] using hj
  have hz := polynomialValue_eq_zero_of_last_coordinate_ne_zero (d ∘ π) W (fun i => hdegree (π i)) hπ
    q hq (fun i => hd (π i)) y hroot hlast
  dsimp only [q] at hz
  rw [polynomialValue_permutation d W hdegree hW π hπ p] at hz
  exact hz

theorem map_polynomialValue_eq_zero_of_common_root {R : Type*} [CommRing R] (φ : R →+* K)
    (d : Fin (n + 1) → ℕ) (W : ℕ) (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (x : Fin (n + 1) → K) (hx : ∀ i, MvPolynomial.eval₂ φ x (p i) = 0) (hnz : ∃ j, x j ≠ 0) :
    φ (polynomialValue d W hdegree hW p) = 0 := by
  rw [polynomialValue_map]
  apply polynomialValue_eq_zero_of_common_root d W hdegree hW _ (fun i => (hp i).map φ) hd x _ hnz
  intro i
  rw [MvPolynomial.eval_map]
  exact hx i

theorem eval_characteristicQuotient_eq_zero_of_common_root (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (s : K) (x : Fin (n + 1) → K) (hx : ∀ i, MvPolynomial.eval x (p i) = s * x i ^ d i) (hnz : ∃ j, x j ≠ 0) :
    Polynomial.eval s (Macaulay.characteristicQuotient p d W) = 0 := by
  rw [eval_characteristicQuotient d W hdegree hW p hp hd s]
  apply polynomialValue_eq_zero_of_common_root d W hdegree hW _ _ hd x _ hnz
  · intro i
    exact (hp i).sub (MvPolynomial.isHomogeneous_monomial s (Finsupp.degree_single i (d i)))
  · intro i
    simp [hx i, MvPolynomial.eval_monomial]

theorem eval_map_characteristicQuotient_eq_zero_of_common_root {R : Type*} [CommRing R] (φ : R →+* K)
    (d : Fin (n + 1) → ℕ) (W : ℕ) (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (s : K) (x : Fin (n + 1) → K) (hx : ∀ i, MvPolynomial.eval₂ φ x (p i) = s * x i ^ d i) (hnz : ∃ j, x j ≠ 0) :
    Polynomial.eval s ((Macaulay.characteristicQuotient p d W).map φ) = 0 := by
  rw [Macaulay.characteristicQuotient_map]
  apply eval_characteristicQuotient_eq_zero_of_common_root d W hdegree hW _ (fun i => (hp i).map φ) hd s x _ hnz
  intro i
  rw [MvPolynomial.eval_map]
  exact hx i

end LeanCanny.Algebra.MacaulayUniversal
