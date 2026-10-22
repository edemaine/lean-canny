/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightedExact
public import LeanCanny.Algebra.KoszulExactSurjectivity
public import LeanCanny.Algebra.MacaulayNullstellensatz

/-! # The sharp Macaulay degree bound and the projective root criterion

Over an algebraically closed field, positive homogeneous inputs with no
nonzero common root generate every form of degree `1 + ∑ (dᵢ - 1)`.
Equivalently, their full Macaulay row map is surjective. The normalized
polynomial quotient is therefore nonzero exactly when there is no nonzero
common root, including specializations with zero extraneous determinant.
-/

@[expose] public section

open scoped Classical Matrix

namespace LeanCanny.Algebra.Macaulay
variable {n : ℕ} {K : Type*} [Field K] [IsAlgClosed K]

theorem fullMatrix_surjective_of_no_nonzero_root (p : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W)
    (hroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0) :
    Function.Surjective (fun v => Matrix.vecMul v (fullMatrix p d W)) :=
  KoszulWeighted.fullMatrix_surjective_of_weighted_exact p d W hp hW
    (KoszulWeighted.weighted_exact_of_no_nonzero_root p d (level d) W hp hd hW hroot)

theorem fullMatrix_surjective_iff_no_nonzero_root (p : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W) :
    Function.Surjective (fun v => Matrix.vecMul v (fullMatrix p d W)) ↔
      ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0 :=
  ⟨no_nonzero_root_of_fullMatrix_surjective p d W hp hW,
    fullMatrix_surjective_of_no_nonzero_root p d W hp hd hW⟩

theorem homogeneous_mem_generated_of_no_nonzero_root (p : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0)
    (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous (level d)) :
    f ∈ ProjectiveNullstellensatz.generated p :=
  (fullMatrix_surjective_iff_homogeneous_membership p d (level d) hp Nat.lt_two_pow_self).mp
    (fullMatrix_surjective_of_no_nonzero_root p d (level d) hp hd Nat.lt_two_pow_self hroot) f hf

end LeanCanny.Algebra.Macaulay

namespace LeanCanny.Algebra.MacaulayUniversal
variable {n : ℕ} {K : Type*} [Field K] [IsAlgClosed K]

theorem polynomialValue_isUnit_of_no_nonzero_root (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hroot : ∀ x : Fin (n + 1) → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0) :
    IsUnit (polynomialValue d W hdegree hW p) :=
  polynomialValue_isUnit_of_fullMatrix_surjective d W hdegree hW p hp hd
    (Macaulay.fullMatrix_surjective_of_no_nonzero_root p d W hp hd hW hroot)

theorem polynomialValue_ne_zero_iff_no_nonzero_root (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) :
    polynomialValue d W hdegree hW p ≠ 0 ↔
      ∀ x : Fin (n + 1) → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0 :=
  ⟨no_nonzero_root_of_polynomialValue_ne_zero d W hdegree hW p hp hd,
    fun hroot => (polynomialValue_isUnit_of_no_nonzero_root d W hdegree hW p hp hd hroot).ne_zero⟩

theorem polynomialValue_eq_zero_iff_exists_common_root (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) :
    polynomialValue d W hdegree hW p = 0 ↔
      ∃ x : Fin (n + 1) → K, (∀ i, MvPolynomial.eval x (p i) = 0) ∧ ∃ j, x j ≠ 0 := by
  constructor
  · intro hz
    by_contra hn
    have hroot : ∀ x : Fin (n + 1) → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0 := by
      intro x hx
      funext j
      by_contra hj
      exact hn ⟨x, hx, j, hj⟩
    exact (polynomialValue_isUnit_of_no_nonzero_root d W hdegree hW p hp hd hroot).ne_zero hz
  · rintro ⟨x, hx, hnz⟩
    exact polynomialValue_eq_zero_of_common_root d W hdegree hW p hp hd x hx hnz

theorem eval_characteristicQuotient_eq_zero_iff_exists_common_root (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (s : K) :
    Polynomial.eval s (Macaulay.characteristicQuotient p d W) = 0 ↔
      ∃ x : Fin (n + 1) → K, (∀ i, MvPolynomial.eval x (p i) = s * x i ^ d i) ∧ ∃ j, x j ≠ 0 := by
  rw [eval_characteristicQuotient d W hdegree hW p hp hd s,
    polynomialValue_eq_zero_iff_exists_common_root d W hdegree hW _
      (fun i => (hp i).sub (MvPolynomial.isHomogeneous_monomial s (Finsupp.degree_single i (d i)))) hd]
  simp only [map_sub, MvPolynomial.eval_monomial, Finsupp.prod_single_index, pow_zero, sub_eq_zero]

end LeanCanny.Algebra.MacaulayUniversal
