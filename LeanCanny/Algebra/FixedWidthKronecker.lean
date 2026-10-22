/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import Mathlib.Algebra.Polynomial.BigOperators

/-! # Fixed-width Kronecker substitution in arbitrarily many variables

Replacing variable i by X^(2^(W*i)) embeds every polynomial whose exponents
fit W bits. Binary ranks are exactly the resulting univariate exponents.
The map is a ring homomorphism, so it commutes with determinants.
-/

@[expose] public section

namespace LeanCanny.Algebra.FixedWidthKronecker
open LeanCanny.Encoding FixedWidthPolynomial
open scoped BigOperators Classical

variable {R : Type*} [CommSemiring R]

noncomputable def encode (A W : ℕ) : MvPolynomial (Fin A) R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.X ^ (2 ^ (i.val * W)))

theorem monomial (A W : ℕ) (m : Fin A →₀ ℕ) (a : R) :
    encode A W (MvPolynomial.monomial m a) =
      Polynomial.monomial (∑ i : Fin A, m i * 2 ^ (i.val * W)) a := by
  rw [encode, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [Nat.mul_comm (2 ^ _), Polynomial.C_mul_X_pow_eq_monomial]

theorem vector_monomial (A W : ℕ) (r : Fin (count A W)) (a : R) :
    encode A W (MvPolynomial.monomial (vector A W r) a) = Polynomial.monomial r.val a := by
  rw [monomial]
  have h := congrArg Fin.val ((@finFunctionFinEquiv (2 ^ W) A).apply_symm_apply r)
  rw [finFunctionFinEquiv_apply] at h
  have he : (∑ i : Fin A, vector A W r i * 2 ^ (i.val * W)) = r.val := by
    simpa only [vector, Finsupp.coe_equivFunOnFinite_symm, ← pow_mul, Nat.mul_comm W] using h
  rw [he]

theorem encode_eq_sum (A W : ℕ) (p : MvPolynomial (Fin A) R)
    (hp : ∀ m ∈ p.support, ∀ i, m i < 2 ^ W) :
    encode A W p = ∑ r : Fin (count A W), Polynomial.monomial r.val (p.coeff (vector A W r)) := by
  calc
    _ = encode A W (∑ r : Fin (count A W), MvPolynomial.monomial (vector A W r) (p.coeff (vector A W r))) :=
      congrArg (encode A W) (sum_monomials_eq A W p hp).symm
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [vector_monomial]

theorem coefficient (A W : ℕ) (p : MvPolynomial (Fin A) R)
    (hp : ∀ m ∈ p.support, ∀ i, m i < 2 ^ W) (r : Fin (count A W)) :
    (encode A W p).coeff r.val = p.coeff (vector A W r) := by
  rw [encode_eq_sum A W p hp, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _ hs
    exact ite_eq_right (fun h => hs (Fin.ext h))
  · simp

theorem coefficient_of_ge (A W : ℕ) (p : MvPolynomial (Fin A) R)
    (hp : ∀ m ∈ p.support, ∀ i, m i < 2 ^ W) (r : ℕ) (hr : count A W ≤ r) :
    (encode A W p).coeff r = 0 := by
  rw [encode_eq_sum A W p hp, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro s _
  rw [Polynomial.coeff_monomial]
  exact ite_eq_right (by have := s.isLt; omega)

noncomputable def native {σ : Type*} {A : ℕ} (f : σ ≃ Fin A) (W : ℕ) :
    MvPolynomial σ R →+* Polynomial R := (encode A W).comp (MvPolynomial.rename f).toRingHom

theorem native_coefficient {σ : Type*} [Fintype σ] {A : ℕ} (f : σ ≃ Fin A) (W D : ℕ)
    (p : MvPolynomial σ R) (hp : p.totalDegree ≤ D) (hW : D < 2 ^ W)
    (r : ℕ) (hr : r < count A W) :
    (native f W p).coeff r = p.coeff (nativeExponent f W r) := by
  have hs (m) (hm : m ∈ (MvPolynomial.rename f p).support) (i) : m i < 2 ^ W :=
    ((MvPolynomial.monomial_le_degreeOf i hm).trans
      ((MvPolynomial.degreeOf_le_totalDegree _ i).trans ((MvPolynomial.totalDegree_rename_le _ _).trans hp))).trans_lt hW
  change (encode A W (MvPolynomial.rename f p)).coeff r = _
  have hc := coefficient A W (MvPolynomial.rename f p) hs ⟨r, hr⟩
  change (encode A W (MvPolynomial.rename f p)).coeff r = _ at hc
  rw [hc, ← entry_vector A W ⟨r, hr⟩, coeff_rename_rank]

end LeanCanny.Algebra.FixedWidthKronecker
