/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthKronecker
public import LeanCanny.Algebra.IndexedRationalSubstitutionBounds
public import LeanCanny.Algebra.MvCoefficientMass

/-! # Indexed rational clearing with several free variables

Fixed even denominator powers preserve signs at every assignment where
the denominators are nonzero. Fixed-width Kronecker substitution commutes
with clearing, permitting the existing native univariate coefficient engine.
-/

@[expose] public section
namespace LeanCanny.Algebra.IndexedMultivariateRational
open scoped Classical BigOperators

variable {σ R : Type*} [CommSemiring R]

noncomputable def cleared (A M W : ℕ) (a : ℕ → R) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ r ∈ Finset.range M, MvPolynomial.C (a r) * ∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)

theorem encode_cleared (K B A M W : ℕ) (a : ℕ → R) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → MvPolynomial (Fin K) R) :
    FixedWidthKronecker.encode K B (cleared A M W a e n d) =
      RationalSubstitution.Indexed.cleared A M W a e
        (fun i => FixedWidthKronecker.encode K B (n i)) (fun i => FixedWidthKronecker.encode K B (d i)) := by
  simp only [cleared, map_sum, map_mul, map_prod, map_pow, RationalSubstitution.Indexed.cleared]
  congr 1
  funext r
  congr 1
  simp only [FixedWidthKronecker.encode, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]

theorem totalDegree_cleared_le (A M W E : ℕ) (a : ℕ → R) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → MvPolynomial σ R)
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W)
    (hn : ∀ i, i < A → (n i).totalDegree ≤ E) (hd : ∀ i, i < A → (d i).totalDegree ≤ E) :
    (cleared A M W a e n d).totalDegree ≤ A * W * E := by
  unfold cleared
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r hr
  have hr' := Finset.mem_range.mp hr
  calc
    _ ≤ (MvPolynomial.C (a r)).totalDegree + (∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)).totalDegree := by simp only [MvPolynomial.totalDegree_C, Nat.zero_add]
    _ ≤ ∑ i ∈ Finset.range A, (n i ^ e r i * d i ^ (W - e r i)).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _i ∈ Finset.range A, W * E := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      calc
        _ ≤ (n i ^ e r i).totalDegree + (d i ^ (W - e r i)).totalDegree := MvPolynomial.totalDegree_mul _ _
        _ ≤ e r i * (n i).totalDegree + (W - e r i) * (d i).totalDegree :=
          Nat.add_le_add (MvPolynomial.totalDegree_pow _ _) (MvPolynomial.totalDegree_pow _ _)
        _ ≤ e r i * E + (W - e r i) * E := Nat.add_le_add
          (Nat.mul_le_mul_left _ (hn i hi')) (Nat.mul_le_mul_left _ (hd i hi'))
        _ = W * E := by rw [← Nat.add_mul, Nat.add_sub_of_le (he r hr' i hi')]
    _ = A * W * E := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_assoc]

theorem eval₂_cleared {K : Type*} [Field K] (φ : R →+* K) (v : σ → K) (A M W : ℕ)
    (a : ℕ → R) (e : ℕ → ℕ → ℕ) (n d : ℕ → MvPolynomial σ R)
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W)
    (hd : ∀ i, i < A → (d i).eval₂ φ v ≠ 0) :
    (cleared A M W a e n d).eval₂ φ v = (∏ i ∈ Finset.range A, (d i).eval₂ φ v ^ W) *
      (RationalSubstitution.Indexed.source A M a e).eval₂ φ
        (fun i => (n i.val).eval₂ φ v / (d i.val).eval₂ φ v) := by
  let ψ := MvPolynomial.eval₂Hom φ v
  have hC (a : R) : ψ (MvPolynomial.C a) = φ a := MvPolynomial.eval₂_C _ _ _
  change ψ (cleared A M W a e n d) = (∏ i ∈ Finset.range A, ψ (d i) ^ W) *
    (RationalSubstitution.Indexed.source A M a e).eval₂ φ (fun i => ψ (n i.val) / ψ (d i.val))
  simp only [cleared, map_sum, map_mul, map_prod, map_pow, hC]
  rw [RationalSubstitution.Indexed.eval₂_source φ A M a e (fun i => ψ (n i) / ψ (d i)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = φ (a r) * ∏ i ∈ Finset.range A, ψ (d i) ^ W * (ψ (n i) / ψ (d i)) ^ e r i := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact (RationalSubstitution.scale_div_pow _ _ _ _ (he r (Finset.mem_range.mp hr) i (Finset.mem_range.mp hi))
        (hd i (Finset.mem_range.mp hi))).symm
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

theorem sign_eval₂_cleared (φ : R →+* ℝ) (v : σ → ℝ) (A M D : ℕ)
    (a : ℕ → R) (e : ℕ → ℕ → ℕ) (n d : ℕ → MvPolynomial σ R)
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ 2 * D)
    (hd : ∀ i, i < A → (d i).eval₂ φ v ≠ 0) :
    SignType.sign ((cleared A M (2 * D) a e n d).eval₂ φ v) =
      SignType.sign ((RationalSubstitution.Indexed.source A M a e).eval₂ φ
        (fun i => (n i.val).eval₂ φ v / (d i.val).eval₂ φ v)) := by
  have hpos : 0 < ∏ i ∈ Finset.range A, (d i).eval₂ φ v ^ (2 * D) := by
    apply Finset.prod_pos
    intro i hi
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero (hd i (Finset.mem_range.mp hi))) _
  rw [eval₂_cleared φ v A M (2 * D) a e n d he hd, sign_mul, sign_pos hpos, one_mul]

noncomputable def parameter (k : ℕ) : Polynomial ℤ →+* MvPolynomial (Fin (k + 1)) ℤ :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

theorem parameter_degree (k : ℕ) (p : Polynomial ℤ) : (parameter k p).totalDegree ≤ p.natDegree := by
  change (p.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin (k + 1)))).totalDegree ≤ _
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, Nat.zero_add]
  exact (MvPolynomial.totalDegree_pow _ _).trans (by
    simpa only [MvPolynomial.totalDegree_X, Nat.mul_one] using Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi))

theorem encode_parameter (k W : ℕ) (p : Polynomial ℤ) : FixedWidthKronecker.encode (k + 1) W (parameter k p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial i a =>
    simp only [parameter, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      map_mul, map_pow, FixedWidthKronecker.encode, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Fin.val_zero, Nat.zero_mul, pow_zero, pow_one,
      Polynomial.C_mul_X_pow_eq_monomial]

theorem eval_parameter {T : Type*} [CommSemiring T] (k : ℕ) (p : Polynomial ℤ)
    (φ : ℤ →+* T) (v : Fin (k + 1) → T) : (parameter k p).eval₂ φ v = p.eval₂ φ (v 0) := by
  change (MvPolynomial.eval₂Hom φ v) (parameter k p) = _
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Polynomial.eval₂_add, hp, hq]
  | monomial i a =>
    simp only [parameter, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      map_mul, map_pow, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

end LeanCanny.Algebra.IndexedMultivariateRational
