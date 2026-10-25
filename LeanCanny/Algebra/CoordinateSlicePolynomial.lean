/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalHomogenization
public import LeanCanny.Algebra.CoordinateCriticalValues
public import LeanCanny.Algebra.PolynomialCoefficientDegree

/-! # Coordinate slices over polynomial coefficient rings

The swept coordinate becomes the coefficient parameter and the remaining
coordinates are reindexed consecutively. Evaluation, differentiation, degree,
and the pure-power leading shape pass to this actual polynomial family.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoordinateSlicePolynomial
open MvPolynomial
open scoped Classical BigOperators

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

noncomputable def family :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) (Polynomial R) :=
  eval₂Hom (C.comp Polynomial.C) (Fin.cons (C Polynomial.X) X)

@[simp] theorem family_C (a : R) : family (C a : MvPolynomial (Fin (n + 1)) R) = C (Polynomial.C a) :=
  eval₂Hom_C _ _ _

@[simp] theorem family_X_zero : family (X 0 : MvPolynomial (Fin (n + 1)) R) = C Polynomial.X :=
  eval₂Hom_X' _ _ _

@[simp] theorem family_X_succ (i : Fin n) :
    family (X i.succ : MvPolynomial (Fin (n + 1)) R) = X i := eval₂Hom_X' _ _ _

theorem eval_family (φ : R →+* S) (p : MvPolynomial (Fin (n + 1)) R)
    (t : S) (x : Fin n → S) :
    (family p).eval₂ (Polynomial.eval₂RingHom φ t) x = p.eval₂ φ (Fin.cons t x) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, eval₂_mul, hp, eval₂_mul, eval₂_X]
    congr 1
    refine Fin.cases (by simp) (fun i => by simp) i

theorem pderiv_family (p : MvPolynomial (Fin (n + 1)) R) (i : Fin n) :
    pderiv i (family p) = family (pderiv i.succ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    have hX : pderiv i (family (X j : MvPolynomial (Fin (n + 1)) R)) =
        family (pderiv i.succ (X j : MvPolynomial (Fin (n + 1)) R)) := by
      refine Fin.cases (by simp) (fun j => ?_) j
      by_cases hij : j = i <;> simp [pderiv_X, hij]
    simp only [map_mul, pderiv_mul, map_add, hp, hX]

theorem degree_le [Nontrivial R] (p : MvPolynomial (Fin (n + 1)) R) :
    (family p).totalDegree ≤ p.totalDegree := by
  change (p.eval₂ (C.comp Polynomial.C) (Fin.cons (C Polynomial.X) X)).totalDegree ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply totalDegree_finsetSum_le
  intro e he
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.comp_apply, totalDegree_C, Nat.zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans _ (MvPolynomial.le_totalDegree he)
  apply Finset.sum_le_sum
  intro i _
  apply (totalDegree_pow _ _).trans
  refine Fin.cases (by simp) (fun i => by simp) i

theorem coefficient_degree [Nontrivial R] (p : MvPolynomial (Fin (n + 1)) R) :
    PolynomialCoefficientDegree.Bound (family p) p.totalDegree := by
  have hvar (i : Fin (n + 1)) : PolynomialCoefficientDegree.Bound
      ((Fin.cons (C Polynomial.X) X : Fin (n + 1) → MvPolynomial (Fin n) (Polynomial R)) i) 1 := by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact PolynomialCoefficientDegree.C (by simp)
    · exact PolynomialCoefficientDegree.mono (PolynomialCoefficientDegree.X i) (by decide)
  have hmon (e : Fin (n + 1) →₀ ℕ) (r : R) :
      PolynomialCoefficientDegree.Bound (family (monomial e r)) e.degree := by
    change PolynomialCoefficientDegree.Bound
      ((monomial e r).eval₂ (C.comp Polynomial.C) (Fin.cons (C Polynomial.X) X)) _
    rw [eval₂_monomial]
    have hprod := PolynomialCoefficientDegree.prod e.support
      (fun i => (Fin.cons (C Polynomial.X) X : Fin (n + 1) → MvPolynomial (Fin n) (Polynomial R)) i ^ e i)
      (fun i => e i * 1) (fun i _ => PolynomialCoefficientDegree.pow (hvar i) (e i))
    have hm := PolynomialCoefficientDegree.mul
      (PolynomialCoefficientDegree.C (R := R) (σ := Fin n) (show (Polynomial.C r).natDegree ≤ 0 by simp)) hprod
    simpa only [RingHom.comp_apply, Nat.mul_one, Nat.zero_add, Finsupp.degree_apply, Finsupp.prod] using hm
  have he : family p = ∑ e ∈ p.support, family (monomial e (p.coeff e)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he]
  exact PolynomialCoefficientDegree.sum _ _ _ fun e he =>
    PolynomialCoefficientDegree.mono (hmon e _) (le_totalDegree he)

theorem family_fermat (low : MvPolynomial (Fin (n + 2)) R) (a : R) (N : ℕ) :
    family (FermatCriticalHomogenization.polynomial low a N) =
      FermatCriticalHomogenization.polynomial
        (family low + C (Polynomial.C a * Polynomial.X ^ N)) (Polynomial.C a) N := by
  have hs : family (∑ j : Fin (n + 2), (X j : MvPolynomial (Fin (n + 2)) R) ^ N) =
      C (Polynomial.X ^ N) + ∑ j : Fin (n + 1), X j ^ N := by
    rw [Fin.sum_univ_succ, map_add, map_pow, family_X_zero, map_sum]
    simp only [map_pow, family_X_succ]
  simp only [FermatCriticalHomogenization.polynomial, map_add, map_mul, family_C, hs]
  ring

theorem fermat_lower_degree [Nontrivial R] (low : MvPolynomial (Fin (n + 2)) R) (a : R) (N : ℕ)
    (hlow : low.totalDegree < N) :
    (family low + C (Polynomial.C a * Polynomial.X ^ N)).totalDegree < N := by
  apply (totalDegree_add _ _).trans_lt
  exact max_lt ((degree_le low).trans_lt hlow) (by rw [totalDegree_C]; omega)

end LeanCanny.Algebra.CoordinateSlicePolynomial
