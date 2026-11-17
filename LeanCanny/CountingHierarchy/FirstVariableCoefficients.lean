/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Coefficient polynomials retaining all remaining variables -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

variable {n : ℕ}

noncomputable def firstVariableCoefficient (P : MvPolynomial (Fin (n + 1)) ℤ) (k : ℕ) :
    MvPolynomial (Fin n) ℤ := (MvPolynomial.finSuccEquiv ℤ n P).coeff k

theorem firstVariableCoefficient_degree_le (P : MvPolynomial (Fin (n + 1)) ℤ) (k : ℕ) :
    (firstVariableCoefficient P k).totalDegree ≤ P.totalDegree := by
  by_cases h : firstVariableCoefficient P k = 0
  · simp only [h, MvPolynomial.totalDegree_zero, Nat.zero_le]
  · have := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P k h
    exact (Nat.le_add_right _ k).trans this

theorem firstVariableCoefficient_mass_le (P : MvPolynomial (Fin (n + 1)) ℤ) (k : ℕ) :
    MvMass.mass (firstVariableCoefficient P k) ≤ MvMass.mass P := by
  let Q := firstVariableCoefficient P k
  have hinj : Function.Injective (Finsupp.cons k : (Fin n →₀ ℕ) → (Fin (n + 1) →₀ ℕ)) := by
    intro e f h
    simpa only [Finsupp.tail_cons] using congrArg Finsupp.tail h
  have heq : MvMass.mass Q =
      ∑ e ∈ Q.support.image (Finsupp.cons k), (P.coeff e).natAbs := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    simp only [MvMass.mass, Q, firstVariableCoefficient, MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [heq, show Q.support.image (Finsupp.cons k) = {e ∈ P.support | e 0 = k} from
    MvPolynomial.image_support_finSuccEquiv, MvMass.mass]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

theorem eval_finSuccEquiv {S : Type*} [CommRing S] (phi : ℤ →+* S)
    (z : Fin n → S) (t : S) (P : MvPolynomial (Fin (n + 1)) ℤ) :
    (MvPolynomial.finSuccEquiv ℤ n P).eval₂ (MvPolynomial.eval₂Hom phi z) t =
      MvPolynomial.eval₂ phi (Fin.cons t z) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C,
      RingHom.coe_comp, Function.comp_apply, Polynomial.eval₂_C, MvPolynomial.eval₂_C]
  | add P Q hP hQ => simp only [map_add, Polynomial.eval₂_add, MvPolynomial.eval₂_add, hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, Polynomial.eval₂_mul, MvPolynomial.eval₂_mul, hP]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval₂_X, MvPolynomial.eval₂_X,
        Fin.cons_zero]
    · simp only [MvPolynomial.finSuccEquiv_X_succ, Polynomial.eval₂_C, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_X, Fin.cons_succ]

end LeanCanny.CountingHierarchy
