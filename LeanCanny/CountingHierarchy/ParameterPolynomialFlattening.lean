/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PolynomialParameterMass
public import Mathlib.Topology.Algebra.MvPolynomial

/-! # Flattening a polynomial with retained multivariate parameters -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

variable {τ : Type*}

/-- `none` is the outer polynomial variable; `some i` retains parameter `i`. -/
noncomputable def flattenParameterPolynomial :
    Polynomial (MvPolynomial τ ℤ) →+* MvPolynomial (Option τ) ℤ :=
  Polynomial.eval₂RingHom (MvPolynomial.rename some).toRingHom (MvPolynomial.X none)

theorem flattenParameterPolynomial_monomial (i : ℕ) (a : MvPolynomial τ ℤ) :
    flattenParameterPolynomial (Polynomial.monomial i a) =
      MvPolynomial.rename some a * MvPolynomial.X none ^ i :=
  Polynomial.eval₂_monomial _ _

theorem flattenParameterPolynomial_mass_le (p : Polynomial (MvPolynomial τ ℤ)) :
    MvMass.mass (flattenParameterPolynomial p) ≤ PolynomialParameterMass.mass p := by
  conv_lhs => rw [p.as_sum_range, map_sum]
  apply (MvMass.sum_le _ _).trans
  rw [PolynomialParameterMass.range_sum p (p.natDegree + 1) (Nat.lt_succ_self _)]
  apply Finset.sum_le_sum
  intro i _
  rw [flattenParameterPolynomial_monomial]
  apply (MvMass.mul_le _ _).trans
  have hx : MvMass.mass ((MvPolynomial.X none : MvPolynomial (Option τ) ℤ) ^ i) ≤ 1 :=
    (MvMass.pow_le _ _).trans_eq (by rw [MvMass.X, one_pow])
  exact (Nat.mul_le_mul (MvMass.rename_le _ _) hx).trans_eq (Nat.mul_one _)

theorem flattenParameterPolynomial_degree_le (p : Polynomial (MvPolynomial τ ℤ)) (D H : ℕ)
    (hD : p.natDegree ≤ D) (hH : ∀ i, (p.coeff i).totalDegree ≤ H) :
    (flattenParameterPolynomial p).totalDegree ≤ D + H := by
  conv_lhs => rw [p.as_sum_range' (D + 1) (by omega), map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  rw [flattenParameterPolynomial_monomial]
  have hc := (MvPolynomial.totalDegree_rename_le some (p.coeff i)).trans (hH i)
  have hx : ((MvPolynomial.X none : MvPolynomial (Option τ) ℤ) ^ i).totalDegree ≤ i :=
    (MvPolynomial.totalDegree_pow _ _).trans_eq (by rw [MvPolynomial.totalDegree_X, Nat.mul_one])
  exact (MvPolynomial.totalDegree_mul _ _).trans ((Nat.add_le_add hc hx).trans (by
    have := Finset.mem_range.mp hi
    omega))

theorem eval_flattenParameterPolynomial {S : Type*} [CommRing S] (phi : ℤ →+* S)
    (z : τ → S) (t : S) (p : Polynomial (MvPolynomial τ ℤ)) :
    MvPolynomial.eval₂ phi ((fun i => i.elim t z)) (flattenParameterPolynomial p) =
      p.eval₂ (MvPolynomial.eval₂Hom phi z) t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, MvPolynomial.eval₂_add, Polynomial.eval₂_add, hp, hq]
  | monomial i a =>
    rw [flattenParameterPolynomial_monomial]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_rename, Polynomial.eval₂_monomial]
    rfl

end LeanCanny.CountingHierarchy
