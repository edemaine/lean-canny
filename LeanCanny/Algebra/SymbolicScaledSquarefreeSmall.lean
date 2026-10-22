/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicScaledSquarefreeSpecialization

/-! # A source-derived small interval for symbolic squarefree preprocessing

The original leading coefficient and selected principal subresultant have
explicit mass bounds. A common dyadic threshold preserves their nonvanishing,
so ordinary real evaluation preserves the symbolic GCD order and root set.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicScaledSquarefree
open Polynomial PrincipalSubresultant
open scoped Classical

theorem selected_psc_eq_gcd_coeff (p : Polynomial Coefficient) (hd : p.natDegree ≠ 0) :
    psc p p.derivative p.natDegree p.derivative.natDegree (degree p) = (gcd p).coeff (degree p) := by
  rw [gcd, ite_eq_right hd, coefficientForm_coeff, ite_eq_left le_rfl, subresultantCoeff_self]

def smallExponent (D b : ℕ) : ℕ := b + gcdMassExponent D b + 1

noncomputable def scalarEvaluation (beta : ℝ) : Coefficient →+* ℝ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℝ) beta

private theorem eval_ne_zero_of_small (q : ℤ[X]) (hq : q ≠ 0) (b s : ℕ)
    (hm : coefficientMass q ≤ 2 ^ b) (hs : b < s)
    (beta : ℝ) (hb : 0 < beta) (hbs : beta ≤ InfinitesimalSign.dyadic s) :
    scalarEvaluation beta q ≠ 0 := by
  have he := InfinitesimalSign.integer_sign_eval_le_dyadic q b s hm hs beta hb hbs
  intro hz
  change SignType.sign (scalarEvaluation beta q) = _ at he
  rw [hz, sign_zero] at he
  exact (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq) (sign_eq_zero_iff.mp he.symm)

theorem small_controls (p : Polynomial Coefficient) (hp : p ≠ 0) (b : ℕ)
    (hm : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b)
    (beta : ℝ) (hb : 0 < beta)
    (hbs : beta ≤ InfinitesimalSign.dyadic (smallExponent p.natDegree b)) :
    scalarEvaluation beta p.leadingCoeff ≠ 0 ∧
      (p.natDegree ≠ 0 → scalarEvaluation beta
        (psc p p.derivative p.natDegree p.derivative.natDegree (degree p)) ≠ 0) := by
  constructor
  · apply eval_ne_zero_of_small _ (leadingCoeff_ne_zero.mpr hp) b _
      (hm p.natDegree) (by unfold smallExponent; omega) beta hb hbs
  · intro hd
    apply eval_ne_zero_of_small _ (degree_psc_ne_zero p hd) (gcdMassExponent p.natDegree b) _
      _ (by unfold smallExponent; omega) beta hb hbs
    rw [selected_psc_eq_gcd_coeff p hd]
    exact gcd_coefficient_mass p b hm _

theorem small_gcd_degree (p : Polynomial Coefficient) (hp : p ≠ 0) (b : ℕ)
    (hm : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b)
    (beta : ℝ) (hb : 0 < beta)
    (hbs : beta ≤ InfinitesimalSign.dyadic (smallExponent p.natDegree b)) :
    (SquarefreePart.common (p.map (scalarEvaluation beta))).natDegree = degree p := by
  have h := small_controls p hp b hm beta hb hbs
  exact (specialized_gcd_data _ p h.1 h.2).2

theorem small_separable (p : Polynomial Coefficient) (hp : p ≠ 0) (b : ℕ)
    (hm : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b)
    (beta : ℝ) (hb : 0 < beta)
    (hbs : beta ≤ InfinitesimalSign.dyadic (smallExponent p.natDegree b)) :
    ((polynomial p).map (scalarEvaluation beta)).Separable := by
  have h := small_controls p hp b hm beta hb hbs
  exact specialized_separable _ p h.1 h.2

theorem small_roots_iff (p : Polynomial Coefficient) (hp : p ≠ 0) (b : ℕ)
    (hm : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b)
    (beta : ℝ) (hb : 0 < beta)
    (hbs : beta ≤ InfinitesimalSign.dyadic (smallExponent p.natDegree b)) (a : ℝ) :
    (polynomial p).eval₂ (scalarEvaluation beta) a = 0 ↔ p.eval₂ (scalarEvaluation beta) a = 0 := by
  have h := small_controls p hp b hm beta hb hbs
  exact specialized_roots_iff _ p h.1 h.2 a

end LeanCanny.Algebra.SymbolicScaledSquarefree
