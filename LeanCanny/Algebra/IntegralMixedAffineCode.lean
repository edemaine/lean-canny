/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedAffineCoefficients
public import LeanCanny.ETR.SizedCollectedCoefficient
/-! # Original affine rules use the verified ETR integer-term coefficient reader -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedAffineCode
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open scoped Classical

def term : AffineExpr → ETR.Term
  | .constant c => .const c
  | .reference i => .var i
  | .add a b => .add (term a) (term b)
  | .scale c e => .mul (.const c) (term e)

def encode (e : AffineExpr) := (term e).toData.toBits

theorem constant_coefficient (e : AffineExpr) (N : ℕ) :
    ((term e).finitePolynomial N).coeff 0 = IntegralMixedAffineCoefficients.constantCoefficient e := by
  induction e with
  | constant c => simp only [term, ETR.Term.finitePolynomial, MvPolynomial.coeff_C, ite_true, IntegralMixedAffineCoefficients.constantCoefficient]
  | reference j =>
    simp only [term, ETR.Term.finitePolynomial, IntegralMixedAffineCoefficients.constantCoefficient]
    split_ifs <;> simp
  | add a b ha hb => simpa only [term, ETR.Term.finitePolynomial, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      IntegralMixedAffineCoefficients.constantCoefficient] using congrArg₂ (· + ·) ha hb
  | scale c e he => simpa only [term, ETR.Term.finitePolynomial, MvPolynomial.coeff_C_mul,
      IntegralMixedAffineCoefficients.constantCoefficient] using congrArg (c * ·) he

theorem reference_coefficient (e : AffineExpr) (N : ℕ) (i : Fin N) :
    ((term e).finitePolynomial N).coeff (Finsupp.single i 1) = IntegralMixedAffineCoefficients.referenceCoefficient e i.val := by
  induction e with
  | constant c =>
    exact MvPolynomial.coeff_C_of_ne_zero (by simp) c
  | reference j =>
    simp only [term, ETR.Term.finitePolynomial, IntegralMixedAffineCoefficients.referenceCoefficient]
    by_cases hj : j < N
    · rw [dite_eq_left hj]
      simp only [MvPolynomial.coeff_X, Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0), Fin.ext_iff]
    · have hn : j ≠ i.val := by intro he; exact hj (he ▸ i.isLt)
      rw [dite_eq_right hj, ite_eq_right hn]
      rfl
  | add a b ha hb => simpa only [term, ETR.Term.finitePolynomial, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      IntegralMixedAffineCoefficients.referenceCoefficient] using congrArg₂ (· + ·) ha hb
  | scale c e he => simpa only [term, ETR.Term.finitePolynomial, MvPolynomial.coeff_C_mul,
      IntegralMixedAffineCoefficients.referenceCoefficient] using congrArg (c * ·) he

theorem reference_outside (e : AffineExpr) (N i : ℕ) (hN : (term e).arity ≤ N) (hi : N ≤ i) :
    IntegralMixedAffineCoefficients.referenceCoefficient e i = 0 := by
  induction e with
  | constant c => rfl
  | reference j =>
    have hn : j ≠ i := by change j + 1 ≤ N at hN; omega
    exact ite_eq_right hn
  | add a b ha hb =>
    exact (congrArg₂ (· + ·) (ha ((le_max_left _ _).trans hN)) (hb ((le_max_right _ _).trans hN))).trans (add_zero 0)
  | scale c e he =>
    change c * IntegralMixedAffineCoefficients.referenceCoefficient e i = 0
    rw [he ((le_max_right _ _).trans hN), mul_zero]
end LeanCanny.Algebra.IntegralMixedAffineCode
