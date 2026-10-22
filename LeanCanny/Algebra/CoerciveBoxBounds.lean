/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoerciveBoxGramEliminant
public import LeanCanny.Algebra.CoerciveRadiusBits
public import LeanCanny.Algebra.NestedMassSwap
public import LeanCanny.Algebra.SymbolicScaledSquarefreeSmall

/-! # Uniform original-source budgets for canonical symbolic annihilants -/

@[expose] public section
namespace LeanCanny.Algebra.CoerciveBoxGramEliminant
open Polynomial CoerciveCriticalHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def massExponent (n D b : ℕ) : ℕ :=
  blockDimension n D * (2 * (blockDimension n D).size + 2 * CoerciveRadiusBits.budgetExponent D b) + 1

theorem mass_le_pow (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) (i : Fin n) :
    NestedMass.mass (polynomial q D i) ≤ 2 ^ massExponent n D b := by
  let C := columnCount n D
  let N := blockDimension n D
  let K := CoerciveRadiusBits.budgetExponent D b
  have hC : C ≤ N := by dsimp [C, N, blockDimension]; nlinarith
  have hR : (n + 2) * C ≤ N := by dsimp [N, blockDimension, C]; nlinarith
  have hCN : C ≤ 2 ^ N.size := hC.trans (Nat.lt_size_self N).le
  have hfac : C.factorial ≤ (2 ^ N.size) ^ C :=
    (Nat.factorial_le_pow C).trans (Nat.pow_le_pow_left hCN C)
  have hbudget := CoerciveRadiusBits.coefficientBudget_le q D b hb
  have hbase : (n + 2) * C * CoerciveCriticalBounds.coefficientBudget q D ^ 2 ≤
      2 ^ (N.size + 2 * K) := by
    calc
      _ ≤ 2 ^ N.size * (2 ^ K) ^ 2 := Nat.mul_le_mul
        (hR.trans (Nat.lt_size_self N).le) (Nat.pow_le_pow_left hbudget 2)
      _ = _ := by rw [← pow_mul, Nat.mul_comm K 2, ← pow_add]
  have hm : NestedMass.mass (polynomial q D i) ≤ 2 ^ (C * (2 * N.size + 2 * K)) := by
    apply (mass_le q D hD i).trans
    change C.factorial * _ ^ C ≤ _
    calc
      _ ≤ (2 ^ N.size) ^ C * (2 ^ (N.size + 2 * K)) ^ C :=
        Nat.mul_le_mul hfac (Nat.pow_le_pow_left hbase C)
      _ = _ := by rw [← mul_pow, ← pow_add, ← pow_mul]; congr 1; ring
  exact hm.trans (Nat.pow_le_pow_right (by decide) (by
    unfold massExponent
    dsimp [N, K] at hC ⊢
    have := Nat.mul_le_mul_right (2 * (blockDimension n D).size +
      2 * CoerciveRadiusBits.budgetExponent D b) hC
    omega))

/-- The primitive-root variable is outermost, and the perturbation variable is
in the coefficient ring, as required by symbolic balanced preparation. -/
noncomputable def symbolic (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (i : Fin n) : Polynomial (Polynomial ℤ) :=
  Polynomial.Bivariate.swap (polynomial q D i)

theorem symbolic_ne_zero (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) : symbolic q D i ≠ 0 := by
  intro hz
  apply ne_zero q D hD i
  have h := congrArg Polynomial.Bivariate.swap hz
  simpa only [symbolic, Polynomial.Bivariate.swap_swap_apply, map_zero] using h

theorem symbolic_mass (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) (i : Fin n) :
    NestedMass.mass (symbolic q D i) ≤ 2 ^ massExponent n D b := by
  rw [symbolic, NestedMass.swap]
  exact mass_le_pow q D b hD hb i

theorem symbolic_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) : (symbolic q D i).natDegree ≤ blockDimension n D :=
  (PolynomialKronecker.inner_degree_iff_swap _ _).mp (inner_degree q D hD i)

theorem symbolic_inner_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) (j : ℕ) :
    ((symbolic q D i).coeff j).natDegree ≤ blockDimension n D :=
  (PolynomialKronecker.inner_degree_iff_swap _ _).mpr
    (by rw [symbolic, Polynomial.Bivariate.swap_swap_apply]; exact outer_degree q D hD i) j

private theorem eval_swap (p : Polynomial (Polynomial ℤ)) (s t : ℝ) :
    (Polynomial.Bivariate.swap p).eval₂ (SymbolicScaledSquarefree.scalarEvaluation s) t =
      parameterMap s t p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval₂_add, hp, hq]
  | monomial j a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, Polynomial.eval₂_add, ha, hb]
    | monomial k z =>
      rw [Polynomial.Bivariate.swap_monomial_monomial]
      simp only [Polynomial.eval₂_monomial, SymbolicScaledSquarefree.scalarEvaluation,
        parameterMap, Polynomial.coe_eval₂RingHom, Int.coe_castRingHom]
      ring

theorem symbolic_eval_eq_zero (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) (s : ℝ) (x : Fin n → ℝ)
    (hx : ∀ j, MvPolynomial.eval x (MvPolynomial.pderiv j
      (CoerciveCriticalFibers.polynomial (q.map (Int.castRingHom ℝ)) D s)) = 0) :
    (symbolic q D i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation s) (x i) = 0 := by
  rw [symbolic, eval_swap]
  exact eval_eq_zero q D hD i s x hx

end LeanCanny.Algebra.CoerciveBoxGramEliminant
