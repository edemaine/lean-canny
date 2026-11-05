/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SquareFeatureProductFamily
public import LeanCanny.Algebra.SquareFeatureProductStratum
public import LeanCanny.Algebra.MvTwoParameterCoefficient
/-! # Literal formal feature coefficients specialize to the compact stratum

Integer bounds belong to the unspecialized polynomial. No height assertion
is made about a real center or any coefficient after specialization.
-/
@[expose] public section
namespace LeanCanny.Algebra.SquareFeatureProductEvaluation
open Polynomial MvPolynomial
open SquareFeatureProductFamily
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def values (F : Family) (c : List Bool) (z : Fin (F.arity c) → ℝ) : List ℝ :=
  List.ofFn (fun i : Fin (F.count c) => (F.feature c i.val).eval₂ (Int.castRingHom ℝ) z)

private theorem rename_tail (n : ℕ) (p : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.finSuccEquiv ℤ n (MvPolynomial.rename Fin.succ p) = Polynomial.C p := by
  have HE : (MvPolynomial.finSuccEquiv ℤ n).toRingEquiv.toRingHom.comp
      (MvPolynomial.rename (Fin.succ : Fin n → Fin (n+1))).toRingHom = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [MvPolynomial.finSuccEquiv_apply]
  exact congrArg (fun f => f p) HE

theorem specialization (F : Family) (c : List Bool) (z : Fin (F.arity c) → ℝ) :
    (MvPolynomial.finSuccEquiv ℤ (F.arity c) (SquareFeatureProductFamily.polynomial F c)).map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z) = SquareFeatureProduct.polynomial (values F c z) := by
  rw [SquareFeatureProductFamily.polynomial, map_prod, Polynomial.map_prod]
  rw [SquareFeatureProduct.polynomial, values, List.map_ofFn, List.prod_ofFn]
  change _ = ∏ i : Fin (F.count c), (Polynomial.X + Polynomial.C
    (((F.feature c i.val).eval₂ (Int.castRingHom ℝ) z)^2))
  rw [Fin.prod_univ_eq_prod_range (fun i => Polynomial.X + Polynomial.C
    (((F.feature c i).eval₂ (Int.castRingHom ℝ) z)^2)) (F.count c)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [SquareFeatureProductFamily.factor, map_add, map_pow, finSuccEquiv_X_zero,
    rename_tail, Polynomial.map_add, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_C,
    MvPolynomial.coe_eval₂Hom]

theorem coefficient (F : Family) (c : List Bool) (z : Fin (F.arity c) → ℝ) (k : ℕ) :
    (MvTwoParameterCoefficient.one (SquareFeatureProductFamily.polynomial F c) k).eval₂
      (Int.castRingHom ℝ) z = (SquareFeatureProduct.polynomial (values F c z)).coeff k := by
  rw [←specialization F c z, Polynomial.coeff_map]
  rfl

/-- One selected zero coefficient and one reciprocal-square equation pin
the exact number of zero features, including the zero-coefficient case. -/
theorem compact_iff (F : Family) (c : List Bool) (z : Fin (F.arity c) → ℝ) (k : ℕ) :
    (∃ w : ℝ,
      ((if k=0 then 0 else (MvTwoParameterCoefficient.one
        (SquareFeatureProductFamily.polynomial F c) (k-1)).eval₂ (Int.castRingHom ℝ) z)^2 +
      ((MvTwoParameterCoefficient.one (SquareFeatureProductFamily.polynomial F c) k).eval₂
        (Int.castRingHom ℝ) z*w^2-1)^2)=0) ↔ SquareFeatureProduct.zeroCount (values F c z)=k := by
  simp only [coefficient]
  exact SquareFeatureProduct.exists_equation_iff (values F c z) k

end LeanCanny.Algebra.SquareFeatureProductEvaluation
