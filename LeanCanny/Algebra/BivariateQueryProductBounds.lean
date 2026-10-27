/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CertifiedPolynomial
public import LeanCanny.Algebra.NestedCoefficientMass
public import LeanCanny.Algebra.PolynomialKronecker
public import LeanCanny.Algebra.SignQueryBounds

/-! # Bounds for indexed bivariate product queries

Each exponent is zero, one, or two. One radix accommodates both every
original factor and the complete product, including an empty product.
-/

@[expose] public section
namespace LeanCanny.Algebra.BivariateQueryProductBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation
open scoped Classical BigOperators

structure Family where
  polynomial : List Bool → ℕ → (ℤ[X])[X]
  exponent : List Bool → ℕ → Fin 3
  count : List Bool → ℕ
  degree : List Bool → ℕ
  parameterDegree : List Bool → ℕ
  mass : List Bool → ℕ
  polynomial_degree : ∀ c i, (polynomial c i).natDegree ≤ degree c
  coefficient_degree : ∀ c i j, ((polynomial c i).coeff j).natDegree ≤ parameterDegree c
  coefficient_mass : ∀ c i j, coefficientMass ((polynomial c i).coeff j) ≤ 2 ^ mass c

structure Access (F : Family) where
  reader : CertifiedPolynomial.BivariateReader (fun w => F.polynomial (pairFst w) (Nat.fromBitsLE (pairSnd w)))
  exponent : List Bool → List Bool
  exponent_eq : ∀ c i, exponent (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (F.exponent c i).val
  exponent_FP : exponent ∈ FP
  count_binary : BinaryFn F.count
  degree_binary : BinaryFn F.degree
  parameterDegree_binary : BinaryFn F.parameterDegree
  mass_binary : BinaryFn F.mass

noncomputable def Family.product (F : Family) (c : List Bool) : (ℤ[X])[X] :=
  RootSignQueries.queryPolynomial (fun i : Fin (F.count c) => F.polynomial c i.val) (fun i => F.exponent c i.val)

theorem Family.product_degree (F : Family) (c : List Bool) :
    (F.product c).natDegree ≤ 2 * F.count c * F.degree c := by
  simpa only [Family.product, Fintype.card_fin] using RootSignQueries.natDegree_queryPolynomial_le
    (fun i : Fin (F.count c) => F.polynomial c i.val) (fun i => F.exponent c i.val) (F.degree c)
    (fun i => F.polynomial_degree c i.val)

theorem Family.product_parameter_degree (F : Family) (c : List Bool) (j : ℕ) :
    ((F.product c).coeff j).natDegree ≤ 2 * F.count c * F.parameterDegree c := by
  apply (PolynomialKronecker.inner_degree_iff_swap _ _).mpr ?_ j
  have H := RootSignQueries.natDegree_queryPolynomial_le
    (fun i : Fin (F.count c) => Polynomial.Bivariate.swap (F.polynomial c i.val))
    (fun i => F.exponent c i.val) (F.parameterDegree c)
    (fun i => (PolynomialKronecker.inner_degree_iff_swap _ _).mp (F.coefficient_degree c i.val))
  simpa only [Family.product, RootSignQueries.queryPolynomial, map_prod, map_pow, Fintype.card_fin] using H

theorem Family.product_mass (F : Family) (c : List Bool) :
    NestedMass.mass (F.product c) ≤ 2 ^ (2 * F.count c * (F.mass c + (F.degree c + 1).size)) := by
  have hf (i : Fin (F.count c)) : NestedMass.mass (F.polynomial c i.val) ≤ 2 ^ (F.mass c + (F.degree c + 1).size) :=
    NestedMass.le_pow _ _ _ (F.polynomial_degree c i.val) (F.coefficient_mass c i.val)
  calc
    _ ≤ ∏ i : Fin (F.count c), NestedMass.mass (F.polynomial c i.val ^ (F.exponent c i.val).val) := NestedMass.prod_le _ _
    _ ≤ ∏ _i : Fin (F.count c), (2 ^ (F.mass c + (F.degree c + 1).size)) ^ 2 := by
      apply Finset.prod_le_prod
      intro i _
      exact (NestedMass.pow_le _ _).trans ((Nat.pow_le_pow_left (hf i) _).trans
        (Nat.pow_le_pow_right Nat.one_le_two_pow (by have := (F.exponent c i.val).isLt; omega)))
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      congr 1
      ring

noncomputable def Family.radix (F : Family) (c : List Bool) : ℕ :=
  2 * F.count c * F.parameterDegree c + F.parameterDegree c + 1

theorem Family.radix_pos (F : Family) (c : List Bool) : 0 < F.radix c := by unfold Family.radix; omega

theorem Family.factor_inner_lt (F : Family) (c : List Bool) (i j : ℕ) :
    ((F.polynomial c i).coeff j).natDegree < F.radix c :=
  (F.coefficient_degree c i j).trans_lt (by unfold Family.radix; omega)

theorem Family.product_inner_lt (F : Family) (c : List Bool) (j : ℕ) :
    ((F.product c).coeff j).natDegree < F.radix c :=
  (F.product_parameter_degree c j).trans_lt (by unfold Family.radix; omega)

theorem radix_binary {F : Family} (A : Access F) : BinaryFn F.radix :=
  ((((BinaryFn.const 2).mul A.count_binary).mul A.parameterDegree_binary).add A.parameterDegree_binary).add (BinaryFn.const 1)

end LeanCanny.Algebra.BivariateQueryProductBits
