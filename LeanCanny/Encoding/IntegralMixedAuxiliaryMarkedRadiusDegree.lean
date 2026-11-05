/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusModel

/-! # Degree preservation for the actual formal-radius marked prelude

Evaluation may have a kernel. The scaled characteristic constructors preserve
outer degree because their actual scaling coefficients remain nonzero.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusModel
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation Polynomial
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open IntegralMixedAuxiliarySlackMatrix (parameters count charge)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem scaled_expand_degree {A : Type*} [CommRing A] [IsDomain A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (c : A) (hc : c ≠ 0) (k : ℕ) :
    (Polynomial.expand A k (ScaledGradedReductionAnnihilator.polynomial M c 1)).natDegree =
      Fintype.card ι * k := by
  rw [Polynomial.natDegree_expand, ScaledGradedReductionAnnihilator.polynomial, pow_one,
    Polynomial.natDegree_comp, Matrix.charpoly_natDegree_eq_dim,
    Polynomial.natDegree_C_mul_X _ hc, Nat.mul_one]

private theorem scaled_expand_map {A B : Type*} [CommRing A] [CommRing B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (c : A) (k : ℕ) (φ : A →+* B) :
    (Polynomial.expand A k (ScaledGradedReductionAnnihilator.polynomial M c 1)).map φ =
      Polynomial.expand B k (ScaledGradedReductionAnnihilator.polynomial (M.map φ) (φ c) 1) := by
  simp only [ScaledGradedReductionAnnihilator.polynomial, pow_one, Polynomial.map_expand,
    Polynomial.map_comp, Matrix.charpoly_map, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]

private theorem scaled_expand_map_degree {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (c : A) (k : ℕ) (φ : A →+* B) (hc : φ c ≠ 0) :
    ((Polynomial.expand A k (ScaledGradedReductionAnnihilator.polynomial M c 1)).map φ).natDegree =
      (Polynomial.expand A k (ScaledGradedReductionAnnihilator.polynomial M c 1)).natDegree := by
  have hc0 : c ≠ 0 := fun h => hc (by rw [h, map_zero])
  rw [scaled_expand_map, scaled_expand_degree _ _ hc, scaled_expand_degree _ _ hc0]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

theorem sphere_map_natDegree (R : ℕ) (key : List Bool) :
    ((sphere hn ht ha key).map (Polynomial.evalRingHom ((2 : ℤ) ^ R))).natDegree =
      (sphere hn ht ha key).natDegree := by
  apply scaled_expand_map_degree
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C] using
    pow_ne_zero 2 (IntegralMixedFramedSlackRootBits.common_ne_zero (parameters n t)
      (planAt hn ht ha) (dataAt hn ht ha) key)

theorem regular_map_natDegree (R : ℕ) (key : List Bool) :
    ((regular hn ht ha key).map (Polynomial.evalRingHom ((2 : ℤ) ^ R))).natDegree =
      (regular hn ht ha key).natDegree := by
  apply scaled_expand_map_degree
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
    IntegralMixedFramedSlackRadiusModel.power_eval]
  exact mul_ne_zero (pow_ne_zero _ (by decide : (2 : ℤ) ≠ 0))
    (pow_ne_zero _ (IntegralMixedFramedSlackRootBits.common_ne_zero (parameters n t)
      (planAt hn ht ha) (dataAt hn ht ha) key))

private theorem constant_map_natDegree (p : ℤ[X]) (r : ℤ) :
    ((constant p).map (Polynomial.evalRingHom r)).natDegree = (constant p).natDegree := by
  rw [constant_map_eval]
  exact (Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective p).symm

private theorem powerLeaf_map_natDegree (offset slope : ℕ) (r : ℤ) :
    ((powerLeaf offset slope).map (Polynomial.evalRingHom r)).natDegree =
      (powerLeaf offset slope).natDegree := by
  simp only [powerLeaf, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.natDegree_X_sub_C]

theorem polynomial_map_natDegree (R : List Bool → ℕ) (q : List Bool) :
    ((polynomial hn ht ha q).map (Polynomial.evalRingHom ((2 : ℤ) ^ R (pairFst q)))).natDegree =
      (polynomial hn ht ha q).natDegree := by
  dsimp only [polynomial]
  split_ifs
  · exact constant_map_natDegree _ _
  · exact sphere_map_natDegree hn ht ha _ _
  · exact regular_map_natDegree hn ht ha _ _
  · exact powerLeaf_map_natDegree _ _ _
  · exact powerLeaf_map_natDegree _ _ _
  · exact powerLeaf_map_natDegree _ _ _
  · exact powerLeaf_map_natDegree _ _ _
  · simp only [Polynomial.map_X, Polynomial.natDegree_X]

theorem native_natDegree (R : List Bool → ℕ) (q : List Bool) :
    ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial q).natDegree =
      (polynomial hn ht ha q).natDegree := by
  rw [← polynomial_map_eval hn ht ha R q]
  exact polynomial_map_natDegree hn ht ha R q

theorem native_leadingCoeff (R : List Bool → ℕ) (q : List Bool) :
    ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial q).leadingCoeff =
      ((polynomial hn ht ha q).leadingCoeff).eval ((2 : ℤ) ^ R (pairFst q)) := by
  rw [← polynomial_map_eval hn ht ha R q]
  simp only [Polynomial.leadingCoeff, Polynomial.coeff_map, polynomial_map_natDegree,
    Polynomial.coe_evalRingHom]

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusModel
