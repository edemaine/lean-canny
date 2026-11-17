/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RootLabelModularEvaluation
public import CslibFrontier.Foundations.FieldTheory.Finite.Basic

/-! # Correctness of modular evaluation for actual cleared root labels -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators Classical

lemma unaryModularProduct_cast (n p : ℕ) (v : ℕ → ℕ) :
    (unaryModularProduct n p v : ZMod p) =
      ∏ i : Fin n, (v i.val : ZMod p) := by
  rw [unaryModularProduct_eq, ZMod.natCast_mod, Nat.cast_prod, Finset.prod_range]

lemma unaryModularSum_cast (n p : ℕ) (v : ℕ → ℕ) :
    (unaryModularSum n p v : ZMod p) =
      ∑ i : Fin n, (v i.val : ZMod p) := by
  rw [unaryModularSum_eq, ZMod.natCast_mod, Nat.cast_sum, Finset.sum_range]

lemma product_omit_one {R : Type*} [CommMonoid R] {m : ℕ} (f : Fin m → R) (i : Fin m) :
    (∏ j : Fin m, if j = i then 1 else f j) = ∏ j ∈ Finset.univ.erase i, f j := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true, one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (Finset.ne_of_mem_erase hj)

theorem modularClearedNumerator_cast {p m : ℕ} (B s : ℕ)
    (g : Fin m → Polynomial ℤ) (x : ZMod p) (den num : ℕ → ℕ)
    (hden : ∀ i : Fin m, (den i.val : ZMod p) =
      (signTestDenominator B s (g i)).eval₂ (Int.castRingHom (ZMod p)) x)
    (hnum : ∀ i : Fin m, (num i.val : ZMod p) =
      (signTestNumerator B s (g i)).eval₂ (Int.castRingHom (ZMod p)) x)
    (i : Fin m) :
    (modularClearedNumerator p m den num i.val : ZMod p) =
      (signTestClearedNumerator B s g i).eval₂ (Int.castRingHom (ZMod p)) x := by
  rw [modularClearedNumerator, ZMod.natCast_mod, Nat.cast_mul,
    unaryModularProduct_cast, hnum i, signTestClearedNumerator,
    Polynomial.eval₂_mul, Polynomial.eval₂_finsetProd]
  congr 1
  have he : (∏ j : Fin m, ((if j.val = i.val then 1 else den j.val : ℕ) : ZMod p)) =
      ∏ j : Fin m, if j = i then 1 else
        (signTestDenominator B s (g j)).eval₂ (Int.castRingHom (ZMod p)) x := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [Nat.cast_ite, Nat.cast_one, Fin.val_inj, hden j]
  exact he.trans (product_omit_one _ i)

/-- The modular score equals evaluation of the actual integer polynomial;
no nonvanishing-denominator premise is needed for this algebraic identity. -/
theorem modularRootLabel_cast {p m : ℕ} [Fact p.Prime] (B s : ℕ)
    (g : Fin m → Polynomial ℤ) (t : Fin m → SignType) (x : ZMod p)
    (den num target : ℕ → ℕ)
    (hden : ∀ i : Fin m, (den i.val : ZMod p) =
      (signTestDenominator B s (g i)).eval₂ (Int.castRingHom (ZMod p)) x)
    (hnum : ∀ i : Fin m, (num i.val : ZMod p) =
      (signTestNumerator B s (g i)).eval₂ (Int.castRingHom (ZMod p)) x)
    (htarget : ∀ i : Fin m, (target i.val : ZMod p) = ((t i : ℤ) : ZMod p)) :
    (modularRootLabel p m den num target : ZMod p) =
      (rootLabelPolynomial B s g t).eval₂ (Int.castRingHom (ZMod p)) x := by
  have hE : (unaryModularProduct m p den : ZMod p) =
      (signTestCommonDenominator B s g).eval₂ (Int.castRingHom (ZMod p)) x := by
    rw [unaryModularProduct_cast, signTestCommonDenominator, Polynomial.eval₂_finsetProd]
    exact Finset.prod_congr rfl (fun i _ => hden i)
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [modularRootLabel, modularSub_cast (Nat.pos_of_ne_zero hp),
    powMod_of_ne_zero hp, ZMod.natCast_mod, Nat.cast_pow, hE,
    Nat.cast_mul, Nat.cast_ofNat, unaryModularSum_cast,
    rootLabelPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_finsetSum]
  simp only [Int.coe_castRingHom, Int.cast_ofNat]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [powMod_of_ne_zero hp, ZMod.natCast_mod, Nat.cast_pow,
    modularSub_cast (Nat.pos_of_ne_zero hp), Nat.cast_mul, hE,
    modularClearedNumerator_cast B s g x den num hden hnum i, htarget i]
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Int.coe_castRingHom]

end LeanCanny.CountingHierarchy
