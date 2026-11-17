/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FingerprintModularEvaluation
public import LeanCanny.CountingHierarchy.FingerprintLabelPolynomial
public import LeanCanny.CountingHierarchy.RootLabelModularCorrectness

/-! # Correctness of modular fingerprint-label evaluation -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators Classical

theorem binaryClearedNumerator_cast {p m : ℕ} [Fact p.Prime] (B s : ℕ)
    (g : Fin m → Polynomial ℤ) (x : ZMod p) (den num : ℕ → ℕ)
    (hden : ∀ i : Fin m, (den i.val : ZMod p) =
      (signTestDenominator B s (g i)).eval₂ (Int.castRingHom (ZMod p)) x)
    (hnum : ∀ i : Fin m, (num i.val : ZMod p) =
      (signTestNumerator B s (g i)).eval₂ (Int.castRingHom (ZMod p)) x)
    (i : Fin m) :
    (binaryClearedNumerator p m den num i.val : ZMod p) =
      (signTestClearedNumerator B s g i).eval₂ (Int.castRingHom (ZMod p)) x := by
  rw [binaryClearedNumerator, ZMod.natCast_mod, Nat.cast_mul, binaryModularProduct_cast,
    hnum i, signTestClearedNumerator, Polynomial.eval₂_mul, Polynomial.eval₂_finsetProd]
  congr 1
  have he : (∏ j : Fin m, ((if j.val = i.val then 1 else den j.val : ℕ) : ZMod p)) =
      ∏ j : Fin m, if j = i then 1 else
        (signTestDenominator B s (g j)).eval₂ (Int.castRingHom (ZMod p)) x := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [Nat.cast_ite, Nat.cast_one, Fin.val_inj, hden j]
  exact he.trans (product_omit_one _ i)

/-- Evaluation equals the actual integer label polynomial, including at
primes where some denominators reduce to zero. -/
theorem modularFingerprintLabel_cast {p m : ℕ} [Fact p.Prime] (B s : ℕ)
    (g : Fin (m + 1) → Polynomial ℤ) (w : Fin m → ℕ) (target : ℤ) (x : ZMod p)
    (den num weight : ℕ → ℕ) (targetValue : ℕ)
    (hden : ∀ i : Fin (m + 1), (den i.val : ZMod p) =
      (signTestDenominator B s (g i)).eval₂ (Int.castRingHom (ZMod p)) x)
    (hnum : ∀ i : Fin (m + 1), (num i.val : ZMod p) =
      (signTestNumerator B s (g i)).eval₂ (Int.castRingHom (ZMod p)) x)
    (hw : ∀ i : Fin m, (weight i.val : ZMod p) = (w i : ZMod p))
    (ht : (targetValue : ZMod p) = (target : ZMod p)) :
    (modularFingerprintLabel p m den num weight targetValue : ZMod p) =
      (fingerprintLabelPolynomial B s g w target).eval₂ (Int.castRingHom (ZMod p)) x := by
  have hE : (binaryModularProduct p (m + 1) den : ZMod p) =
      (signTestCommonDenominator B s g).eval₂ (Int.castRingHom (ZMod p)) x := by
    rw [binaryModularProduct_cast, signTestCommonDenominator, Polynomial.eval₂_finsetProd]
    exact Finset.prod_congr rfl (fun i _ => hden i)
  have hT (i : Fin (m + 1)) := binaryClearedNumerator_cast B s g x den num hden hnum i
  have hS : ((∑ i ∈ Finset.range m, weight i * binaryClearedNumerator p (m + 1) den num (i + 1) : ℕ) : ZMod p) =
      ∑ i : Fin m, (w i : ZMod p) *
        (signTestClearedNumerator B s g i.succ).eval₂ (Int.castRingHom (ZMod p)) x := by
    rw [Nat.cast_sum, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_mul, hw i]
    exact congrArg (fun z : ZMod p => (w i : ZMod p) * z) (hT i.succ)
  have hzero : (binaryClearedNumerator p (m + 1) den num 0 : ZMod p) =
      (signTestClearedNumerator B s g 0).eval₂ (Int.castRingHom (ZMod p)) x := hT 0
  have hp := (Fact.out : p.Prime).ne_zero
  simp only [modularFingerprintLabel, modularSub_cast (Nat.pos_of_ne_zero hp),
    powMod_of_ne_zero hp, ZMod.natCast_mod, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat,
    hE, hzero, hS, ht]
  simp only [fingerprintLabelPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_finsetSum,
    Int.coe_castRingHom, Int.cast_ofNat, Int.cast_natCast]

end LeanCanny.CountingHierarchy
