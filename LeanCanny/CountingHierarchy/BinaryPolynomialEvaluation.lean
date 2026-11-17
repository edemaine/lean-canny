/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Range
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Evaluating binary-degree polynomials from uniform coefficient access -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

noncomputable def binaryPolynomialValue (p D t : ℕ) (coeff : ℕ → ℕ) : ℕ :=
  (∑ k ∈ Finset.range (D + 1), coeff k * powMod p t k) % p

theorem binaryPolynomialValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D t : α → ℕ} {coeff : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (ht : ComputableInPolyTime t enc encNat)
    (hc : coeff ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => binaryPolynomialValue (p w) (D w) (t w) (fun k => coeff (w, k))) ∈
      CountingFunction (a + 1) enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hk := ComputableInPolyTime.snd enc encNat
  have hpow := CountingFunction.of_polyTime (a := a) (computableInPolyTime_powMod (hp.comp hf) (ht.comp hf) hk)
  have hsum := CountingFunction.sum_range E (CountingFunction.nat_mul hc hpow)
    (ComputableInPolyTime.binary_add' hD (.const 1))
  exact CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)

theorem binaryPolynomialValue_cast {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]
    (phi : R →+* ZMod p) (P : Polynomial R) (D t : ℕ) (hD : P.natDegree ≤ D)
    (coeff : ℕ → ℕ) (hc : ∀ k ≤ D, (coeff k : ZMod p) = phi (P.coeff k)) :
    (binaryPolynomialValue p D t coeff : ZMod p) = P.eval₂ phi (t : ZMod p) := by
  rw [binaryPolynomialValue, ZMod.natCast_mod, Nat.cast_sum,
    Polynomial.eval₂_eq_sum_range' phi (by omega : P.natDegree < D + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_mul, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_pow, hc k (by have := Finset.mem_range.mp hk; omega)]

end LeanCanny.CountingHierarchy
