/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.QuotientCharacteristicSpecialization
public import LeanCanny.CountingHierarchy.ModularArithmetic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Uniform quotient determinants from the constant characteristic coefficient -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue

@[expose] noncomputable def quotientDeterminantValue (p n ell B : ℕ)
    (v J : List ℕ → ℕ) (r : ℕ → List ℕ → ℕ) : ℕ :=
  (powMod p (modularSub p 0 1) (ell ^ n) *
    quotientCharacteristicValue p n ell B 0 v J r) % p

theorem quotientDeterminantValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n ell B : α → ℕ}
    {v J : α × List ℕ → ℕ} {r : α × (ℕ × List ℕ) → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hv : v ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hJ : J ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hr : r ∈ CountingFunction a (encPair enc (encPair encNat (encList encNat))) encNat) :
    (fun w => quotientDeterminantValue (p w) (n w) (ell w) (B w)
      (fun z => v (w, z)) (fun z => J (w, z)) (fun i z => r (w, i, z))) ∈
        CountingFunction (a + 8) enc encNat := by
  have hcoeff := quotientCharacteristicValue_mem E hp hn hell hB
    (ComputableInPolyTime.const 0) hv hJ hr
  have hsign := computableInPolyTime_powMod hp
    (modularSub_polyTime hp (.const 0) (.const 1))
    (ComputableInPolyTime.binary_pow' hell hn)
  exact CountingFunction.nat_mod
    (CountingFunction.nat_mul (CountingFunction.of_polyTime hsign) hcoeff)
    (CountingFunction.of_polyTime hp)

/-- Correctness refers directly to the determinant of the source matrix;
reduction modulo a prime need not preserve source degrees or separability. -/
theorem quotientDeterminantValue_cast
    {S : Type*} [CommRing S] {p n B : ℕ} [Fact p.Prime] (φ : S →+* ZMod p)
    (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S)
    (hdeg : ∀ k ≤ (d + 1) ^ n, (v ^ k * jacobian (d + 1) r).totalDegree ≤ B)
    (hcut : (d + 1) * (B + 1) + 1 < p)
    (hD : (d + 1) ^ n < p - 1) (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value Jvalue : List ℕ → ℕ) (rvalue : ℕ → List ℕ → ℕ)
    (hvalue : ∀ s < p ^ n, (value (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p)) (v.map φ))
    (hJvalue : ∀ s < p ^ n, (Jvalue (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p))
        ((jacobian (d + 1) r).map φ))
    (hrvalue : ∀ i : Fin n, ∀ s < p ^ n, (rvalue i.val (gridPoint p n s) : ZMod p) =
      eval (fun j : Fin n => (((gridPoint p n s)[j.val]?.getD 0 : ℕ) : ZMod p)) ((r i).map φ)) :
    (quotientDeterminantValue p n (d + 1) B value Jvalue rvalue : ZMod p) =
      φ (multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).det := by
  rw [quotientDeterminantValue, ZMod.natCast_mod, Nat.cast_mul,
    powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    modularSub_cast (Fact.out : p.Prime).pos, Nat.cast_zero, Nat.cast_one, zero_sub,
    quotientCharacteristicValue_eq_specialization φ d hd r hr v hdeg hcut hD hdegree
      value Jvalue rvalue hvalue hJvalue hrvalue, ZMod.natCast_zmod_val,
    Matrix.det_eq_sign_charpoly_coeff, map_mul, map_pow, map_neg, map_one, card_normalIndex]

end LeanCanny.CountingHierarchy
