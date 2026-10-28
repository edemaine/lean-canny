/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PreparedPolynomialContext
public import LeanCanny.Algebra.CoefficientMass
public import LeanCanny.Computation.PolyTimeBinaryNat
public import Mathlib.FieldTheory.Separable

/-! # Native separable parameter families

Separability over the rationals implies simplicity of parameter roots in
every characteristic-zero field. Native binary degree and mass controls and
coefficient readers are packaged independently of any original parent syntax.
Actual-sample filtering is a separate obligation.
-/

@[expose] public section
namespace LeanCanny.Algebra.SeparablePolynomialFamily
open LeanCanny.Encoding LeanCanny.Computation Polynomial

structure Source where
  polynomial : List Bool → ℤ[X]
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  degree_le : ∀ u, (polynomial u).natDegree ≤ degree u
  mass_le : ∀ u, coefficientMass (polynomial u) ≤ 2 ^ mass u
  separable : ∀ u, ((polynomial u).map (Int.castRingHom ℚ)).Separable

structure Access (P : Source) : Prop where
  degree : BinaryFn P.degree
  mass : BinaryFn P.mass
  coefficient : SpaceFunction (PrimitivePairBits.coefficient P.polynomial)

theorem separable_in_field (P : Source) (u : List Bool) {K : Type*} [Field K] [CharZero K] :
    ((P.polynomial u).map (Int.castRingHom K)).Separable := by
  have H := (P.separable u).map (f := Rat.castHom K)
  rw [Polynomial.map_map] at H
  have he : (Rat.castHom K).comp (Int.castRingHom ℚ) = Int.castRingHom K := RingHom.ext_int _ _
  rwa [he] at H

theorem derivative_ne_zero (P : Source) (u : List Bool) {K : Type*} [Field K] [CharZero K]
    (theta : K) (ht : (P.polynomial u).eval₂ (Int.castRingHom K) theta = 0) :
    (P.polynomial u).derivative.eval₂ (Int.castRingHom K) theta ≠ 0 := by
  have H := (separable_in_field P u (K := K)).eval₂_derivative_ne_zero (RingHom.id K)
    (x := theta) (by simpa only [Polynomial.eval₂_map, RingHom.id_comp] using ht)
  simpa only [Polynomial.derivative_map, Polynomial.eval₂_map, RingHom.id_comp] using H

def comp (P : Source) (context : List Bool → List Bool) : Source where
  polynomial := P.polynomial ∘ context
  degree := P.degree ∘ context
  mass := P.mass ∘ context
  degree_le u := P.degree_le (context u)
  mass_le u := P.mass_le (context u)
  separable u := P.separable (context u)

theorem comp_access {P : Source} (A : Access P) (context : List Bool → List Bool)
    (hc : context ∈ FP) : Access (comp P context) :=
  ⟨A.degree.comp hc, A.mass.comp hc,
    PrimitivePairBits.withContextEvaluator _ context (SpaceFunction.ofFP _ hc) A.coefficient⟩

end LeanCanny.Algebra.SeparablePolynomialFamily
