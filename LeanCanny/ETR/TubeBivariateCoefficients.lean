/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateSystem

/-! # Scalar source identities for the full bivariate tube system

The linear row is constant in the inner variable, and regular rows are constant
in the outer variable. Scalar identities keep query normalization outside
multivariate polynomials whose coordinate types depend on the input.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeBivariate
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Algebra.RationalSubstitution Algebra.MatrixPower
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def rawLinear (bits : List Bool) (ell : ℕ → ℤ) (W k v : ℕ) : ℤ :=
  ((LinearCoefficientBits.polynomial (fun _ => TubeParameter.spatialCount bits)
    (TubeLinear.scalar (fun _ => ell)) []).coeff
      (Indexed.exponentVector (TubeParameter.spatialCount bits) (FixedWidthPolynomial.entry W k))).coeff v

theorem linear_coefficient_eq_raw (source : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (degree : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    LinearCoefficientBits.coefficient (TubeParameter.spatialCount ∘ source) (TubeCleared.matrixWidth ∘ source)
      (TubeLinear.scalar ell) degree c k = rawLinear (source c) (ell c) (TubeCleared.matrixWidth (source c)) k
        (Nat.fromBitsLE (degree c)) := rfl

attribute [local irreducible] rawLinear TubeCleared.rawCoefficient

theorem linear_packet (source : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (degree modulus : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    LinearCoefficientBits.value (TubeParameter.spatialCount ∘ source) (TubeCleared.matrixWidth ∘ source)
      (TubeLinear.scalar ell) degree modulus (pair c (BinaryNatCode.encode k)) =
      IntegerBits.coefficientResidue (rawLinear (source c) (ell c) (TubeCleared.matrixWidth (source c)) k
        (Nat.fromBitsLE (degree c))) (Nat.fromBitsLE (modulus c) + 1) := by
  rw [LinearCoefficientBits.value_packet, linear_coefficient_eq_raw]

noncomputable def rowCoefficient (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (i : Fin (TubeParameter.spatialCount (source c))) (k u v : ℕ) : ℤ :=
  (((rows source active n d ell c i).coeff (Indexed.exponentVector (TubeParameter.spatialCount (source c))
    (FixedWidthPolynomial.entry (TubeCleared.matrixWidth (source c)) k))).coeff v).coeff u

theorem regular_coefficient (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (i : Fin (TubeParameter.spatialCount (source c))) (k u v : ℕ)
    (hi : i.val ≠ 0) :
    rowCoefficient source active n d ell c i k u v =
      if v = 0 then (TubeCleared.rawCoefficient (source c) (active c) (BinaryNatCode.encode (i.val - 1))
        (n c) (d c) (TubeCleared.matrixWidth (source c)) k).coeff u else 0 := by
  rw [rowCoefficient, rows, ite_eq_right hi, MvPolynomial.coeff_map]
  rw [TubeCleared.row_eq_raw, TubeCleared.raw_coefficient_rename]
  change ((Polynomial.C (TubeCleared.rawCoefficient _ _ _ _ _ _ _)).coeff v).coeff u = _
  by_cases hv : v = 0
  · simp only [hv, Polynomial.coeff_C_zero, ite_true]
  · simp [Polynomial.coeff_C, hv]

theorem linear_coefficient (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (i : Fin (TubeParameter.spatialCount (source c))) (k u v : ℕ)
    (hi : i.val = 0) :
    rowCoefficient source active n d ell c i k u v =
      if u = 0 then rawLinear (source c) (ell c) (TubeCleared.matrixWidth (source c)) k v else 0 := by
  rw [rowCoefficient, rows, ite_eq_left hi, MvPolynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  by_cases hu : u = 0
  · rw [hu, Polynomial.coeff_C_zero, ite_eq_left rfl]
    unfold rawLinear
    rfl
  · rw [Polynomial.coeff_C]
    simp only [hu, ite_false]

theorem reduction_coefficient {σ : Type*} (p : MvPolynomial σ (Polynomial (Polynomial ℤ)))
    (e : σ →₀ ℕ) (u v m : ℕ) :
    ((((p.map (reduction m)).coeff e).coeff v).coeff u) = (((p.coeff e).coeff v).coeff u : ZMod m) := by
  rw [MvPolynomial.coeff_map]
  change ((((p.coeff e).map (Polynomial.mapRingHom (Int.castRingHom (ZMod m)))).coeff v).coeff u) = _
  rw [Polynomial.coeff_map]
  change ((((p.coeff e).coeff v).map (Int.castRingHom (ZMod m))).coeff u) = _
  rw [Polynomial.coeff_map]
  rfl

end LeanCanny.ETR.TubeBivariate
