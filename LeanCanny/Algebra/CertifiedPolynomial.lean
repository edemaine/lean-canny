/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DerivativeCoefficientSpace

/-! # Certified streamed bivariate integer coefficients

The determinant and dyadic stages share one inner/outer query order. The
coefficient program carries its native space certificate and correctness on
canonical index packets.
-/

@[expose] public section

namespace LeanCanny.Algebra.CertifiedPolynomial
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

/-- The determinant backend's inner/outer index order, independent of matrices. -/
structure BivariateReader (p : List Bool → (ℤ[X])[X]) where
  coefficient : List Bool → List Bool
  evaluator : SpaceFunction coefficient
  coefficient_eq : ∀ q u v, coefficient
    (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      residueBits ((((p (pairFst q)).coeff v).coeff u : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))

end LeanCanny.Algebra.CertifiedPolynomial
