/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.IntegerRegularSource
public import LeanCanny.Encoding.FermatSweepCertificate

/-! # Bounded sweep certificates for constructed regular integer sources

The source regularity proved by denominator clearing supplies a valid short
direction-and-sample record. Its validity is the emptiness of one complex
projective bad-root fiber, with no input regularity certificate.
-/

@[expose] public section
namespace LeanCanny.Geometry.IntegerRegularSweepCertificate
open MvPolynomial
open LeanCanny.Algebra LeanCanny.Encoding
open FermatCriticalHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_valid_record (low : MvPolynomial (Fin (n + 2)) ℤ) (a : ℤ) (N b : ℕ)
    (hlow : low.totalDegree < N) (ha : a ≠ 0) (hN : 1 < N)
    (hp : MvMass.mass (polynomial low a N) ≤ 2 ^ b) :
    ∃ record : List Bool, record.length = (n + 1) * FermatSweepCertificate.width n N ∧
      FermatSweepCertificate.Valid ((IntegerRegularSource.lower low N b).map (Int.castRingHom ℚ))
        (IntegerRegularSource.leading (n + 1) a N b : ℚ) N record := by
  apply FermatSweepCertificate.exists_valid_record
  · exact Int.cast_ne_zero.mpr (IntegerRegularSource.leading_ne_zero a N b ha)
  · exact (PolynomialMapDegree.degree_le _ _).trans_lt (IntegerRegularSource.lower_degree low N b hlow)
  · exact hN
  · intro L _ _ x hx
    exact IntegerRegularSource.rational_regular low a N b hlow ha hN hp x hx

end LeanCanny.Geometry.IntegerRegularSweepCertificate
