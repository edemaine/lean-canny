/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CertifiedBivariateTernaryPower
/-! # Ternary powers commute with the literal coefficient encoding -/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateTernaryPowerBits
open LeanCanny.Encoding LeanCanny.Computation

noncomputable def reader (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A W p))
    (e : List Bool→Fin 3) (he : BinaryFn (fun c=>(e c).val)) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A W (fun c=>p c^(e c).val)) :=by
  have E : (fun c=>FixedWidthBivariateReader.polynomial A W p c^(e c).val)=
      FixedWidthBivariateReader.polynomial A W (fun c=>p c^(e c).val) :=by
    funext c
    exact (Polynomial.map_pow _ _).symm
  exact E ▸ CertifiedBivariateTernaryPower.reader R e he

end LeanCanny.Algebra.FixedWidthBivariateTernaryPowerBits
