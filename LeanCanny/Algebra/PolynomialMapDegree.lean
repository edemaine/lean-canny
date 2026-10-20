/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Coefficient maps do not increase multivariate total degree -/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialMapDegree

theorem degree_le {ι R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (p : MvPolynomial ι R) : (p.map φ).totalDegree ≤ p.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (MvPolynomial.support_map_subset φ p)

end LeanCanny.Algebra.PolynomialMapDegree
