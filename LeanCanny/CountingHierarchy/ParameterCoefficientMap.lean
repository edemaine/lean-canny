/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.MultivariateParameterMass
public import LeanCanny.CountingHierarchy.MultivariateParameterDegree

/-! # Mass and degree under maps of retained coefficient parameters -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

variable {ι κ τ : Type*}

theorem MultivariateParameterMass.map_le (p : MvPolynomial ι (MvPolynomial κ ℤ))
    (phi : MvPolynomial κ ℤ →+* MvPolynomial τ ℤ)
    (hphi : ∀ a, MvMass.mass (phi a) ≤ MvMass.mass a) :
    MultivariateParameterMass.mass (p.map phi) ≤ MultivariateParameterMass.mass p := by
  conv_lhs => rw [p.as_sum, map_sum]
  simp only [MvPolynomial.map_monomial]
  apply (MultivariateParameterMass.sum_le _ _).trans
  exact Finset.sum_le_sum (fun e _ => by
    rw [MultivariateParameterMass.monomial]
    exact hphi (p.coeff e))

theorem MultivariateParameterMass.map_rename_le (p : MvPolynomial ι (MvPolynomial κ ℤ)) (f : κ → τ) :
    MultivariateParameterMass.mass (p.map (MvPolynomial.rename f).toRingHom) ≤ MultivariateParameterMass.mass p :=
  MultivariateParameterMass.map_le p _ (MvMass.rename_le f)

theorem HasMultivariateParameterDegree.map_rename {p : MvPolynomial ι (MvPolynomial κ ℤ)} {H : ℕ}
    (hp : HasMultivariateParameterDegree p H) (f : κ → τ) :
    HasMultivariateParameterDegree (p.map (MvPolynomial.rename f).toRingHom) H := by
  intro e
  rw [MvPolynomial.coeff_map]
  exact (MvPolynomial.totalDegree_rename_le f (p.coeff e)).trans (hp e)

end LeanCanny.CountingHierarchy
