/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ParametricTiltedCoerciveEliminant
/-! # Tilted eliminants retain the actual coefficient specialization -/
@[expose] public section
namespace LeanCanny.Algebra.ParametricTiltedCoerciveEliminant
open MvPolynomial CoerciveCriticalHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

noncomputable def coefficientMap (φ : R →+* S) : Coefficient R →+* Coefficient S :=
  Polynomial.mapRingHom (Polynomial.mapRingHom φ)

theorem system_map (φ : R →+* S) (q : MvPolynomial (Fin n) R) (D : ℕ) (u i : Fin n) (j : Fin (n+1)) :
    (system q D u i j).map (coefficientMap φ)=system (q.map φ) D u i j := by
  rw [system,map_rename,TiltedCoerciveCriticalFibers.map_nativeSystem,MvPolynomial.map_map]
  have HC : (coefficientMap φ).comp constants=constants.comp φ := by
    ext x
    simp [coefficientMap,constants]
  rw [HC,← MvPolynomial.map_map]
  simp [coefficientMap,system]

theorem polynomial_map (φ : R →+* S) (q : MvPolynomial (Fin n) R) (D : ℕ) (u i : Fin n) :
    coefficientMap φ (polynomial q D u i)=polynomial (q.map φ) D u i := by
  unfold polynomial
  rw [MacaulayUniversal.polynomialValue_map]
  congr 1
  funext j
  exact system_map φ q D u i j

end LeanCanny.Algebra.ParametricTiltedCoerciveEliminant
