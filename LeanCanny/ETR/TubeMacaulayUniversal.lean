/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayKernelBasis
public import LeanCanny.Algebra.MacaulayUniversalSpecialization

/-! # Universal specialization of the tube characteristic determinants

The existing tube homogeneity, positive degrees, and width bound reconstruct
the full subtractive system by specializing universal coefficients. The
universal numerator and denominator specialize to the actual characteristic
determinants. Universal divisibility would therefore give the required
characteristic divisibility; that universal premise remains unproved.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayUniversal
open LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

abbrev Coefficient := Polynomial (Polynomial (Polynomial ℤ))

-- Keep the spatial arity explicit when rewriting the determinant identities.
noncomputable abbrev degrees (source : List Bool → List Bool) (c : List Bool) :
    Fin (TubeParameter.spatialCount (source c)) → ℕ :=
  fun i => (TubeCleared.layout source).degree c i.val

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def system :
    Fin (TubeParameter.spatialCount (source c)) → MvPolynomial (Fin (TubeParameter.spatialCount (source c))) Coefficient :=
  Macaulay.subtractiveSystem (TubeBivariate.rows source active n d ell c) (degrees source c)

theorem homogeneous (i : Fin (TubeParameter.spatialCount (source c))) :
    (system source active n d ell c i).IsHomogeneous (MacaulayBits.Degrees (TubeCleared.layout source) c i) :=
  Macaulay.subtractiveSystem_homogeneous _ _ (TubeBivariate.rows_homogeneous source active n d ell c) i

noncomputable def coefficientMap :
    MacaulayUniversal.CoefficientRing (TubeParameter.spatialCount (source c)) Coefficient →+* Coefficient :=
  MvPolynomial.eval (fun v => (system source active n d ell c v.1).coeff v.2)

theorem system_specialization (i : Fin (TubeParameter.spatialCount (source c))) :
    (MacaulayUniversal.system (R := Coefficient) (degrees source c)
      (TubeCleared.matrixWidth (source c)) (Equiv.refl _) i).map (coefficientMap source active n d ell c) =
        system source active n d ell c i :=
  MacaulayUniversal.specialize_system_of_level _ _ _ (homogeneous source active n d ell c)
    (fun j => TubeCleared.degree_pos source c j.val) (TubeMacaulayKernelBasis.width_bound source c) i

theorem numerator_specialization :
    coefficientMap source active n d ell c
      (MacaulayUniversal.numerator (R := Coefficient) (degrees source c)
        (TubeCleared.matrixWidth (source c)) (Equiv.refl _)) =
      (AffineCharacteristic.subtractiveMatrix (Macaulay.activeMinor (TubeBivariate.rows source active n d ell c)
        (degrees source c) (TubeCleared.matrixWidth (source c)))).det := by
  have h := MacaulayUniversal.specialize_numerator (R := Coefficient)
    (n := TubeParameter.spatialCount (source c)) (degrees source c)
    (TubeCleared.matrixWidth (source c)) (system source active n d ell c) (homogeneous source active n d ell c)
    (fun j => TubeCleared.degree_pos source c j.val) (TubeMacaulayKernelBasis.width_bound source c)
  change coefficientMap source active n d ell c _ =
    (Macaulay.activeMinor (system source active n d ell c) _ _).det at h
  rw [system, Macaulay.activeMinor_subtractiveSystem] at h
  exact h

theorem denominator_specialization :
    coefficientMap source active n d ell c
      (MacaulayUniversal.denominator (R := Coefficient) (degrees source c)
        (TubeCleared.matrixWidth (source c)) (Equiv.refl _)) =
      (AffineCharacteristic.subtractiveMatrix (Macaulay.extraneousMinor (TubeBivariate.rows source active n d ell c)
        (degrees source c) (TubeCleared.matrixWidth (source c)))).det := by
  have h := MacaulayUniversal.specialize_denominator (R := Coefficient)
    (n := TubeParameter.spatialCount (source c)) (degrees source c)
    (TubeCleared.matrixWidth (source c)) (system source active n d ell c) (homogeneous source active n d ell c)
    (fun j => TubeCleared.degree_pos source c j.val) (TubeMacaulayKernelBasis.width_bound source c)
  change coefficientMap source active n d ell c _ =
    (Macaulay.extraneousMinor (system source active n d ell c) _ _).det at h
  rw [system, Macaulay.extraneousMinor_subtractiveSystem] at h
  exact h

end LeanCanny.ETR.TubeMacaulayUniversal
