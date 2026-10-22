/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateSystem
public import LeanCanny.Algebra.MacaulayGenericShift

/-! # Generic shifted multiplication for the actual tube system

The characteristic shift is independent of the perturbation and projection
parameters. Over its rational-function field, the full graded multiplication
matrix has a section. The shifted ideal contains every homogeneous polynomial
at the Macaulay level and a power of the variable ideal. Its only possible
common zero over any integral-domain coefficient extension is the origin.
No coordinate-reader or additional algebraic assumptions are needed here.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayGenericShift
open LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def system :
    Fin (TubeParameter.spatialCount (source c)) →
      MvPolynomial (Fin (TubeParameter.spatialCount (source c))) (RatFunc (Polynomial (Polynomial ℤ))) :=
  Macaulay.genericShift (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c)

theorem section_mul :
    Macaulay.genericShiftSection (TubeBivariate.rows source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)) *
      Macaulay.fullMatrix (system source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)) = 1 :=
  Macaulay.genericShiftSection_mul _ _ _

theorem vecMul_surjective :
    Function.Surjective (Matrix.vecMul · (Macaulay.fullMatrix (system source active n d ell c)
      (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)))) :=
  Macaulay.genericShift_vecMul_surjective _ _ _

theorem homogeneous_mem_span
    (f : MvPolynomial (Fin (TubeParameter.spatialCount (source c))) (RatFunc (Polynomial (Polynomial ℤ))))
    (hf : f.IsHomogeneous (Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c))) :
    f ∈ Ideal.span (Set.range (system source active n d ell c)) := by
  have hW := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hW
  exact Macaulay.genericShift_homogeneous_mem_span _ _ _
    (TubeBivariate.rows_homogeneous source active n d ell c) hW f hf

theorem power_idealOfVars_le :
    MvPolynomial.idealOfVars (Fin (TubeParameter.spatialCount (source c))) (RatFunc (Polynomial (Polynomial ℤ))) ^
        Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c) ≤
      Ideal.span (Set.range (system source active n d ell c)) := by
  have hW := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hW
  exact Macaulay.genericShift_power_idealOfVars_le _ _ _
    (TubeBivariate.rows_homogeneous source active n d ell c) hW

theorem common_zero {S : Type*} [CommRing S] [IsDomain S]
    (φ : RatFunc (Polynomial (Polynomial ℤ)) →+* S) (x : Fin (TubeParameter.spatialCount (source c)) → S)
    (hx : ∀ i, MvPolynomial.eval₂Hom φ x (system source active n d ell c i) = 0) : x = 0 := by
  have hW := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hW
  exact Macaulay.genericShift_common_zero _ _ _
    (TubeBivariate.rows_homogeneous source active n d ell c) hW φ x hx

end LeanCanny.ETR.TubeMacaulayGenericShift
