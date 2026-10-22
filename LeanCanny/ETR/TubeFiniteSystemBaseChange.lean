/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicFinitePersistence

/-! # Coefficient extension of the actual compiled affine tube system

Specializing the level and then extending coefficients agrees with extending
the level first. This permits rational level systems to use the finite complex
fibers already supplied by the stored parameter packets.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Algebra MvPolynomial
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
variable {K E : Type*} [Field K] [Field E]

theorem map_finiteChartVariables (φ : K →+* E) (bits : List Bool)
    (j : Fin (TubeParameter.spatialCount bits)) :
    MvPolynomial.map φ (finiteChartVariables bits j) = finiteChartVariables bits j := by
  unfold finiteChartVariables
  refine Fin.cases ?_ (fun i => ?_) j
  · exact map_one _
  · exact MvPolynomial.map_X φ _

theorem map_finiteCoefficientMap (φ : K →+* E) (bits : List Bool) (alpha : K) :
    (MvPolynomial.map φ).comp (finiteCoefficientMap bits alpha) =
      finiteCoefficientMap bits (φ alpha) := by
  ext <;> simp [finiteCoefficientMap]

theorem map_finiteSystem (φ : K →+* E) (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (c : List Bool) (alpha : K) (j : Fin (TubeParameter.spatialCount (source c))) :
    (finiteSystem source active n d ell c alpha j).map φ =
      finiteSystem source active n d ell c (φ alpha) j := by
  change (MvPolynomial.map φ) (MvPolynomial.eval₂ (finiteCoefficientMap (source c) alpha)
    (finiteChartVariables (source c)) (TubeBivariate.rows source active n d ell c j)) = _
  rw [MvPolynomial.eval₂_comp_left, map_finiteCoefficientMap]
  have hx : (MvPolynomial.map φ) ∘ finiteChartVariables (source c) =
      finiteChartVariables (source c) := funext (map_finiteChartVariables φ (source c))
  rw [hx]
  rfl

end LeanCanny.ETR.TubeCharacteristicQuotient
