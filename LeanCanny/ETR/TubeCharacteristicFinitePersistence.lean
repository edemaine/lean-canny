/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFiniteFiber
public import LeanCanny.ETR.TubeCharacteristicRegularPersistence
/-! # Finite affine tube fibers, including singular roots

Express the projection parameter and affine spatial coordinates as
polynomial variables. Finiteness of this affine zero set over an algebraically
closed field forces the lowest characteristic quotient coefficient to vanish
at every root. The proof needs no Jacobian invertibility, and permits
positive-dimensional components in the projective hyperplane at infinity.
A coefficient-extension argument supplies the same conclusion for real
roots when the affine zero set is finite over an algebraically closed
extension of the reals. `TubeCharacteristicGeometricPersistence` supplies a
geometric finiteness bridge under explicit substitution-parameter identities.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Algebra
open MvPolynomial
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
variable {K : Type*} [Field K] [IsAlgClosed K]
variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def finiteParameterIndex (bits : List Bool) : Fin (TubeParameter.spatialCount bits) :=
  ⟨0, by unfold TubeParameter.spatialCount; omega⟩

noncomputable def finiteChartVariables (bits : List Bool) :
    Fin (TubeParameter.spatialCount bits) → MvPolynomial (Fin (TubeParameter.spatialCount bits)) K :=
  Fin.cons 1 (fun j => MvPolynomial.X j.succ)

noncomputable def finiteCoefficientMap (bits : List Bool) (epsilon : K) :
    Polynomial (Polynomial ℤ) →+* MvPolynomial (Fin (TubeParameter.spatialCount bits)) K :=
  Polynomial.eval₂RingHom (MvPolynomial.C.comp (Polynomial.eval₂RingHom (Int.castRingHom K) epsilon))
    (MvPolynomial.X (finiteParameterIndex bits))

omit [IsAlgClosed K] in
theorem eval_finiteCoefficientMap (bits : List Bool) (epsilon : K) (z : Fin (TubeParameter.spatialCount bits) → K) :
    (MvPolynomial.eval z).comp (finiteCoefficientMap bits epsilon) = regularCoefficientMap epsilon (z (finiteParameterIndex bits)) := by
  ext <;> simp [finiteCoefficientMap, regularCoefficientMap]

omit [IsAlgClosed K] in
theorem eval_finiteChartVariables_zero (bits : List Bool) (z : Fin (TubeParameter.spatialCount bits) → K) :
    MvPolynomial.eval z (finiteChartVariables bits (finiteParameterIndex bits)) = 1 := by
  exact map_one _

noncomputable def finiteSystem (epsilon : K) :
    Fin (TubeParameter.spatialCount (source c)) → MvPolynomial (Fin (TubeParameter.spatialCount (source c))) K :=
  MacaulayFiniteFiber.originalSystem (TubeBivariate.rows source active n d ell c)
    (finiteCoefficientMap (source c) epsilon) (finiteChartVariables (source c))

omit [IsAlgClosed K] in
theorem eval_finiteSystem (epsilon : K) (z : Fin (TubeParameter.spatialCount (source c)) → K)
    (i : Fin (TubeParameter.spatialCount (source c))) :
    MvPolynomial.eval z (finiteSystem source active n d ell c epsilon i) =
      MvPolynomial.eval₂ (regularCoefficientMap epsilon (z (finiteParameterIndex (source c))))
        (fun j => MvPolynomial.eval z (finiteChartVariables (source c) j)) (TubeBivariate.rows source active n d ell c i) := by
  change MvPolynomial.eval z (MvPolynomial.eval₂ (finiteCoefficientMap (source c) epsilon)
    (finiteChartVariables (source c)) (TubeBivariate.rows source active n d ell c i)) = _
  rw [MvPolynomial.eval_eval₂]
  exact congrArg (fun f : Polynomial (Polynomial ℤ) →+* K =>
    MvPolynomial.eval₂ f (fun j => MvPolynomial.eval z (finiteChartVariables (source c) j))
      (TubeBivariate.rows source active n d ell c i)) (eval_finiteCoefficientMap (source c) epsilon z)

omit [IsAlgClosed K] in
theorem eval_finiteChartVariables (bits : List Bool) (z : Fin (TubeParameter.spatialCount bits) → K)
    (i : Fin (TubeParameter.spatialCount bits)) :
    MvPolynomial.eval z (finiteChartVariables bits i) = (Fin.cons (1 : K) (fun j => z j.succ) : Fin (TubeParameter.spatialCount bits) → K) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact map_one _
  · exact MvPolynomial.eval_X _

noncomputable def finitePoint {S : Type*} (bits : List Bool) (a : RegularChart bits S) :
    Fin (TubeParameter.spatialCount bits) → S := Fin.cons a.1 a.2

theorem regularCoefficientMap_comp {S T : Type*} [CommRing S] [CommRing T]
    (φ : S →+* T) (epsilon u : S) :
    φ.comp (regularCoefficientMap epsilon u) = regularCoefficientMap (φ epsilon) (φ u) := by
  ext <;> simp [regularCoefficientMap]

private theorem finite_persistence_width_bound :
    Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c) < 2 ^ TubeCleared.matrixWidth (source c) := by
  have hw := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hw
  exact hw

theorem polynomial_trailingCoeff_eval_eq_zero_of_finite_fiber (epsilon : K)
    (hfinite : (zeroLocus K (ProjectiveNullstellensatz.generated (finiteSystem source active n d ell c epsilon))).Finite)
    (z : Fin (TubeParameter.spatialCount (source c)) → K)
    (hz : z ∈ zeroLocus K (ProjectiveNullstellensatz.generated (finiteSystem source active n d ell c epsilon))) :
    regularCoefficientMap epsilon (z (finiteParameterIndex (source c))) (polynomial source active n d ell c).trailingCoeff = 0 := by
  have hW := finite_persistence_width_bound source c
  have hd : ∀ i : Fin (TubeParameter.spatialCount (source c)),
      0 < MacaulayBits.Degrees (TubeCleared.layout source) c i := fun i => TubeCleared.degree_pos source c i.val
  have hdegree := MacaulayUniversal.degree_lt_width _ _ hd hW
  have he := MacaulayFiniteFiber.trailingCoeff_eval_eq_zero_of_finite_fiber
    (TubeBivariate.rows source active n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (TubeCleared.matrixWidth (source c)) hdegree hW (TubeBivariate.rows_homogeneous source active n d ell c) hd
    (finiteCoefficientMap (source c) epsilon) (finiteChartVariables (source c))
    (fun z => ⟨finiteParameterIndex (source c), fun hn => one_ne_zero
      ((eval_finiteChartVariables_zero (source c) z).symm.trans hn)⟩) hfinite z hz
  have hm := congrArg (fun f : Polynomial (Polynomial ℤ) →+* K =>
    f (polynomial source active n d ell c).trailingCoeff) (eval_finiteCoefficientMap (source c) epsilon z)
  exact hm.symm.trans he

theorem lowestProjectionPolynomial_eval_eq_zero_of_finite_fiber (epsilon : K)
    (hfinite : (zeroLocus K (ProjectiveNullstellensatz.generated (finiteSystem source active n d ell c epsilon))).Finite)
    (z : Fin (TubeParameter.spatialCount (source c)) → K)
    (hz : z ∈ zeroLocus K (ProjectiveNullstellensatz.generated (finiteSystem source active n d ell c epsilon))) :
    Polynomial.eval (z (finiteParameterIndex (source c))) (lowestProjectionPolynomial source active n d ell c epsilon) = 0 := by
  have he := polynomial_trailingCoeff_eval_eq_zero_of_finite_fiber source active n d ell c epsilon hfinite z hz
  simpa only [lowestProjectionPolynomial, Polynomial.eval_map, regularCoefficientMap, Polynomial.coe_eval₂RingHom] using he

section RealExtension
variable {L : Type*} [Field L] [IsAlgClosed L] [Algebra ℝ L]

theorem polynomial_trailingCoeff_eval_eq_zero_of_finite_extension_fiber (epsilon : ℝ)
    (hfinite : (zeroLocus L (ProjectiveNullstellensatz.generated
      (finiteSystem source active n d ell c (algebraMap ℝ L epsilon)))).Finite)
    (a : RegularChart (source c) ℝ) (hroot : regularSystem source active n d ell c epsilon a = 0) :
    regularCoefficientMap epsilon a.1 (polynomial source active n d ell c).trailingCoeff = 0 := by
  let φ := algebraMap ℝ L
  let z : Fin (TubeParameter.spatialCount (source c)) → L := fun i => φ (finitePoint (source c) a i)
  have hchart : (fun j => MvPolynomial.eval z (finiteChartVariables (source c) j)) =
      φ ∘ regularChart (source c) a := by
    funext j
    rw [eval_finiteChartVariables]
    refine Fin.cases ?_ (fun _ => rfl) j
    exact (map_one φ).symm
  have hparam : z (finiteParameterIndex (source c)) = φ a.1 := rfl
  have hz : z ∈ zeroLocus L (ProjectiveNullstellensatz.generated
      (finiteSystem source active n d ell c (φ epsilon))) := by
    rw [ProjectiveNullstellensatz.zeroLocus_generated]
    intro i
    rw [eval_finiteSystem, hchart, hparam, ← regularCoefficientMap_comp φ epsilon a.1,
      ← MvPolynomial.eval₂_comp_left]
    have he : MvPolynomial.eval₂ (regularCoefficientMap epsilon a.1) (regularChart (source c) a)
        (TubeBivariate.rows source active n d ell c i) = 0 := congrFun hroot i
    rw [he, map_zero]
  have he := polynomial_trailingCoeff_eval_eq_zero_of_finite_fiber source active n d ell c
    (φ epsilon) hfinite z hz
  rw [hparam, ← regularCoefficientMap_comp φ epsilon a.1] at he
  exact φ.injective (he.trans (map_zero φ).symm)

theorem lowestProjectionPolynomial_eval_eq_zero_of_finite_extension_fiber (epsilon : ℝ)
    (hfinite : (zeroLocus L (ProjectiveNullstellensatz.generated
      (finiteSystem source active n d ell c (algebraMap ℝ L epsilon)))).Finite)
    (a : RegularChart (source c) ℝ) (hroot : regularSystem source active n d ell c epsilon a = 0) :
    Polynomial.eval a.1 (lowestProjectionPolynomial source active n d ell c epsilon) = 0 := by
  have he := polynomial_trailingCoeff_eval_eq_zero_of_finite_extension_fiber source active n d ell c epsilon hfinite a hroot
  simpa only [lowestProjectionPolynomial, Polynomial.eval_map, regularCoefficientMap, Polynomial.coe_eval₂RingHom] using he
end RealExtension

end LeanCanny.ETR.TubeCharacteristicQuotient
