/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicPolynomial
public import LeanCanny.Geometry.MacaulayRegularPersistence

/-! # Regular affine roots annihilate the lowest tube quotient coefficient

Fix the perturbation parameter and use the projective chart with first
coordinate one. The unknowns are the projection parameter and the remaining
spatial coordinates. At a root with invertible Jacobian, the implicit
function theorem constructs nearby characteristic-shifted roots. Thus the
lowest coefficient of the actual quotient vanishes at that root's projection.
The general persistence theorem for singular proper components remains open.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Algebra LeanCanny.Geometry
open Filter
open scoped Topology Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

abbrev RegularChart (bits : List Bool) (K : Type*) :=
  K × (Fin (TubeProjectionEncoding.pointCount (TubeIndexed.arity bits) + 1) → K)

variable {K : Type*} [RCLike K]

noncomputable def regularCoefficientMap {S : Type*} [CommRing S] (epsilon u : S) : Polynomial (Polynomial ℤ) →+* S :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom S) epsilon) u

noncomputable def regularChart (bits : List Bool) (a : RegularChart bits K) : Fin (TubeParameter.spatialCount bits) → K :=
  Fin.cons 1 a.2

theorem regularCoefficientMap_contDiff (bits : List Bool) (epsilon : K) (p : Polynomial (Polynomial ℤ)) :
    ContDiff K 1 (fun a : RegularChart bits K => regularCoefficientMap epsilon a.1 p) :=
  ParametricPolynomialCalculus.polynomial_eval₂ p
    (fun _ => Polynomial.eval₂RingHom (Int.castRingHom K) epsilon) Prod.fst 1 (fun _ => contDiff_const) contDiff_fst

theorem regularChart_contDiff (bits : List Bool) (i : Fin (TubeParameter.spatialCount bits)) :
    ContDiff K 1 (fun a : RegularChart bits K => regularChart bits a i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact contDiff_const
  · exact (contDiff_apply K K j).comp contDiff_snd

theorem regularChart_nonzero (bits : List Bool) (a : RegularChart bits K) : ∃ j, regularChart bits a j ≠ 0 := by
  refine ⟨⟨0, by unfold TubeParameter.spatialCount; omega⟩, ?_⟩
  exact one_ne_zero

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def regularSystem (epsilon : K) (a : RegularChart (source c) K) : Fin (TubeParameter.spatialCount (source c)) → K :=
  MacaulayRegularPersistence.family (TubeBivariate.rows source active n d ell c)
    (fun z : RegularChart (source c) K => regularCoefficientMap epsilon z.1) (regularChart (source c)) a

theorem exists_regular_shifted_root_curve (epsilon : K) (a : RegularChart (source c) K)
    (hroot : regularSystem source active n d ell c epsilon a = 0)
    (hJac : (fderiv K (regularSystem source active n d ell c epsilon) a).IsInvertible) :
    ∃ curve : K → RegularChart (source c) K, curve 0 = a ∧ ContinuousAt curve 0 ∧
      ∀ᶠ s in 𝓝 (0 : K), ∀ i,
        regularSystem source active n d ell c epsilon (curve s) i =
          s * regularChart (source c) (curve s) i ^ (MacaulayBits.Degrees (TubeCleared.layout source) c i) :=
  MacaulayRegularPersistence.exists_shifted_root_curve (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (fun z : RegularChart (source c) K => regularCoefficientMap epsilon z.1)
    (regularChart (source c)) (regularCoefficientMap_contDiff (source c) epsilon) (regularChart_contDiff (source c)) a hroot hJac

private theorem regular_persistence_width_bound :
    Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c) < 2 ^ TubeCleared.matrixWidth (source c) := by
  have hw := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hw
  exact hw

theorem polynomial_trailingCoeff_eval_eq_zero_of_regular_root (epsilon : K) (a : RegularChart (source c) K)
    (hroot : regularSystem source active n d ell c epsilon a = 0)
    (hJac : (fderiv K (regularSystem source active n d ell c epsilon) a).IsInvertible) :
    regularCoefficientMap epsilon a.1 (polynomial source active n d ell c).trailingCoeff = 0 := by
  have hW := regular_persistence_width_bound source c
  have hd : ∀ i : Fin (TubeParameter.spatialCount (source c)),
      0 < MacaulayBits.Degrees (TubeCleared.layout source) c i := fun i => TubeCleared.degree_pos source c i.val
  have hdegree := MacaulayUniversal.degree_lt_width _ _ hd hW
  exact MacaulayRegularPersistence.trailingCoeff_eq_zero_of_regular_root
    (TubeBivariate.rows source active n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (TubeCleared.matrixWidth (source c)) hdegree hW (TubeBivariate.rows_homogeneous source active n d ell c) hd
    (fun z : RegularChart (source c) K => regularCoefficientMap epsilon z.1) (regularChart (source c))
    (regularCoefficientMap_contDiff (source c) epsilon) (regularChart_contDiff (source c))
    (regularChart_nonzero (source c)) a hroot hJac

noncomputable def lowestProjectionPolynomial {S : Type*} [CommRing S] (epsilon : S) : Polynomial S :=
  (polynomial source active n d ell c).trailingCoeff.map (Polynomial.eval₂RingHom (Int.castRingHom S) epsilon)

theorem lowestProjectionPolynomial_eval_eq_zero_of_regular_root (epsilon : K) (a : RegularChart (source c) K)
    (hroot : regularSystem source active n d ell c epsilon a = 0)
    (hJac : (fderiv K (regularSystem source active n d ell c epsilon) a).IsInvertible) :
    Polynomial.eval a.1 (lowestProjectionPolynomial source active n d ell c epsilon) = 0 := by
  have he := polynomial_trailingCoeff_eval_eq_zero_of_regular_root source active n d ell c epsilon a hroot hJac
  simpa only [lowestProjectionPolynomial, Polynomial.eval_map, regularCoefficientMap, Polynomial.coe_eval₂RingHom] using he

end LeanCanny.ETR.TubeCharacteristicQuotient
