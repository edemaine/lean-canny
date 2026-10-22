/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCompiledAffineRoots
public import LeanCanny.Geometry.FiniteProjectionRoots

/-! # Lifting regular geometric critical points into the compiled affine system

The spatial coordinates retain the reciprocal coordinate and the original
point. The added affine coordinate is the prescribed linear projection of
that spatial tuple. Denominator clearing preserves every spatial zero.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCompiledAffineRoots
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical BigOperators
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
variable {K : Type*} [Field K]

noncomputable def spatialPoint (bits : List Bool) (x : Option (TubeSource.Coordinate bits) → K) :
    Fin (pointCount (TubeIndexed.arity bits) + 1) → K :=
  fun i => x ((TubeMacaulay.coordinateEquiv (TubeIndexed.arity bits)).symm i)

noncomputable def compiledPoint (bits : List Bool) (ell : ℕ → ℤ)
    (x : Option (TubeSource.Coordinate bits) → K) : Fin (TubeParameter.spatialCount bits) → K :=
  Fin.cons (∑ i, (Int.castRingHom K) (ell (i.val + 1)) * spatialPoint bits x i) (spatialPoint bits x)

theorem decodedPoint_compiledPoint (bits : List Bool) (ell : ℕ → ℤ)
    (x : Option (TubeSource.Coordinate bits) → K) :
    decodedPoint bits (compiledPoint bits ell x) = x := by
  funext i
  change x ((TubeMacaulay.coordinateEquiv (TubeIndexed.arity bits)).symm
    ((TubeMacaulay.coordinateEquiv (TubeIndexed.arity bits)) i)) = x i
  exact congrArg x ((TubeMacaulay.coordinateEquiv (TubeIndexed.arity bits)).symm_apply_apply i)

theorem eval_spatial_row (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon u : K)
    (y : Fin (pointCount (TubeIndexed.arity (source c)) + 1) → K)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) → (d c i).eval₂ (Int.castRingHom K) epsilon ≠ 0)
    (i : Fin (TubeParameter.spatialCount (source c))) (hi : i.val ≠ 0) :
    MvPolynomial.eval₂ (TubeCharacteristicQuotient.regularCoefficientMap epsilon u)
      (Fin.cons (1 : K) y : Fin (TubeParameter.spatialCount (source c)) → K)
      (TubeBivariate.rows source active n d ell c i) =
      TubeCleared.scale (source c) (d c) (Int.castRingHom K) epsilon *
        (TubeParameter.spatialPolynomial source active (fun _ => BinaryNatCode.encode (i.val - 1)) c).eval₂
          (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon)
          (fun j => (Fin.cons (1 : K) y : Fin (TubeParameter.spatialCount (source c)) → K)
            (TubeParameter.spatialEquiv (source c) j)) := by
  have hr := TubeCleared.row_map_eq source active (fun _ => BinaryNatCode.encode (i.val - 1))
    n d (Int.castRingHom K) epsilon c hd
  have h := congrArg (MvPolynomial.eval (fun j =>
    (Fin.cons (1 : K) y : Fin (TubeParameter.spatialCount (source c)) → K)
      (TubeParameter.spatialEquiv (source c) j))) hr
  rw [MvPolynomial.eval_map, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_map] at h
  rw [TubeBivariate.rows, ite_eq_right hi]
  refine (MvPolynomial.eval₂_map Polynomial.C _ _ _).trans ?_
  have hc : (TubeCharacteristicQuotient.regularCoefficientMap epsilon u).comp Polynomial.C =
      Polynomial.eval₂RingHom (Int.castRingHom K) epsilon := Polynomial.eval₂RingHom_comp_C _ _
  rw [hc]
  exact (MvPolynomial.eval₂_rename _ _ _ _).trans h

theorem compiled_root_of_spatial (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon : K)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) → (d c i).eval₂ (Int.castRingHom K) epsilon ≠ 0)
    (x : Option (TubeSource.Coordinate (source c)) → K)
    (hx : ∀ j, (TubeRegularMacaulay.spatial (source c)
      (activeSet (TubeIndexed.arity (source c)) (active c)) j).eval₂
        (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon)
        (fun j => j.elim 1 x) = 0) :
    ∀ i, MvPolynomial.eval (compiledPoint (source c) (ell c) x)
      (TubeCharacteristicQuotient.finiteSystem source active n d ell c epsilon i) = 0 := by
  intro i
  rw [TubeCharacteristicQuotient.eval_finiteSystem]
  simp_rw [TubeCharacteristicQuotient.eval_finiteChartVariables]
  let y := spatialPoint (source c) x
  let u := ∑ j, (Int.castRingHom K) (ell c (j.val + 1)) * y j
  change MvPolynomial.eval₂ (TubeCharacteristicQuotient.regularCoefficientMap epsilon u)
    (Fin.cons (1 : K) y : Fin (TubeParameter.spatialCount (source c)) → K)
    (TubeBivariate.rows source active n d ell c i) = 0
  by_cases hi : i.val = 0
  · have he : i = TubeCharacteristicQuotient.finiteParameterIndex (source c) := Fin.ext hi
    subst i
    rw [eval_projection_row]
    change u - u = 0
    exact sub_self _
  · rw [eval_spatial_row source active n d ell c epsilon _ _ hd i hi]
    have hchart := decoded_chart (source c) (compiledPoint (source c) (ell c) x)
    rw [decodedPoint_compiledPoint] at hchart
    have he := congrArg (fun point : TubeParameter.Spatial (source c) → K =>
      (TubeParameter.spatialPolynomial source active (fun _ => BinaryNatCode.encode (i.val - 1)) c).eval₂
        (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon) point) hchart
    exact (congrArg (fun v => TubeCleared.scale (source c) (d c) (Int.castRingHom K) epsilon * v)
      (he.trans (hx _))).trans (mul_zero _)

theorem compiled_root_iff_spatial (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon : K)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) → (d c i).eval₂ (Int.castRingHom K) epsilon ≠ 0)
    (x : Option (TubeSource.Coordinate (source c)) → K) :
    (∀ i, MvPolynomial.eval (compiledPoint (source c) (ell c) x)
      (TubeCharacteristicQuotient.finiteSystem source active n d ell c epsilon i) = 0) ↔
      ∀ j, (TubeRegularMacaulay.spatial (source c)
        (activeSet (TubeIndexed.arity (source c)) (active c)) j).eval₂
          (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon)
          (fun j => j.elim 1 x) = 0 := by
  constructor
  · intro h
    simpa only [decodedPoint_compiledPoint] using
      spatial_roots_of_compiled source active n d ell c epsilon hd _ h
  · exact compiled_root_of_spatial source active n d ell c epsilon hd x

end LeanCanny.ETR.TubeCompiledAffineRoots
