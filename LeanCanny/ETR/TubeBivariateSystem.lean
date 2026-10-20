/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeClearedRows
public import LeanCanny.ETR.TubeLinearCoefficientSpace
public import LeanCanny.Algebra.MacaulayBivariateSpace

/-! # The full cleared regular tube system with an independent projection variable

Regular spatial coefficients are polynomials in the inner perturbation variable.
The added projection equation uses the outer variable. Every reciprocal and
original regular row is retained. Uniform coordinate bounds supply the bivariate
backend's entry-degree contract after reduction modulo any positive modulus.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeBivariate
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def rows (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (i : Fin (TubeParameter.spatialCount (source c))) :
    MvPolynomial (Fin (TubeParameter.spatialCount (source c))) (Polynomial (Polynomial ℤ)) :=
  if i.val = 0 then (TubeLinear.polynomial source ell c).map (Polynomial.mapRingHom Polynomial.C)
  else (MvPolynomial.rename (TubeParameter.spatialEquiv (source c))
    (TubeCleared.row source active (fun _ => BinaryNatCode.encode (i.val - 1)) n d c)).map Polynomial.C

theorem rows_homogeneous (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (i : Fin (TubeParameter.spatialCount (source c))) :
    (rows source active n d ell c i).IsHomogeneous ((TubeCleared.layout source).degree c i.val) := by
  change (rows source active n d ell c i).IsHomogeneous (if i.val = 0 then 1 else TubeIndexed.degreeBound (source c))
  rw [rows]
  split_ifs
  · exact (TubeLinear.homogeneous source ell c).map _
  · apply MvPolynomial.IsHomogeneous.map
    apply MvPolynomial.IsHomogeneous.rename_isHomogeneous
    exact TubeCleared.homogeneous (source c) _ _ (n c) (d c)

theorem rows_inner_bound (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (c : List Bool) (i : Fin (TubeParameter.spatialCount (source c)))
    (e : Fin (TubeParameter.spatialCount (source c)) →₀ ℕ) (j : ℕ) :
    (((rows source active n d ell c i).coeff e).coeff j).natDegree ≤
      Nat.fromBitsLE (TubeCleared.uniformDegree source B.degree c) := by
  rw [rows]
  split_ifs
  · rw [MvPolynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    rw [Polynomial.natDegree_C]
    exact Nat.zero_le _
  · rw [MvPolynomial.coeff_map]
    change ((Polynomial.C ((MvPolynomial.rename (TubeParameter.spatialEquiv (source c))
      (TubeCleared.row source active (fun _ => BinaryNatCode.encode (i.val - 1)) n d c)).coeff e)).coeff j).natDegree ≤ _
    by_cases hj : j = 0
    · subst j
      rw [Polynomial.coeff_C_zero]
      exact TubeCleared.renamed_coefficient_degree source active _ n d B c e
    · simp [Polynomial.coeff_C, hj]

noncomputable def reduction (m : ℕ) : Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial (ZMod m)) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom (ZMod m)))

noncomputable def family (source active modulus inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) : MacaulayBivariate.Family where
  layout := TubeCleared.layout source
  modulus c := Nat.fromBitsLE (modulus c) + 1
  inner c := Nat.fromBitsLE (inner c)
  outer c := Nat.fromBitsLE (outer c)
  bound c := Nat.fromBitsLE (TubeCleared.uniformDegree source B.degree c)
  polynomial c i := (rows source active n d ell c i).map (reduction (Nat.fromBitsLE (modulus c) + 1))
  modulus_ne_zero _ := by omega
  inner_bound c i e j := by
    change Fin (TubeParameter.spatialCount (source c)) at i
    change (Fin (TubeParameter.spatialCount (source c)) →₀ ℕ) at e
    change ((((rows source active n d ell c i).map (reduction (Nat.fromBitsLE (modulus c) + 1))).coeff e).coeff j).natDegree ≤ _
    rw [MvPolynomial.coeff_map]
    change (((((rows source active n d ell c i).coeff e).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1))))).coeff j).natDegree) ≤ _
    rw [Polynomial.coeff_map]
    exact Polynomial.natDegree_map_le.trans (rows_inner_bound source active n d ell B c i e j)

end LeanCanny.ETR.TubeBivariate
