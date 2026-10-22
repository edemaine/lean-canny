/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeParameterDecisions
public import LeanCanny.Algebra.CoefficientAddMap
public import LeanCanny.Algebra.CoefficientWidthSpace

/-! # Uniform denominator clearing of the regular homogeneous spatial rows

Parameter coordinates depend on the original input context. One fixed additive
map clears every spatial coefficient, so a row has a common denominator scale.
The resulting polynomials remain homogeneous and have the actual streamed
spatial coefficients proved by parameter specialization.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCleared
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open Algebra.RationalSubstitution
open scoped BigOperators Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def coefficientMap (bits : List Bool) (n d : ℕ → Polynomial ℤ) :
    TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+ Polynomial ℤ :=
  (Indexed.clearHom (fun _ => 2 ^ (TubeIndexed.blockWidth bits - 1))
    (fun i : Fin (TubeParameter.parameterCount bits) => n i.val)
    (fun i : Fin (TubeParameter.parameterCount bits) => d i.val)).comp
      (MvPolynomial.rename (TubeParameter.parameterEquiv bits)).toAddMonoidHom

noncomputable def spatial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : TubeRegularSource.Index bits) (n d : ℕ → Polynomial ℤ) :
    MvPolynomial (TubeParameter.Spatial bits) (Polynomial ℤ) :=
  CoefficientAddMap.apply (coefficientMap bits n d) (TubeRegularMacaulay.spatial bits s j)

theorem homogeneous (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : TubeRegularSource.Index bits) (n d : ℕ → Polynomial ℤ) :
    (spatial bits s j n d).IsHomogeneous (TubeIndexed.degreeBound bits) :=
  CoefficientAddMap.homogeneous _ _ _ (TubeRegularMacaulay.spatial_homogeneous bits s j)

theorem support_bound (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : TubeRegularSource.Index bits)
    (n d : ℕ → Polynomial ℤ) (e : TubeParameter.Spatial bits →₀ ℕ) (he : e ∈ (spatial bits s j n d).support)
    (i : TubeParameter.Spatial bits) : e i ≤ TubeIndexed.degreeBound bits :=
  (Finsupp.le_degree i e).trans ((MvPolynomial.le_totalDegree he).trans (homogeneous bits s j n d).totalDegree_le)

noncomputable def row (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    MvPolynomial (TubeParameter.Spatial (source c)) (Polynomial ℤ) :=
  spatial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
    (TubeRegularBits.decodedIndex source index c) (n c) (d c)

noncomputable def coefficientAt (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (c : List Bool) (r : ℕ) : Polynomial ℤ :=
  (row source active index n d c).coeff (FixedWidthPolynomial.nativeExponent (TubeParameter.spatialEquiv (source c))
    (TubeIndexed.blockWidth (source c)) r)

theorem family_eq (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (q : List Bool) :
    (TubeParameter.family source active index (fun c => n (pairFst c)) (fun c => d (pairFst c))).polynomial q =
      coefficientAt source active index n d (pairFst q) (Nat.fromBitsLE (pairSnd q)) := by
  rw [TubeParameter.polynomial_eq]
  rfl

attribute [local irreducible] coefficientAt

theorem family_packet (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (c : List Bool) (r : ℕ) :
    (TubeParameter.family source active index (fun c => n (pairFst c)) (fun c => d (pairFst c))).polynomial
      (pair c (BinaryNatCode.encode r)) = coefficientAt source active index n d c r := by
  rw [family_eq, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]


noncomputable def scale {K : Type*} [CommRing K] (bits : List Bool) (d : ℕ → Polynomial ℤ) (φ : ℤ →+* K) (x : K) : K :=
  ∏ i ∈ Finset.range (TubeParameter.parameterCount bits), (d i).eval₂ φ x ^ (2 ^ TubeIndexed.blockWidth bits)

noncomputable def parameterMap {K : Type*} [Field K] (bits : List Bool) (n d : ℕ → Polynomial ℤ) (φ : ℤ →+* K) (x : K) :
    TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K :=
  MvPolynomial.eval₂Hom φ (fun i => (n (TubeParameter.parameterEquiv bits i).val).eval₂ φ x /
    (d (TubeParameter.parameterEquiv bits i).val).eval₂ φ x)

noncomputable def specializedCoefficient {K : Type*} [Field K] (source active index : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (φ : ℤ →+* K) (x : K) (c : List Bool) (r : ℕ) : K :=
  ((TubeParameter.spatialPolynomial source active index c).map (parameterMap (source c) (n c) (d c) φ x)).coeff
    (FixedWidthPolynomial.nativeExponent (TubeParameter.spatialEquiv (source c)) (TubeIndexed.blockWidth (source c)) r)

theorem eval_family_coefficient {K : Type*} [Field K] (source active index : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (φ : ℤ →+* K) (x : K) (q : List Bool)
    (hd : ∀ i, i < TubeParameter.parameterCount (source (pairFst q)) → (d (pairFst q) i).eval₂ φ x ≠ 0) :
    ((TubeParameter.family source active index (fun c => n (pairFst c)) (fun c => d (pairFst c))).polynomial q).eval₂ φ x =
      scale (source (pairFst q)) (d (pairFst q)) φ x *
        specializedCoefficient source active index n d φ x (pairFst q) (Nat.fromBitsLE (pairSnd q)) :=
  TubeParameter.eval_coefficient φ x source active index (fun c => n (pairFst c)) (fun c => d (pairFst c)) q hd

attribute [local irreducible] scale specializedCoefficient

theorem eval_coefficient_packet {K : Type*} [Field K] (source active index : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (φ : ℤ →+* K) (x : K) (c : List Bool) (r : ℕ)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) → (d c i).eval₂ φ x ≠ 0) :
    (coefficientAt source active index n d c r).eval₂ φ x = scale (source c) (d c) φ x *
      specializedCoefficient source active index n d φ x c r := by
  have h := eval_family_coefficient source active index n d φ x (pair c (BinaryNatCode.encode r)) (by
    simpa only [pairFst_pair] using hd)
  rw [family_packet, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode] at h
  exact h

theorem row_map_eq {K : Type*} [Field K] (source active index : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (φ : ℤ →+* K) (x : K) (c : List Bool)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) → (d c i).eval₂ φ x ≠ 0) :
    (row source active index n d c).map (Polynomial.eval₂RingHom φ x) =
      scale (source c) (d c) φ x •
        (TubeParameter.spatialPolynomial source active index c).map (parameterMap (source c) (n c) (d c) φ x) := by
  apply CoefficientAddMap.map_eq_smul
  intro m hm
  have hb (i : TubeParameter.Spatial (source c)) : m i < 2 ^ TubeIndexed.blockWidth (source c) :=
    ((Finsupp.le_degree i m).trans ((MvPolynomial.le_totalDegree hm).trans
      (TubeRegularMacaulay.spatial_homogeneous (source c) _ _).totalDegree_le)).trans_lt (TubeIndexed.degreeBound_lt (source c))
  obtain ⟨r, hr⟩ := CoefficientWidthBits.exists_native_rank _ _ (TubeParameter.spatialEquiv (source c)) m hb
  have h := eval_coefficient_packet source active index n d φ x c r hd
  unfold coefficientAt specializedCoefficient at h
  rw [hr, MvPolynomial.coeff_map] at h
  exact h

end LeanCanny.ETR.TubeCleared
