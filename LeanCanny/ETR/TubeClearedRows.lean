/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeClearedCoefficientSpace
public import LeanCanny.ETR.TubeParameterReaders

/-! # Context-independent row data and uniform coefficient degrees

Raw input fields specify the actual cleared row without retaining a query
parser. Scalar coefficient identities can therefore normalize extended matrix
packets without rewriting variable types inside multivariate polynomials.
Uniform parameter bounds give one degree allowance for every spatial monomial.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCleared
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open Algebra.RationalSubstitution
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def rawRow (bits active index : List Bool) (n d : ℕ → Polynomial ℤ) :
    MvPolynomial (TubeParameter.Spatial bits) (Polynomial ℤ) :=
  spatial bits (activeSet (TubeIndexed.arity bits) active)
    (TubeRegularBits.decodedIndex (fun _ => bits) (fun _ => index) []) n d

theorem row_eq_raw (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    row source active index n d c = rawRow (source c) (active c) (index c) (n c) (d c) := rfl

noncomputable def rawCoefficient (bits active index : List Bool) (n d : ℕ → Polynomial ℤ) (W r : ℕ) : Polynomial ℤ :=
  (rawRow bits active index n d).coeff (FixedWidthPolynomial.nativeExponent (TubeParameter.spatialEquiv bits) W r)

attribute [local irreducible] rawCoefficient

theorem wide_packet_raw (source active index degree modulus : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) (r : ℕ) :
    wideValue source active index degree modulus n d (pair c (BinaryNatCode.encode r)) =
      IntegerBits.coefficientResidue
        ((rawCoefficient (source c) (active c) (index c) (n c) (d c) (matrixWidth (source c)) r).coeff (Nat.fromBitsLE (degree c)))
        (Nat.fromBitsLE (modulus c) + 1) := by
  unfold rawCoefficient
  rw [← row_eq_raw source active index n d c]
  exact wide_packet source active index degree modulus n d c r

theorem raw_coefficient_rename (bits active index : List Bool) (n d : ℕ → Polynomial ℤ) (W r : ℕ) :
    (MvPolynomial.rename (TubeParameter.spatialEquiv bits) (rawRow bits active index n d)).coeff
      (Indexed.exponentVector (TubeParameter.spatialCount bits) (FixedWidthPolynomial.entry W r)) =
        rawCoefficient bits active index n d W r := by
  rw [FixedWidthPolynomial.coeff_rename_rank]
  unfold rawCoefficient
  rfl

noncomputable def uniformDegree (source : List Bool → List Bool) (degree : List Bool → List Bool) (c : List Bool) : List Bool :=
  TubeParameter.degreeCode source (degree ∘ TubeParameter.coordinateContext id) (pair c [])

theorem uniformDegree_mem_FP {source degree : List Bool → List Bool} (hs : source ∈ FP) (he : degree ∈ FP) :
    uniformDegree source degree ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair id_mem_FP (constFn_mem_FP []))
    (TubeParameter.degreeCode_mem_FP hs (mem_FP_comp (TubeParameter.coordinateContext_mem_FP id_mem_FP) he))
  exact mem_FP_of_eq (g := uniformDegree source degree) h (fun _ => by simp only [uniformDegree, Function.comp_apply, id_eq])

theorem degree_packet (source degree : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    TubeParameter.degreeCode source (degree ∘ TubeParameter.coordinateContext id) (pair c (BinaryNatCode.encode r)) =
      uniformDegree source degree c := by
  simp only [uniformDegree, TubeParameter.degreeCode, TubeParameter.arityCode, TubeParameter.widthCode,
    TubeParameter.coordinateContext, Function.comp_apply, pairFst_pair, id_eq]

theorem coefficientAt_degree (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (r : ℕ) :
    (coefficientAt source active index n d c r).natDegree ≤ Nat.fromBitsLE (uniformDegree source B.degree c) := by
  have h := TubeParameter.polynomial_degree source active index _ _ (B.precomposeUniform id id_mem_FP)
    (pair c (BinaryNatCode.encode r))
  change ((TubeParameter.family source active index (fun q => n (pairFst q)) (fun q => d (pairFst q))).polynomial
    (pair c (BinaryNatCode.encode r))).natDegree ≤
    Nat.fromBitsLE (TubeParameter.degreeCode source (B.degree ∘ TubeParameter.coordinateContext id)
      (pair c (BinaryNatCode.encode r))) at h
  rw [family_packet source active index n d c r] at h
  rw [degree_packet] at h
  exact h

theorem row_coefficient_degree (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (e : TubeParameter.Spatial (source c) →₀ ℕ) :
    ((row source active index n d c).coeff e).natDegree ≤ Nat.fromBitsLE (uniformDegree source B.degree c) := by
  by_cases he : e ∈ (row source active index n d c).support
  · have hb : ∀ i, e i < 2 ^ TubeIndexed.blockWidth (source c) := fun i =>
      (support_bound (source c) _ _ (n c) (d c) e he i).trans_lt (TubeIndexed.degreeBound_lt (source c))
    obtain ⟨r, hr⟩ := CoefficientWidthBits.exists_native_rank _ _ (TubeParameter.spatialEquiv (source c)) e hb
    have h := coefficientAt_degree source active index n d B c r
    unfold coefficientAt at h
    rw [hr] at h
    exact h
  · rw [MvPolynomial.notMem_support_iff.mp he, Polynomial.natDegree_zero]
    exact Nat.zero_le _

theorem renamed_coefficient_degree (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (e : Fin (TubeParameter.spatialCount (source c)) →₀ ℕ) :
    ((MvPolynomial.rename (TubeParameter.spatialEquiv (source c)) (row source active index n d c)).coeff e).natDegree ≤
      Nat.fromBitsLE (uniformDegree source B.degree c) := by
  let f := TubeParameter.spatialEquiv (source c)
  have he : (e.mapDomain f.symm).mapDomain f = e := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply]
  rw [← he, MvPolynomial.coeff_rename_mapDomain f f.injective]
  exact row_coefficient_degree source active index n d B c _

end LeanCanny.ETR.TubeCleared
