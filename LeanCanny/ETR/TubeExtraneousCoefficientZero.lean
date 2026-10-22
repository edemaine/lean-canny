/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeExtraneousCoefficientPolynomial
public import LeanCanny.ETR.TubeExtraneousSign
public import LeanCanny.ETR.TubeBivariateReindex
public import LeanCanny.ETR.TubeDeformationCoefficientZero
public import LeanCanny.Computation.SpaceDeciderFunction

/-! # Whole extraneous deformation coefficient identity tests in polynomial space

Each input is `pair context deformationDegree`. A bounded scan tests every
scalar coefficient of its degree-bounded encoding. Scalar queries decode the
original two exponents and run the complete integer zero evaluator. The saved
scan state and every original coefficient-reader cost are included.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeExtraneous
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] determinant scalarCoefficient coefficient
attribute [local irreducible] TubeIndexed.degreeBound TubeParameter.spatialCount TubeCleared.matrixWidth TubeDeformation.coefficientCount

noncomputable def encodedScalar (source active degree : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (q : List Bool) : ℤ :=
  ((encodedDeterminant source active degree n d ell (TubeDeformation.CoefficientQuery.base q)).coeff
    (Nat.fromBitsLE (TubeDeformation.CoefficientQuery.outer q))).coeff (Nat.fromBitsLE (TubeDeformation.CoefficientQuery.rank q))

theorem leaf_coefficient (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (q : List Bool) :
    coefficient (source ∘ TubeDeformation.CoefficientQuery.base) (active ∘ TubeDeformation.CoefficientQuery.base)
      (TubeDeformation.CoefficientQuery.inner source B.degree) (TubeDeformation.CoefficientQuery.middle source B.degree) TubeDeformation.CoefficientQuery.outer
      (fun c => n (TubeDeformation.CoefficientQuery.base c)) (fun c => d (TubeDeformation.CoefficientQuery.base c)) (fun c => ell (TubeDeformation.CoefficientQuery.base c)) q =
        encodedScalar source active B.degree n d ell q := by
  rw [coefficient_reindex, TubeDeformation.CoefficientQuery.inner_value, TubeDeformation.CoefficientQuery.middle_value]
  exact (encoded_coefficient_any source active n d ell B _ _ _).symm

def scalarZeroLanguage (source active degree : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {q | encodedScalar source active degree n d ell q = 0}

theorem scalarZeroDecider {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceDecider (scalarZeroLanguage source active D.bounds.degree n d ell) := by
  let DL := (D.reindex TubeDeformation.CoefficientQuery.base TubeDeformation.CoefficientQuery.base_mem_FP).reselect
    (TubeDeformation.CoefficientQuery.inner source D.bounds.degree) (TubeDeformation.CoefficientQuery.middle source D.bounds.degree)
    (TubeDeformation.CoefficientQuery.inner_mem_FP D.sourceFP D.bounds.degreeFP) (TubeDeformation.CoefficientQuery.middle_mem_FP D.sourceFP D.bounds.degreeFP)
  have E := integerZeroDecider DL TubeDeformation.CoefficientQuery.outer TubeDeformation.CoefficientQuery.outer_mem_FP
  refine E.congr ?_
  ext q
  change coefficient (source ∘ TubeDeformation.CoefficientQuery.base) (active ∘ TubeDeformation.CoefficientQuery.base)
    (TubeDeformation.CoefficientQuery.inner source D.bounds.degree) (TubeDeformation.CoefficientQuery.middle source D.bounds.degree) TubeDeformation.CoefficientQuery.outer
    (fun c => n (TubeDeformation.CoefficientQuery.base c)) (fun c => d (TubeDeformation.CoefficientQuery.base c)) (fun c => ell (TubeDeformation.CoefficientQuery.base c)) q = 0 ↔ _
  rw [leaf_coefficient source active n d ell D.bounds q]
  rfl

def coefficientZeroLanguage (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {q | (determinant source active n d ell (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q)) = 0}

theorem coefficientZeroLanguage_eq_scan (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) :
    coefficientZeroLanguage source active n d ell =
      BoundedScan.language (scalarZeroLanguage source active B.degree n d ell)
        (fun q => Nat.fromBitsLE (TubeDeformation.coefficientCount source B.degree (pairFst q))) := by
  ext q
  change (determinant source active n d ell (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q)) = 0 ↔ _
  rw [← encoded_coefficient_zero_iff source active n d ell B (pairFst q) (Nat.fromBitsLE (pairSnd q))]
  change _ ↔ ∀ i < Nat.fromBitsLE (TubeDeformation.coefficientCount source B.degree (pairFst q)),
    encodedScalar source active B.degree n d ell (pair q (BinaryNatCode.encode i)) = 0
  simp only [encodedScalar, TubeDeformation.CoefficientQuery.base, TubeDeformation.CoefficientQuery.outer, TubeDeformation.CoefficientQuery.rank,
    pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
  constructor
  · intro hz i _
    rw [hz, Polynomial.coeff_zero]
  · intro h
    ext i
    by_cases hi : i < Nat.fromBitsLE (TubeDeformation.coefficientCount source B.degree (pairFst q))
    · simpa only [Polynomial.coeff_zero] using h i hi
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le
        (encoded_coefficient_degree source active n d ell B (pairFst q) (Nat.fromBitsLE (pairSnd q))) (Nat.le_of_not_gt hi)),
        Polynomial.coeff_zero]

theorem coefficientZeroDecider {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceDecider (coefficientZeroLanguage source active n d ell) := by
  let bound := fun q => BinaryNat.normalize (TubeDeformation.coefficientCount source D.bounds.degree (pairFst q))
  have hb0 := mem_FP_comp (mem_FP_comp pairFst_mem_FP (TubeDeformation.coefficientCount_mem_FP D.sourceFP D.bounds.degreeFP)) BinaryNat.normalize_mem_FP
  have hb : bound ∈ FP := mem_FP_of_eq hb0 (fun _ => rfl)
  have E := BoundedScan.decider (scalarZeroDecider D) bound hb
    (fun q => Nat.fromBitsLE (TubeDeformation.coefficientCount source D.bounds.degree (pairFst q)))
    (fun q => BinaryNat.normalize_eq_bits (TubeDeformation.coefficientCount source D.bounds.degree (pairFst q)))
  exact E.congr (coefficientZeroLanguage_eq_scan source active n d ell D.bounds).symm

theorem coefficientZeroLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) : coefficientZeroLanguage source active n d ell ∈ PSPACE :=
  (coefficientZeroDecider D).mem_PSPACE

end LeanCanny.ETR.TubeExtraneous
