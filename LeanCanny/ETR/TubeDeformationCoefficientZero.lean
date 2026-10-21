/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationCoefficientPolynomial
public import LeanCanny.ETR.TubeDeformationSign
public import LeanCanny.ETR.TubeBivariateReindex
public import LeanCanny.Computation.SpaceDeciderFunction

/-! # Whole deformation coefficient identity tests in polynomial space

Each input is `pair context deformationDegree`. A bounded scan tests every
scalar coefficient of its degree-bounded encoding. Scalar queries decode the
original two exponents and run the complete integer zero evaluator. The saved
scan state and every original coefficient-reader cost are included.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] determinant scalarCoefficient coefficient
attribute [local irreducible] TubeIndexed.degreeBound TubeParameter.spatialCount TubeCleared.matrixWidth coefficientCount

namespace CoefficientQuery

def base (q : List Bool) : List Bool := pairFst (pairFst q)
def outer (q : List Bool) : List Bool := pairSnd (pairFst q)
def rank (q : List Bool) : List Bool := pairSnd q

theorem base_mem_FP : base ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem outer_mem_FP : outer ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

noncomputable def division (source degree : List Bool → List Bool) (q : List Bool) : List Bool :=
  BinaryNat.divMod (pair (rank q) (radixCode source degree (base q)))

noncomputable def inner (source degree : List Bool → List Bool) : List Bool → List Bool := pairSnd ∘ division source degree
noncomputable def middle (source degree : List Bool → List Bool) : List Bool → List Bool := pairFst ∘ division source degree

theorem division_mem_FP {source degree : List Bool → List Bool} (hs : source ∈ FP) (hd : degree ∈ FP) : division source degree ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair pairSnd_mem_FP (mem_FP_comp base_mem_FP (radixCode_mem_FP hs hd))) BinaryNat.divMod_mem_FP
  exact mem_FP_of_eq (g := division source degree) h (fun _ => by simp only [division, rank, Function.comp_apply])

theorem inner_mem_FP {source degree : List Bool → List Bool} (hs : source ∈ FP) (hd : degree ∈ FP) : inner source degree ∈ FP :=
  mem_FP_comp (division_mem_FP hs hd) pairSnd_mem_FP

theorem middle_mem_FP {source degree : List Bool → List Bool} (hs : source ∈ FP) (hd : degree ∈ FP) : middle source degree ∈ FP :=
  mem_FP_comp (division_mem_FP hs hd) pairFst_mem_FP

theorem inner_value (source degree : List Bool → List Bool) (q : List Bool) :
    Nat.fromBitsLE (inner source degree q) = Nat.fromBitsLE (rank q) % radix source degree (base q) := by
  simp only [inner, division, Function.comp_apply, BinaryNat.divMod_pair, pairSnd_pair, radixCode_code,
    MacaulayBits.fromBits_encode, Nat.fromBitsLE_bits]

theorem middle_value (source degree : List Bool → List Bool) (q : List Bool) :
    Nat.fromBitsLE (middle source degree q) = Nat.fromBitsLE (rank q) / radix source degree (base q) := by
  simp only [middle, division, Function.comp_apply, BinaryNat.divMod_pair, pairFst_pair, radixCode_code,
    MacaulayBits.fromBits_encode, Nat.fromBitsLE_bits]

end CoefficientQuery

noncomputable def encodedScalar (source active degree : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (q : List Bool) : ℤ :=
  ((encodedDeterminant source active degree n d ell (CoefficientQuery.base q)).coeff
    (Nat.fromBitsLE (CoefficientQuery.outer q))).coeff (Nat.fromBitsLE (CoefficientQuery.rank q))

theorem leaf_coefficient (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (q : List Bool) :
    coefficient (source ∘ CoefficientQuery.base) (active ∘ CoefficientQuery.base)
      (CoefficientQuery.inner source B.degree) (CoefficientQuery.middle source B.degree) CoefficientQuery.outer
      (fun c => n (CoefficientQuery.base c)) (fun c => d (CoefficientQuery.base c)) (fun c => ell (CoefficientQuery.base c)) q =
        encodedScalar source active B.degree n d ell q := by
  rw [coefficient_reindex, CoefficientQuery.inner_value, CoefficientQuery.middle_value]
  exact (encoded_coefficient_any source active n d ell B _ _ _).symm

def scalarZeroLanguage (source active degree : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {q | encodedScalar source active degree n d ell q = 0}

theorem scalarZeroDecider {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceDecider (scalarZeroLanguage source active D.bounds.degree n d ell) := by
  let DL := (D.reindex CoefficientQuery.base CoefficientQuery.base_mem_FP).reselect
    (CoefficientQuery.inner source D.bounds.degree) (CoefficientQuery.middle source D.bounds.degree)
    (CoefficientQuery.inner_mem_FP D.sourceFP D.bounds.degreeFP) (CoefficientQuery.middle_mem_FP D.sourceFP D.bounds.degreeFP)
  have E := integerZeroDecider DL CoefficientQuery.outer CoefficientQuery.outer_mem_FP
  refine E.congr ?_
  ext q
  change coefficient (source ∘ CoefficientQuery.base) (active ∘ CoefficientQuery.base)
    (CoefficientQuery.inner source D.bounds.degree) (CoefficientQuery.middle source D.bounds.degree) CoefficientQuery.outer
    (fun c => n (CoefficientQuery.base c)) (fun c => d (CoefficientQuery.base c)) (fun c => ell (CoefficientQuery.base c)) q = 0 ↔ _
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
        (fun q => Nat.fromBitsLE (coefficientCount source B.degree (pairFst q))) := by
  ext q
  change (determinant source active n d ell (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q)) = 0 ↔ _
  rw [← encoded_coefficient_zero_iff source active n d ell B (pairFst q) (Nat.fromBitsLE (pairSnd q))]
  change _ ↔ ∀ i < Nat.fromBitsLE (coefficientCount source B.degree (pairFst q)),
    encodedScalar source active B.degree n d ell (pair q (BinaryNatCode.encode i)) = 0
  simp only [encodedScalar, CoefficientQuery.base, CoefficientQuery.outer, CoefficientQuery.rank,
    pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
  constructor
  · intro hz i _
    rw [hz, Polynomial.coeff_zero]
  · intro h
    ext i
    by_cases hi : i < Nat.fromBitsLE (coefficientCount source B.degree (pairFst q))
    · simpa only [Polynomial.coeff_zero] using h i hi
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le
        (encoded_coefficient_degree source active n d ell B (pairFst q) (Nat.fromBitsLE (pairSnd q))) (Nat.le_of_not_gt hi)),
        Polynomial.coeff_zero]

theorem coefficientZeroDecider {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceDecider (coefficientZeroLanguage source active n d ell) := by
  let bound := fun q => BinaryNat.normalize (coefficientCount source D.bounds.degree (pairFst q))
  have hb0 := mem_FP_comp (mem_FP_comp pairFst_mem_FP (coefficientCount_mem_FP D.sourceFP D.bounds.degreeFP)) BinaryNat.normalize_mem_FP
  have hb : bound ∈ FP := mem_FP_of_eq hb0 (fun _ => rfl)
  have E := BoundedScan.decider (scalarZeroDecider D) bound hb
    (fun q => Nat.fromBitsLE (coefficientCount source D.bounds.degree (pairFst q)))
    (fun q => BinaryNat.normalize_eq_bits (coefficientCount source D.bounds.degree (pairFst q)))
  exact E.congr (coefficientZeroLanguage_eq_scan source active n d ell D.bounds).symm

theorem coefficientZeroLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) : coefficientZeroLanguage source active n d ell ∈ PSPACE :=
  (coefficientZeroDecider D).mem_PSPACE

end LeanCanny.ETR.TubeDeformation
