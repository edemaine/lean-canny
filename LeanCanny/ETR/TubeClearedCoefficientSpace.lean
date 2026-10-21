/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayLayout

/-! # Cleared regular-row coefficients at the Macaulay exponent width

The matrix width covers the full Macaulay level. A bounded exponent guard
prevents truncation from aliasing an unsupported matrix monomial to a supported
source monomial. The parameter coordinates are uniform across spatial ranks.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCleared
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm coefficientAt

def narrowInput (degree modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (pair (pairFst q) (BinaryNat.normalize (pairSnd q))) (degree (pairFst q)))
    (BinaryNat.normalize (modulus (pairFst q)))

theorem narrowInput_mem_FP {degree modulus : List Bool → List Bool} (hk : degree ∈ FP) (hm : modulus ∈ FP) :
    narrowInput degree modulus ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP))
    (mem_FP_comp pairFst_mem_FP hk)) (mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.normalize_mem_FP)

noncomputable def narrowValue (source active index degree modulus : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) : List Bool → List Bool :=
  (TubeParameter.family source active index (fun c => n (pairFst c)) (fun c => d (pairFst c))).value ∘ narrowInput degree modulus

theorem narrowEvaluator (source active index degree modulus : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ)
    (C : TubeParameter.CoordinateReaders source (fun c => n (pairFst c)) (fun c => d (pairFst c)))
    (hs : source ∈ FP) (ha : active ∈ FP) (hi : index ∈ FP) (hk : degree ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (narrowValue source active index degree modulus n d) :=
  (TubeParameter.evaluator source active index _ _ C hs ha hi).precompose _ (narrowInput_mem_FP hk hm)

theorem narrow_packet (source active index degree modulus : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) (r : ℕ) :
    narrowValue source active index degree modulus n d (pair c (BinaryNatCode.encode r)) =
      IntegerBits.coefficientResidue ((coefficientAt source active index n d c r).coeff (Nat.fromBitsLE (degree c)))
        (Nat.fromBitsLE (modulus c) + 1) := by
  have h := IntegerBits.Family.value_packet
    (TubeParameter.family source active index (fun c => n (pairFst c)) (fun c => d (pairFst c)))
    (pair (pair c (BinaryNatCode.encode r)) (degree c)) (Nat.fromBitsLE (modulus c) + 1) (by omega)
  rw [pairFst_pair, pairSnd_pair, family_packet] at h
  change _ = IntegerBits.coefficientResidue _ _ at h
  rw [narrowValue, Function.comp_apply, narrowInput]
  simp only [pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode,
    Nat.add_sub_cancel_right] at h ⊢
  exact h

noncomputable def wideValue (source active index degree modulus : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) : List Bool → List Bool :=
  CoefficientWidthBits.value (TubeParameter.spatialCount ∘ source) (matrixWidth ∘ source)
    (TubeIndexed.blockWidth ∘ source) (TubeIndexed.degreeBound ∘ source)
    (narrowValue source active index degree modulus n d)

theorem wideEvaluator (source active index degree modulus : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ)
    (C : TubeParameter.CoordinateReaders source (fun c => n (pairFst c)) (fun c => d (pairFst c)))
    (hs : source ∈ FP) (ha : active ∈ FP) (hi : index ∈ FP) (hk : degree ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (wideValue source active index degree modulus n d) :=
  CoefficientWidthBits.evaluator (TubeParameter.spatialCount_unary.comp hs) (matrixWidth_unary.comp hs)
    (TubeIndexed.blockWidth_unary.comp hs) (TubeIndexed.degreeBound_unary.comp hs)
    (narrowEvaluator source active index degree modulus n d C hs ha hi hk hm)

theorem wide_packet (source active index degree modulus : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) (r : ℕ) :
    wideValue source active index degree modulus n d (pair c (BinaryNatCode.encode r)) =
      IntegerBits.coefficientResidue
        (((row source active index n d c).coeff (FixedWidthPolynomial.nativeExponent
          (TubeParameter.spatialEquiv (source c)) (matrixWidth (source c)) r)).coeff (Nat.fromBitsLE (degree c)))
        (Nat.fromBitsLE (modulus c) + 1) := by
  have h := CoefficientWidthBits.value_packet
    (TubeParameter.spatialCount ∘ source) (matrixWidth ∘ source)
    (TubeIndexed.blockWidth ∘ source) (TubeIndexed.degreeBound ∘ source)
    (narrowValue source active index degree modulus n d) c (TubeParameter.spatialEquiv (source c))
    (row source active index n d c)
    (fun p => IntegerBits.coefficientResidue (p.coeff (Nat.fromBitsLE (degree c))) (Nat.fromBitsLE (modulus c) + 1))
    (by simp [IntegerBits.coefficientResidue, residueBits, BinaryNatCode.encode])
    (TubeIndexed.degreeBound_lt (source c))
    (support_bound (source c) _ _ (n c) (d c))
    (by
      intro k
      simpa only [coefficientAt, Function.comp_apply] using narrow_packet source active index degree modulus n d c k) r
  exact h

theorem wide_packet_rename (source active index degree modulus : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) (r : ℕ) :
    wideValue source active index degree modulus n d (pair c (BinaryNatCode.encode r)) =
      IntegerBits.coefficientResidue
        (((MvPolynomial.rename (TubeParameter.spatialEquiv (source c)) (row source active index n d c)).coeff
          (Indexed.exponentVector (TubeParameter.spatialCount (source c))
            (FixedWidthPolynomial.entry (matrixWidth (source c)) r))).coeff (Nat.fromBitsLE (degree c)))
        (Nat.fromBitsLE (modulus c) + 1) := by
  rw [FixedWidthPolynomial.coeff_rename_rank]
  exact wide_packet source active index degree modulus n d c r

end LeanCanny.ETR.TubeCleared
