/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeParameterSource

/-! # Polynomial-space substitution into a regular spatial coefficient

Only parameter-coordinate readers are supplied by callers. The compiled regular
source, spatial-exponent filter, term counts, and shifted exponent readers all
come with their own certificates. Source ranks and clearing widths stay binary.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeParameter
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm coefficientValue coefficient

noncomputable def family (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) : IntegerBits.Family where
  arity c := parameterCount (source (pairFst c))
  width c := 2 ^ TubeIndexed.blockWidth (source (pairFst c))
  terms c := FixedWidthPolynomial.count (nativeCount (source (pairFst c))) (TubeIndexed.blockWidth (source (pairFst c)))
  exponent c r i := FixedWidthPolynomial.entry (TubeIndexed.blockWidth (source (pairFst c))) r (spatialCount (source (pairFst c)) + i)
  coefficient := coefficient source active row
  numerator := n
  denominator := d
  exponent_le _ _ _ _ _ := (FixedWidthPolynomial.entry_lt _ _ _).le

noncomputable def arityCode (source : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (parameterCount (source (pairFst c)))

def widthCode (source : List Bool → List Bool) : List Bool → List Bool := TubeIndexed.clearingWidthCode ∘ source ∘ pairFst

noncomputable def termsCode (source : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthPolynomial.countCode (nativeCount ∘ source ∘ pairFst) (TubeIndexed.blockWidth ∘ source ∘ pairFst)

noncomputable def exponentPacket (source : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pairFst q) (pair (pairFst (pairSnd q)) (BinaryNat.add
    (pair (BinaryNatCode.encode (spatialCount (source (pairFst (pairFst q))))) (pairSnd (pairSnd q)))))

noncomputable def exponentRead (source : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthPolynomial.exponentRead (nativeCount ∘ source ∘ pairFst) (TubeIndexed.blockWidth ∘ source ∘ pairFst) ∘ exponentPacket source

theorem arityCode_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : arityCode source ∈ FP :=
  bits_mem_FP ((parameterCount_unary.comp hs).comp pairFst_mem_FP)

theorem widthCode_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : widthCode source ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP hs) TubeIndexed.clearingWidthCode_mem_FP

theorem termsCode_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : termsCode source ∈ FP :=
  FixedWidthPolynomial.countCode_mem_FP ((nativeCount_unary.comp hs).comp pairFst_mem_FP)
    ((TubeIndexed.blockWidth_unary.comp hs).comp pairFst_mem_FP)

theorem exponentPacket_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : exponentPacket source ∈ FP := by
  have hA := bits_mem_FP (((spatialCount_unary.comp hs).comp pairFst_mem_FP).comp pairFst_mem_FP)
  have hi := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hsum := mem_FP_comp (mem_FP_pair hA hi) BinaryNat.add_mem_FP
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) hsum)
  exact mem_FP_of_eq (g := exponentPacket source) h (fun _ => by simp only [exponentPacket, Function.comp_apply, BinaryNatCode.encode])

theorem exponentRead_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : exponentRead source ∈ FP :=
  mem_FP_comp (exponentPacket_mem_FP hs) (FixedWidthPolynomial.exponentRead_mem_FP
    ((nativeCount_unary.comp hs).comp pairFst_mem_FP) ((TubeIndexed.blockWidth_unary.comp hs).comp pairFst_mem_FP))

theorem exponentRead_packet (source : List Bool → List Bool) (c : List Bool) (r i : ℕ)
    (hi : i < parameterCount (source (pairFst c))) :
    Nat.fromBitsLE (exponentRead source (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i)))) =
      FixedWidthPolynomial.entry (TubeIndexed.blockWidth (source (pairFst c))) r (spatialCount (source (pairFst c)) + i) := by
  have hl : spatialCount (source (pairFst c)) + i < nativeCount (source (pairFst c)) := by
    rw [← counts_add]
    omega
  simp only [exponentRead, Function.comp_apply, exponentPacket, pairFst_pair, pairSnd_pair,
    BinaryNat.add_pair, MacaulayBits.fromBits_encode]
  change Nat.fromBitsLE (FixedWidthPolynomial.exponentRead (nativeCount ∘ source ∘ pairFst)
    (TubeIndexed.blockWidth ∘ source ∘ pairFst)
    (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode (spatialCount (source (pairFst c)) + i))))) = _
  rw [FixedWidthPolynomial.exponentRead_packet _ _ c r _ hl, MacaulayBits.fromBits_encode]
  rfl

structure CoordinateReaders (source : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) where
  numerator : List Bool → List Bool
  denominator : List Bool → List Bool
  numeratorEvaluator : SpaceFunction numerator
  denominatorEvaluator : SpaceFunction denominator
  numerator_eq : ∀ c i, i < parameterCount (source (pairFst c)) → ∀ k m, 0 < m →
    numerator (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((n c i).coeff k : ℤ) : ZMod m)
  denominator_eq : ∀ c i, i < parameterCount (source (pairFst c)) → ∀ k m, 0 < m →
    denominator (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((d c i).coeff k : ℤ) : ZMod m)

noncomputable def access (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (C : CoordinateReaders source n d) : IntegerBits.Access (family source active row n d) where
  arity := arityCode source
  width := widthCode source
  terms := termsCode source
  exponent := exponentRead source
  coefficient := coefficientValue source active row
  numerator := C.numerator
  denominator := C.denominator
  arity_eq _ := Nat.fromBitsLE_bits _
  width_eq c := by simp only [family, widthCode, Function.comp_apply, TubeIndexed.clearingWidthCode_code, MacaulayBits.fromBits_encode]
  terms_eq c := by simp only [family, termsCode, FixedWidthPolynomial.countCode_code, MacaulayBits.fromBits_encode, Function.comp_apply]
  exponent_eq c r _ i hi := exponentRead_packet source c r i hi
  coefficient_eq c r _ m hm := coefficientValue_packet source active row c r m hm
  numerator_eq := C.numerator_eq
  denominator_eq := C.denominator_eq


attribute [local irreducible] exponentRead

theorem access_controls (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (C : CoordinateReaders source n d) (hs : source ∈ FP) : (access source active row n d C).ControlsPolyTime := by
  constructor
  · change arityCode source ∈ FP
    exact arityCode_mem_FP hs
  · change widthCode source ∈ FP
    exact widthCode_mem_FP hs
  · change termsCode source ∈ FP
    exact termsCode_mem_FP hs
  · dsimp only [access]
    exact exponentRead_mem_FP hs

attribute [local irreducible] family

theorem evaluator (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (C : CoordinateReaders source n d) (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    SpaceFunction (family source active row n d).value :=
  (access source active row n d C).evaluator
    (access_controls source active row n d C hs)
    (coefficientEvaluator source active row hs ha hr) C.numeratorEvaluator C.denominatorEvaluator

end LeanCanny.ETR.TubeParameter
