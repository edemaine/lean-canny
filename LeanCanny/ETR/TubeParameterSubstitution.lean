/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeParameterSource
public import LeanCanny.Algebra.IndexedSource

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

noncomputable def indexedSource (source active row : List Bool → List Bool) : IntegerBits.IndexedSource :=
  IntegerBits.IndexedSource.projected (nativeCount ∘ source ∘ pairFst)
    (parameterCount ∘ source ∘ pairFst) (TubeIndexed.blockWidth ∘ source ∘ pairFst)
    (fun c => 2 ^ TubeIndexed.blockWidth (source (pairFst c)))
    (fun c i => spatialCount (source (pairFst c)) + i) (coefficient source active row)
    (fun _ _ _ => (FixedWidthPolynomial.entry_lt _ _ _).le)

noncomputable def family (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) : IntegerBits.Family :=
  (indexedSource source active row).withCoordinates n d

noncomputable def arityCode (source : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (parameterCount (source (pairFst c)))

def widthCode (source : List Bool → List Bool) : List Bool → List Bool := TubeIndexed.clearingWidthCode ∘ source ∘ pairFst

noncomputable def termsCode (source : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthPolynomial.countCode (nativeCount ∘ source ∘ pairFst) (TubeIndexed.blockWidth ∘ source ∘ pairFst)

/-- A binary writer for the native index of a substituted parameter. -/
noncomputable def coordinateIndexCode (source : List Bool → List Bool) (q : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNatCode.encode (spatialCount (source (pairFst (pairFst q))))) (pairSnd q))

noncomputable def exponentPacket (source : List Bool → List Bool) (q : List Bool) : List Bool :=
  IntegerBits.IndexedSource.projectedPacket (coordinateIndexCode source) q

noncomputable def exponentRead (source : List Bool → List Bool) : List Bool → List Bool :=
  IntegerBits.IndexedSource.projectedExponentRead (nativeCount ∘ source ∘ pairFst)
    (TubeIndexed.blockWidth ∘ source ∘ pairFst) (coordinateIndexCode source)

theorem arityCode_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : arityCode source ∈ FP :=
  bits_mem_FP ((parameterCount_unary.comp hs).comp pairFst_mem_FP)

theorem widthCode_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : widthCode source ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP hs) TubeIndexed.clearingWidthCode_mem_FP

theorem termsCode_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : termsCode source ∈ FP :=
  FixedWidthPolynomial.countCode_mem_FP ((nativeCount_unary.comp hs).comp pairFst_mem_FP)
    ((TubeIndexed.blockWidth_unary.comp hs).comp pairFst_mem_FP)

theorem coordinateIndexCode_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : coordinateIndexCode source ∈ FP := by
  have hA := bits_mem_FP (((spatialCount_unary.comp hs).comp pairFst_mem_FP).comp pairFst_mem_FP)
  exact mem_FP_comp (mem_FP_pair hA pairSnd_mem_FP) BinaryNat.add_mem_FP

theorem coordinateIndexCode_packet (source : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    coordinateIndexCode source (pair c (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (spatialCount (source (pairFst c)) + i) := by
  simp only [coordinateIndexCode, pairFst_pair, pairSnd_pair, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem coordinateIndex_lt (source : List Bool → List Bool) (c : List Bool) (i : ℕ)
    (hi : i < parameterCount (source (pairFst c))) :
    spatialCount (source (pairFst c)) + i < nativeCount (source (pairFst c)) := by
  rw [← counts_add]
  omega

theorem exponentPacket_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : exponentPacket source ∈ FP :=
  IntegerBits.IndexedSource.projectedPacket_mem_FP (coordinateIndexCode_mem_FP hs)

theorem exponentRead_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : exponentRead source ∈ FP :=
  IntegerBits.IndexedSource.projectedExponentRead_mem_FP
    ((nativeCount_unary.comp hs).comp pairFst_mem_FP) ((TubeIndexed.blockWidth_unary.comp hs).comp pairFst_mem_FP)
    (coordinateIndexCode_mem_FP hs)

theorem exponentRead_packet (source : List Bool → List Bool) (c : List Bool) (r i : ℕ)
    (hi : i < parameterCount (source (pairFst c))) :
    Nat.fromBitsLE (exponentRead source (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i)))) =
      FixedWidthPolynomial.entry (TubeIndexed.blockWidth (source (pairFst c))) r (spatialCount (source (pairFst c)) + i) :=
  IntegerBits.IndexedSource.projectedExponentRead_packet (nativeCount ∘ source ∘ pairFst)
    (parameterCount ∘ source ∘ pairFst) (TubeIndexed.blockWidth ∘ source ∘ pairFst)
    (coordinateIndexCode source) (fun c i => spatialCount (source (pairFst c)) + i)
    (fun c i _ => coordinateIndexCode_packet source c i) (coordinateIndex_lt source) c r i hi

def CoordinateReaders (source : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) :=
  IntegerBits.CoordinateReaders (fun c => parameterCount (source (pairFst c))) n d

-- Preserve the original qualified constructor and field names.
namespace CoordinateReaders
variable {source : List Bool → List Bool} {n d : List Bool → ℕ → Polynomial ℤ}

abbrev mk := @IntegerBits.CoordinateReaders.mk (fun c => parameterCount (source (pairFst c))) n d
abbrev numerator (self : CoordinateReaders source n d) := IntegerBits.CoordinateReaders.numerator self
abbrev denominator (self : CoordinateReaders source n d) := IntegerBits.CoordinateReaders.denominator self
abbrev numeratorEvaluator (self : CoordinateReaders source n d) := IntegerBits.CoordinateReaders.numeratorEvaluator self
abbrev denominatorEvaluator (self : CoordinateReaders source n d) := IntegerBits.CoordinateReaders.denominatorEvaluator self
abbrev numerator_eq (self : CoordinateReaders source n d) := IntegerBits.CoordinateReaders.numerator_eq self
abbrev denominator_eq (self : CoordinateReaders source n d) := IntegerBits.CoordinateReaders.denominator_eq self

end CoordinateReaders

noncomputable def sourceAccess (source active row : List Bool → List Bool) :
    IntegerBits.IndexedSource.Access (indexedSource source active row) where
  arity := arityCode source
  width := widthCode source
  terms := termsCode source
  exponent := exponentRead source
  coefficient := coefficientValue source active row
  arity_eq _ := Nat.fromBitsLE_bits _
  width_eq c := by
    simp only [indexedSource, IntegerBits.IndexedSource.projected, widthCode, Function.comp_apply,
      TubeIndexed.clearingWidthCode_code, MacaulayBits.fromBits_encode]
  terms_eq c := by
    simp only [indexedSource, IntegerBits.IndexedSource.projected, termsCode, FixedWidthPolynomial.countCode_code,
      MacaulayBits.fromBits_encode, Function.comp_apply]
  exponent_eq c r _ i hi := exponentRead_packet source c r i hi
  coefficient_eq c r _ m hm := coefficientValue_packet source active row c r m hm

attribute [local irreducible] exponentRead

theorem sourceAccess_controls (source active row : List Bool → List Bool) (hs : source ∈ FP) :
    (sourceAccess source active row).ControlsPolyTime := by
  constructor
  · exact arityCode_mem_FP hs
  · exact widthCode_mem_FP hs
  · exact termsCode_mem_FP hs
  · exact exponentRead_mem_FP (source := source) hs

noncomputable def access (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (C : CoordinateReaders source n d) : IntegerBits.Access (family source active row n d) :=
  IntegerBits.IndexedSource.access (sourceAccess source active row) C

theorem access_controls (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (C : CoordinateReaders source n d) (hs : source ∈ FP) : (access source active row n d C).ControlsPolyTime :=
  IntegerBits.IndexedSource.access_controls _
    (sourceAccess_controls source active row hs) C

attribute [local irreducible] family

theorem evaluator (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (C : CoordinateReaders source n d) (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    SpaceFunction (family source active row n d).value :=
  (access source active row n d C).evaluator
    (access_controls source active row n d C hs)
    (coefficientEvaluator source active row hs ha hr) C.numeratorEvaluator C.denominatorEvaluator

end LeanCanny.ETR.TubeParameter
