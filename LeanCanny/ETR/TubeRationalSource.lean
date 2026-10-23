/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeIndexedSpace
public import LeanCanny.ETR.TubeIndexedBounds
public import LeanCanny.Algebra.IndexedSource

/-! # Actual tube sources for streamed rational substitution

A static flag selects tube or projection coefficients. All caller fields are
FP maps; native coefficient lookup runs through the complete space routines.
The even clearing width and finite indexed source come from proved bounds.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRational

open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding
open Algebra.MatrixPower
open Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerPolynomial
  TubePolynomial.integerProjection TubeProjection.decodedRow

noncomputable def dimension (projection : Bool) (bits : List Bool) : ℕ :=
  if projection then TubeIndexed.projectionDimension bits else TubeIndexed.tubeDimension bits

theorem dimension_unary (projection : Bool) : UnaryFn (dimension projection) := by
  cases projection
  · exact TubeIndexed.tubeDimension_unary
  · exact TubeIndexed.projectionDimension_unary

noncomputable def coefficient (projection : Bool) (source active row : List Bool → List Bool) (c : List Bool) (r : ℕ) : ℤ :=
  if projection then TubeIndexed.projectionCoefficient (source c)
    (activeSet (TubeIndexed.arity (source c)) (active c))
    (TubeProjection.decodedRow (TubeIndexed.compiled source) row c) r
  else TubeIndexed.tubeCoefficient (source c) (activeSet (TubeIndexed.arity (source c)) (active c)) r

theorem coefficient_lift (projection : Bool) (source active row : List Bool → List Bool) (q : List Bool) (r : ℕ) :
    coefficient projection (source ∘ pairFst) (active ∘ pairFst) (row ∘ pairFst) q r =
      coefficient projection source active row (pairFst q) r := by
  unfold coefficient TubeProjection.decodedRow
  rfl

noncomputable def nativeValue (projection : Bool) (source active row modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  IntegerBits.coefficientResidue (coefficient projection source active row (pairFst q) (Nat.fromBitsLE (pairSnd q)))
    (Nat.fromBitsLE (modulus (pairFst q)) + 1)

theorem nativeEvaluator (projection : Bool) (source active row modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (nativeValue projection source active row modulus) := by
  cases projection
  · exact TubeIndexed.tubeResidueEvaluator source active modulus hs ha hm
  · exact TubeIndexed.projectionResidueEvaluator source active row modulus hs ha hr hm

/-- Change `pair (pair context rank) modulus` into `pair (pair context modulus) rank`. -/
def rankPacket (q : List Bool) : List Bool := pair (pair (pairFst (pairFst q)) (pairSnd q)) (pairSnd (pairFst q))

theorem rankPacket_mem_FP : rankPacket ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def coefficientValue (projection : Bool) (source active row : List Bool → List Bool) (q : List Bool) : List Bool :=
  IntegerBits.coefficientResidue (coefficient projection source active row (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd (pairFst q))))
    (Nat.fromBitsLE (pairSnd q) + 1)

attribute [local irreducible] coefficient

section Packet
attribute [local irreducible] IntegerBits.coefficientResidue

theorem coefficientEvaluator (projection : Bool) (source active row : List Bool → List Bool)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) : SpaceFunction (coefficientValue projection source active row) := by
  let R := nativeEvaluator projection (source ∘ pairFst) (active ∘ pairFst) (row ∘ pairFst) pairSnd
    (mem_FP_comp pairFst_mem_FP hs) (mem_FP_comp pairFst_mem_FP ha) (mem_FP_comp pairFst_mem_FP hr) pairSnd_mem_FP
  let E := R.precompose rankPacket rankPacket_mem_FP
  refine E.congr (funext fun q => ?_)
  simp only [nativeValue, coefficientValue, rankPacket, pairFst_pair, pairSnd_pair,
    Function.comp_apply, coefficient_lift]

theorem coefficientValue_packet (projection : Bool) (source active row : List Bool → List Bool)
    (c : List Bool) (r m : ℕ) (hm : 0 < m) :
    coefficientValue projection source active row (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      IntegerBits.coefficientResidue (coefficient projection source active row c r) m := by
  simp only [coefficientValue, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]

end Packet

noncomputable def indexedSource (projection : Bool) (source active row : List Bool → List Bool) : IntegerBits.IndexedSource :=
  IntegerBits.IndexedSource.dense (fun c => dimension projection (source c))
    (fun c => TubeIndexed.blockWidth (source c)) (fun c => 2 ^ TubeIndexed.blockWidth (source c))
    (coefficient projection source active row) (fun _ _ _ => (Algebra.FixedWidthPolynomial.entry_lt _ _ _).le)

noncomputable def family (projection : Bool) (source active row : List Bool → List Bool)
    (numerator denominator : List Bool → ℕ → Polynomial ℤ) : IntegerBits.Family :=
  (indexedSource projection source active row).withCoordinates numerator denominator

noncomputable def arityCode (projection : Bool) (source : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (dimension projection (source c))

def widthCode (source : List Bool → List Bool) : List Bool → List Bool := TubeIndexed.clearingWidthCode ∘ source

noncomputable def termsCode (projection : Bool) (source : List Bool → List Bool) : List Bool → List Bool :=
  Algebra.FixedWidthPolynomial.countCode (fun c => dimension projection (source c)) (fun c => TubeIndexed.blockWidth (source c))

noncomputable def exponentRead (projection : Bool) (source : List Bool → List Bool) : List Bool → List Bool :=
  Algebra.FixedWidthPolynomial.exponentRead (fun c => dimension projection (source c)) (fun c => TubeIndexed.blockWidth (source c))

theorem arityCode_mem_FP (projection : Bool) {source : List Bool → List Bool} (hs : source ∈ FP) : arityCode projection source ∈ FP :=
  bits_mem_FP ((dimension_unary projection).comp hs)

theorem widthCode_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : widthCode source ∈ FP :=
  mem_FP_comp hs TubeIndexed.clearingWidthCode_mem_FP

theorem termsCode_mem_FP (projection : Bool) {source : List Bool → List Bool} (hs : source ∈ FP) : termsCode projection source ∈ FP :=
  Algebra.FixedWidthPolynomial.countCode_mem_FP ((dimension_unary projection).comp hs) (TubeIndexed.blockWidth_unary.comp hs)

theorem exponentRead_mem_FP (projection : Bool) {source : List Bool → List Bool} (hs : source ∈ FP) : exponentRead projection source ∈ FP :=
  Algebra.FixedWidthPolynomial.exponentRead_mem_FP ((dimension_unary projection).comp hs) (TubeIndexed.blockWidth_unary.comp hs)

theorem arityCode_eq (projection : Bool) (source : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (arityCode projection source c) = dimension projection (source c) := Nat.fromBitsLE_bits _

theorem widthCode_eq (source : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (widthCode source c) = 2 ^ TubeIndexed.blockWidth (source c) := by
  simp only [widthCode, Function.comp_apply, TubeIndexed.clearingWidthCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem termsCode_eq (projection : Bool) (source : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (termsCode projection source c) =
      Algebra.FixedWidthPolynomial.count (dimension projection (source c)) (TubeIndexed.blockWidth (source c)) := by
  simp only [termsCode, Algebra.FixedWidthPolynomial.countCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem exponentRead_packet (projection : Bool) (source : List Bool → List Bool) (c : List Bool) (r i : ℕ)
    (hi : i < dimension projection (source c)) :
    Nat.fromBitsLE (exponentRead projection source (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i)))) =
      Algebra.FixedWidthPolynomial.entry (TubeIndexed.blockWidth (source c)) r i := by
  rw [exponentRead, Algebra.FixedWidthPolynomial.exponentRead_packet _ _ c r i hi, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def sourceAccess (projection : Bool) (source active row : List Bool → List Bool) :
    IntegerBits.IndexedSource.Access (indexedSource projection source active row) :=
  IntegerBits.IndexedSource.denseAccess _ _ _ _ (fun _ _ _ => (Algebra.FixedWidthPolynomial.entry_lt _ _ _).le) (arityCode projection source) (widthCode source)
    (coefficientValue projection source active row) (arityCode_eq projection source) (widthCode_eq source)
    (fun c r _ m hm => coefficientValue_packet projection source active row c r m hm)

theorem sourceAccess_controls (projection : Bool) (source active row : List Bool → List Bool) (hs : source ∈ FP) :
    (sourceAccess projection source active row).ControlsPolyTime :=
  ⟨arityCode_mem_FP projection hs, widthCode_mem_FP hs, termsCode_mem_FP projection hs, exponentRead_mem_FP projection hs⟩

end LeanCanny.ETR.TubeRational
