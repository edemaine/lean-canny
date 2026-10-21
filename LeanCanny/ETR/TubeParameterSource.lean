/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeParameterLayout
public import LeanCanny.Algebra.RationalSubstitutionResidue

/-! # The actual spatial-coefficient source for parameter substitution

A context is `pair originalContext spatialRank`. Source ranks enumerate the full
native polynomial, and a spatial-prefix guard selects its coefficient slice.
Canonical residue packets carry their modulus separately. Every child call is
provided by the existing regular-system coefficient evaluator.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeParameter
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Encoding.Brackets Algebra.MatrixPower
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerProjection
  TubeRegularHomogenization.value nativePolynomial

noncomputable def spatialSize (source : List Bool → List Bool) : List Bool → ℕ := spatialCount ∘ source
def blockWidth (source : List Bool → List Bool) : List Bool → ℕ := TubeIndexed.blockWidth ∘ source

noncomputable def nativeCoefficient (source active row : List Bool → List Bool) (c : List Bool) (r : ℕ) : ℤ :=
  (nativePolynomial source active row c).coeff (FixedWidthPolynomial.nativeExponent (TubeRegularHomogenization.outputEquiv (source c))
    (TubeIndexed.blockWidth (source c)) r)


attribute [local irreducible] nativeCoefficient Algebra.RationalSubstitution.IntegerBits.coefficientResidue

theorem nativeCoefficient_lift (source active row : List Bool → List Bool) (q : List Bool) (r : ℕ) :
    nativeCoefficient (source ∘ pairFst) (active ∘ pairFst) (row ∘ pairFst) q r =
      nativeCoefficient source active row (pairFst q) r := by
  unfold nativeCoefficient nativePolynomial TubeRegularBits.decodedIndex TubeProjection.decodedRow
    TubeProjectionRow.index TubeRegularBits.oldRow
  rfl

theorem nativeCoefficient_packet (source active row modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    TubeRegularHomogenization.value source active row modulus (pair c (BinaryNatCode.encode r)) =
      Algebra.RationalSubstitution.IntegerBits.coefficientResidue (nativeCoefficient source active row c r) (Nat.fromBitsLE (modulus c) + 1) := by
  unfold nativeCoefficient nativePolynomial Algebra.RationalSubstitution.IntegerBits.coefficientResidue
  exact TubeRegularHomogenization.value_packet source active row modulus c r

noncomputable def coefficient (source active row : List Bool → List Bool) (c : List Bool) (r : ℕ) : ℤ :=
  if PartialCoefficientBits.Matches (spatialSize source) (blockWidth source) (pair c (BinaryNatCode.encode r))
  then nativeCoefficient source active row (pairFst c) r else 0

/-- Retain the original context and modulus, discarding the selected spatial rank. -/
def nativePacket (q : List Bool) : List Bool :=
  pair (pair (PartialCoefficientBits.originalContext (pairFst q)) (pairSnd q))
    (BinaryNat.normalize (pairSnd (pairFst q)))

theorem nativePacket_mem_FP : nativePacket ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP PartialCoefficientBits.originalContext_mem_FP
  have hr := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  exact mem_FP_pair (mem_FP_pair hc pairSnd_mem_FP) hr

noncomputable def originalValue (source active row : List Bool → List Bool) (q : List Bool) : List Bool :=
  TubeRegularHomogenization.value (source ∘ pairFst) (active ∘ pairFst) (row ∘ pairFst) pairSnd (nativePacket q)

noncomputable def coefficientValue (source active row : List Bool → List Bool) (q : List Bool) : List Bool :=
  if PartialCoefficientBits.Matches (spatialSize source) (blockWidth source) (pairFst q)
  then originalValue source active row q else []

theorem coefficientEvaluator (source active row : List Bool → List Bool)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) : SpaceFunction (coefficientValue source active row) := by
  have ER := TubeRegularHomogenization.evaluator (source ∘ pairFst) (active ∘ pairFst) (row ∘ pairFst) pairSnd
    (mem_FP_comp pairFst_mem_FP hs) (mem_FP_comp pairFst_mem_FP ha) (mem_FP_comp pairFst_mem_FP hr) pairSnd_mem_FP
  have EN := ER.precompose nativePacket nativePacket_mem_FP
  have hg := (PartialCoefficientBits.matches_fppred (spatialCount_unary.comp hs)
    (TubeIndexed.blockWidth_unary.comp hs)).comp pairFst_mem_FP
  have E := SpaceFunction.branch (fun q => decide (PartialCoefficientBits.Matches (spatialSize source) (blockWidth source) (pairFst q)))
    hg.flag_mem_FP EN (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun q => by simp only [coefficientValue, originalValue, Function.comp_apply, decide_eq_true_eq])

theorem originalValue_packet (source active row : List Bool → List Bool) (c : List Bool) (r m : ℕ) (hm : 0 < m) :
    originalValue source active row (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits ((nativeCoefficient source active row (pairFst c) r : ℤ) : ZMod m) := by
  simp only [originalValue, nativePacket, PartialCoefficientBits.originalContext, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode]
  have h := nativeCoefficient_packet (source ∘ pairFst) (active ∘ pairFst) (row ∘ pairFst) pairSnd
    (pair (pairFst c) (BinaryNatCode.encode (m - 1))) r
  rw [nativeCoefficient_lift] at h
  rw [pairSnd_pair, MacaulayBits.fromBits_encode, Nat.sub_add_cancel hm] at h
  simp only [pairFst_pair, Algebra.RationalSubstitution.IntegerBits.coefficientResidue] at h
  exact h

theorem coefficientValue_packet (source active row : List Bool → List Bool) (c : List Bool) (r m : ℕ) (hm : 0 < m) :
    coefficientValue source active row (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits ((coefficient source active row c r : ℤ) : ZMod m) := by
  rw [coefficientValue, pairFst_pair, coefficient]
  split_ifs
  · exact originalValue_packet source active row c r m hm
  · simp [residueBits, BinaryNatCode.encode]

end LeanCanny.ETR.TubeParameter
