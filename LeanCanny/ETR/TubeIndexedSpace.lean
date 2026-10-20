/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeIndexedSource

/-! # Complete residue readers for indexed tube and projection sources

The source bits, active mask, row, and modulus are FP fields of the caller's
context. A binary rank is the second field of each coefficient query. The
complete native coefficient machines supply exactly the indexed coefficients,
with their source validation and all suspended work included in space.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeIndexed
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding
open Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerPolynomial
  TubePolynomial.integerProjection TubeCoefficient.value TubeProjection.value

def compiled (source : List Bool → List Bool) : List Bool → List Bool := RationalSubstitutionBits.compiledTerm ∘ source

theorem compiled_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : compiled source ∈ FP :=
  mem_FP_comp (f := source) (g := RationalSubstitutionBits.compiledTerm) hs RationalSubstitutionBits.compiledTerm_mem_FP

noncomputable def tubeAt (source active modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) : List Bool :=
  residueBits ((tubeCoefficient (source c) (activeSet (arity (source c)) (active c)) r : ℤ) :
    ZMod (Nat.fromBitsLE (modulus c) + 1))

noncomputable def tubeResidue (source active modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  tubeAt source active modulus (pairFst q) (Nat.fromBitsLE (pairSnd q))

noncomputable def tubeResidueEvaluator (source active modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ha : active ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (tubeResidue source active modulus) := by
  let src := compiled source ∘ pairFst
  let W := fun q => blockWidth (source (pairFst q))
  let E := TubeCoefficient.evaluator src W (active ∘ pairFst) Algebra.FixedWidthPolynomial.rankTarget (modulus ∘ pairFst)
    (mem_FP_comp pairFst_mem_FP (compiled_mem_FP hs)) ((blockWidth_unary.comp hs).comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP ha) Algebra.FixedWidthPolynomial.rankTarget_mem_FP (mem_FP_comp pairFst_mem_FP hm)
  refine E.congr (funext fun q => ?_)
  have he : TubeZeroQuery.exponent (TubeDense.arity src) W Algebra.FixedWidthPolynomial.rankTarget q =
      tubeExponent (source (pairFst q)) (Nat.fromBitsLE (pairSnd q)) := by
    ext j
    simp only [TubeZeroQuery.exponent, Finsupp.coe_equivFunOnFinite_symm, FixedWidthQuery.coordinate,
      Algebra.FixedWidthPolynomial.rankTarget, BinaryNat.normalize_eq_bits, tubeExponent,
      Algebra.FixedWidthPolynomial.nativeExponent, Algebra.FixedWidthPolynomial.entry]
    rfl
  unfold TubeCoefficient.value TubeCoefficient.coefficient
  rw [he]
  rfl

noncomputable def projectionAt (source active row modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) : List Bool :=
  residueBits ((projectionCoefficient (source c) (activeSet (arity (source c)) (active c))
    (TubeProjection.decodedRow (compiled source) row c) r : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

noncomputable def projectionResidue (source active row modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  projectionAt source active row modulus (pairFst q) (Nat.fromBitsLE (pairSnd q))

noncomputable def projectionResidueEvaluator (source active row modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (projectionResidue source active row modulus) := by
  let src := compiled source ∘ pairFst
  let W := fun q => blockWidth (source (pairFst q))
  let E := TubeProjection.evaluator src W (active ∘ pairFst) (row ∘ pairFst) Algebra.FixedWidthPolynomial.rankTarget (modulus ∘ pairFst)
    (mem_FP_comp pairFst_mem_FP (compiled_mem_FP hs)) ((blockWidth_unary.comp hs).comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP ha) (mem_FP_comp pairFst_mem_FP hr) Algebra.FixedWidthPolynomial.rankTarget_mem_FP (mem_FP_comp pairFst_mem_FP hm)
  refine E.congr (funext fun q => ?_)
  have he : TubeProjectionQuery.exponent (TubeDense.arity src) W Algebra.FixedWidthPolynomial.rankTarget q =
      projectionExponent (source (pairFst q)) (Nat.fromBitsLE (pairSnd q)) := by
    ext j
    simp only [TubeProjectionQuery.exponent, Finsupp.coe_equivFunOnFinite_symm, FixedWidthQuery.coordinate,
      Algebra.FixedWidthPolynomial.rankTarget, BinaryNat.normalize_eq_bits, projectionExponent,
      Algebra.FixedWidthPolynomial.nativeExponent, Algebra.FixedWidthPolynomial.entry]
    rfl
  rw [TubeProjection.value_eq_coefficient]
  unfold TubeProjection.coefficient
  rw [he]
  rfl

attribute [local irreducible] tubeAt projectionAt

theorem tubeResidue_packet (source active modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    tubeResidue source active modulus (pair c (BinaryNatCode.encode r)) =
      residueBits ((tubeCoefficient (source c) (activeSet (arity (source c)) (active c)) r : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  conv_lhs =>
    unfold tubeResidue
    rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold tubeAt
  rfl

theorem projectionResidue_packet (source active row modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    projectionResidue source active row modulus (pair c (BinaryNatCode.encode r)) =
      residueBits ((projectionCoefficient (source c) (activeSet (arity (source c)) (active c))
        (TubeProjection.decodedRow (compiled source) row c) r : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  conv_lhs =>
    unfold projectionResidue
    rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold projectionAt
  rfl

end LeanCanny.ETR.TubeIndexed
