/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalCoordinatePathSource
public import LeanCanny.Algebra.ClearingMatrixSpace
public import LeanCanny.Algebra.PreparedPolynomialContext

/-! # Uniform native coefficient evaluation of whole coordinate paths

All substitution factors are accessed through the two indexed stage readers.
One layered matrix product evaluates the entire input-dependent path, with no
intermediate polynomial or exact-degree oracle. Binary degree controls and
unary path length suffice for the computation certificate on all words.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalCoordinatePathBits
open Polynomial UnivariateRational
open LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution.IntegerBits (context selectedDegree mValue)

def origin (p : List Bool) : List Bool := context (pairFst p)
def stageWord (p : List Bool) : List Bool := pairFst (pairSnd p)
def rowWord (p : List Bool) : List Bool := pairFst (pairSnd (pairSnd p))
def colWord (p : List Bool) : List Bool := pairSnd (pairSnd (pairSnd p))
def stage (F : Source) (p : List Bool) : ℕ := min (Nat.fromBitsLE (stageWord p)) (F.depth (origin p))
def stageContext (F : Source) (p : List Bool) : List Bool := pair (origin p) (BinaryNatCode.encode (stage F p))
def entryExponent (F : Source) (p : List Bool) : ℕ := F.degree (origin p) ^ stage F p

noncomputable def indexedNumerator (F : Source) (p : List Bool) : ℤ[X] := (F.inner (pairFst p) (Nat.fromBitsLE (pairSnd p))).numerator
noncomputable def indexedDenominator (F : Source) (p : List Bool) : ℤ[X] := (F.inner (pairFst p) (Nat.fromBitsLE (pairSnd p))).denominator
noncomputable def kernelNumerator (F : Source) : List Bool → ℤ[X] := indexedNumerator F ∘ stageContext F
noncomputable def kernelDenominator (F : Source) : List Bool → ℤ[X] := indexedDenominator F ∘ stageContext F

noncomputable def entry (F : Source) : List Bool → List Bool :=
  ClearingMatrixBits.value (kernelNumerator F) (kernelDenominator F) (entryExponent F)
    (fun p => Nat.fromBitsLE (rowWord p)) (fun p => Nat.fromBitsLE (colWord p)) (pairSnd ∘ pairFst)

theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP RationalSubstitution.IntegerBits.context_mem_FP
theorem stageWord_FP : stageWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem rowWord_FP : rowWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem colWord_FP : colWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

theorem stage_unary (F : Source) (hK : UnaryFn F.depth) : UnaryFn (stage F) :=
  UnaryFn.fromBitsLE_min stageWord_FP (hK.comp origin_FP)

theorem stageContext_FP (F : Source) (hK : UnaryFn F.depth) : stageContext F ∈ FP :=
  mem_FP_pair origin_FP (bits_mem_FP (stage_unary F hK))

theorem entryExponent_binary (F : Source) (hD : BinaryFn F.degree) (hK : UnaryFn F.depth) : BinaryFn (entryExponent F) := by
  have hd : BinaryFn (F.degree ∘ origin) := hD.comp origin_FP
  exact hd.powUnary (stage_unary F hK)

theorem entryEvaluator (F : Source) (hD : BinaryFn F.degree) (hK : UnaryFn F.depth)
    (N : SpaceFunction (PrimitivePairBits.coefficient (indexedNumerator F)))
    (D : SpaceFunction (PrimitivePairBits.coefficient (indexedDenominator F))) : SpaceFunction (entry F) := by
  have Q := SpaceFunction.ofFP _ (stageContext_FP F hK)
  have EN := PrimitivePairBits.withContextEvaluator _ (stageContext F) Q N
  have ED := PrimitivePairBits.withContextEvaluator _ (stageContext F) Q D
  exact ClearingMatrixBits.evaluator (kernelNumerator F) (kernelDenominator F) (entryExponent F)
    (fun p => Nat.fromBitsLE (rowWord p)) (fun p => Nat.fromBitsLE (colWord p)) (pairSnd ∘ pairFst)
    (entryExponent_binary F hD hK) (BinaryFn.fromBits rowWord_FP) (BinaryFn.fromBits colWord_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) EN ED

theorem entry_packet (F : Source) (q : List Bool) (s : ℕ) (i j : Fin (width F q)) :
    entry F (pair q (pair (BinaryNatCode.encode s) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      MatrixPower.residueBits ((factor F q s).map (Int.castRingHom (ZMod (mValue q))) i j) := by
  simp only [entry, ClearingMatrixBits.value, kernelNumerator, kernelDenominator, indexedNumerator, indexedDenominator,
    Function.comp_apply, stageContext, stage, entryExponent, origin, stageWord, rowWord, colWord,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [clear_X_pow]
  change _ = MatrixPower.residueBits
    ((if i.val ≤ F.degree (context q) ^ min s (F.depth (context q)) then
      ((F.inner (context q) (min s (F.depth (context q)))).numerator ^ i.val *
        (F.inner (context q) (min s (F.depth (context q)))).denominator ^
          (F.degree (context q) ^ min s (F.depth (context q)) - i.val)).coeff j.val else 0 : ℤ) : ZMod (mValue q))
  split_ifs
  · rfl
  · simp only [Polynomial.coeff_zero, RationalSubstitution.IntegerBits.coefficientResidue, Int.cast_zero]

noncomputable def access (F : Source) (numerator : Bool) (hD : BinaryFn F.degree) (hK : UnaryFn F.depth) :
    MatrixProductBits.Access (productFamily F numerator) where
  width := width_binary F hD hK
  count := BinaryFn.of_bits (bits_mem_FP (hK.comp RationalSubstitution.IntegerBits.context_mem_FP))
  modulus := (BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)
  row := BinaryFn.const (if numerator then 1 else 0)
  col := BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  entry := entry F
  entry_eq := entry_packet F

theorem coefficientEvaluator (F : Source) (numerator : Bool) (hD : BinaryFn F.degree) (hK : UnaryFn F.depth)
    (N : SpaceFunction (PrimitivePairBits.coefficient (indexedNumerator F)))
    (D : SpaceFunction (PrimitivePairBits.coefficient (indexedDenominator F))) :
    SpaceFunction (PrimitivePairBits.coefficient (F.component numerator)) :=
  (MatrixProductBits.evaluator (productFamily F numerator) (access F numerator hD hK) (entryEvaluator F hD hK N D)).congr (value_eq F numerator)

theorem coefficientEvaluators (F : Source) (hD : BinaryFn F.degree) (hK : UnaryFn F.depth)
    (N : SpaceFunction (PrimitivePairBits.coefficient (indexedNumerator F)))
    (D : SpaceFunction (PrimitivePairBits.coefficient (indexedDenominator F))) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => (F.coordinate c).numerator)) ∧
      SpaceFunction (PrimitivePairBits.coefficient (fun c => (F.coordinate c).denominator)) :=
  ⟨coefficientEvaluator F true hD hK N D, coefficientEvaluator F false hD hK N D⟩

end LeanCanny.Algebra.RationalCoordinatePathBits
