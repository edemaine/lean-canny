/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueDeterminantSource
public import LeanCanny.Algebra.IntegralMixedVirtualNativeAccess

/-! # Native metadata for the second virtual determinant digit

The exact Macaulay level, column count, double-prefix rank, reflected
coefficient and matrix addresses are derived from original metadata.
The writer preserves the complete original query and caller modulus.
These metadata certificates give no Gram-entry evaluator for free.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueDeterminantMetadata
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial IntegralCoordinateBasis
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedCoordinateSquarefree
open IntegralMixedValueDoubleNilpotent IntegralMixedValueDeterminantSource IntegralMixedVirtualNativeBits

theorem level_eq {n : ℕ} (P : SpatialSource n) (r : Rule n) :
    Macaulay.level (RelativeProjectiveValueGram.degrees
      (fun _ : Fin (n - r.critical.offset.val + 1) => coordinateDegree P r) P.degree) =
      P.degree - 1 + (n - r.critical.offset.val + 1) * (coordinateDegree P r - 1) + 1 := by
  simp only [Macaulay.level, RelativeProjectiveValueGram.degrees, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem coordinateDegree_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (h : Metadata F I) :
    BinaryFn (fun q => coordinateDegree (F.spatial q) (F.rule q)) :=
  PurePowerReductionBounds.dimension_binary (free_unary F I h) h.degree

theorem level_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (h : Metadata F I) :
    BinaryFn (fun q => Macaulay.level (RelativeProjectiveValueGram.degrees
      (fun _ : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) =>
        coordinateDegree (F.spatial q) (F.rule q)) (F.spatial q).degree)) :=
  (((h.degree.sub (BinaryFn.const 1)).add
    ((BinaryFn.ofUnary (free_unary F I h)).mul ((coordinateDegree_binary F I h).sub (BinaryFn.const 1)))).add
      (BinaryFn.const 1)).of_eq (fun q => (level_eq (F.spatial q) (F.rule q)).symm)

theorem width_unary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (h : Metadata F I) :
    UnaryFn (fun q => IntegralMixedGridValue.width (F.spatial q) (F.rule q)) :=
  (UnaryFn.length (level_binary F I h).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

theorem columns_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (h : Metadata F I) :
    BinaryFn (fun q => count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))) :=
  ((BinaryFn.const 2).powUnary (width_unary F I h)).powUnary ((free_unary F I h).add (UnaryFn.const 1))

theorem dimension_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (h : Metadata F I) :
    BinaryFn (fun q => IntegralMixedGridValue.dimension (F.spatial q) (F.rule q)) :=
  ((BinaryFn.ofUnary (free_unary F I h)).add (BinaryFn.const 3)).mul (columns_binary F I h)

theorem reflectedIndex_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (h : Metadata F I)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (hk : BinaryFn (fun q => (index q).val)) :
    BinaryFn (fun q => reflectedIndex (F.spatial q) (F.rule q) (index q)) :=
  (dimension_binary F I h).sub (hk.sub (BinaryFn.const 1))

theorem rank_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (h : Metadata F I)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q))) :
    BinaryFn (source F I index).rank :=
  ((BinaryFn.const 2).powUnary h.width).powUnary (h.birth.add (UnaryFn.const 2))

theorem row_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (h : Metadata F I)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (hk : BinaryFn (fun q => (index q).val)) : BinaryFn (fun q => (row F I index q).val) :=
  (reflectedIndex_binary F I h index hk).add (((BinaryFn.const 2).powUnary h.width).mul h.row)

theorem col_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (h : Metadata F I) :
    BinaryFn (fun q => (col F I q).val) :=
  ((BinaryFn.const 0).add (((BinaryFn.const 2).powUnary h.width).mul h.col))

noncomputable def address (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q))) (q : List Bool) : List Bool :=
  pair q (pair (BinaryNatCode.encode (row F I index q).val) (BinaryNatCode.encode (col F I q).val))

theorem address_FP (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (h : Metadata F I)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (hk : BinaryFn (fun q => (index q).val)) : address F I index ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (row_binary F I h index hk).bits_mem_FP (col_binary F I h).bits_mem_FP)

theorem address_original (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q))) (q : List Bool) :
    pairFst (address F I index q) = q := pairFst_pair _ _

theorem positive_FP (F : Family)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (hk : BinaryFn (fun q => (index q).val)) : FPPred (fun q => 0 < (index q).val) :=
  (BinaryFn.const 0).lt hk

end LeanCanny.Algebra.IntegralMixedValueDeterminantMetadata
