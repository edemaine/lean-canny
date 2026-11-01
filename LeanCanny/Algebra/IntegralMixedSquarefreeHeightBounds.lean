/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCoordinateBounds
public import LeanCanny.Algebra.IntegralMixedSquarefreeMatrixSource
public import LeanCanny.Algebra.IntegralPrincipalHeightBounds

/-! # Derived original-source heights for actual squarefree exceptional cuts

The same virtual coordinate source supplies every principal determinant
entry. Its derivative and determinant bounds yield the actual squarefree
factor's nilpotent matrix, then coefficient extraction gives raw old-bank
matrix bounds. No selected-component injectivity or factor-height oracle
is needed, and the spatial dimension is fixed before scalar births.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeHeightBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial IntegralCoordinateBasis
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource
open IntegralMixedCoordinateBounds IntegralMixedCoordinateSquarefree
open scoped Classical

def height (n M W D S L G : ℕ) : ℕ :=
  IntegralPrincipalHeightBounds.height (IntegralMixedExceptionalBounds.K (n + 1) D) M
    (IntegralMixedCoordinateBounds.height n M W D S L G)

theorem height_binary {n M W D S L G : List Bool → ℕ}
    (hn : UnaryFn n) (hM : BinaryFn M) (hW : UnaryFn W) (hD : BinaryFn D)
    (hS : BinaryFn S) (hL : BinaryFn L) (hG : BinaryFn G) :
    BinaryFn (fun q => height (n q) (M q) (W q) (D q) (S q) (L q) (G q)) :=
  IntegralPrincipalHeightBounds.height_binary
    (PurePowerReductionBounds.dimension_binary (hn.add (UnaryFn.const 1)) hD) hM
    (IntegralMixedCoordinateBounds.height_binary hn hM hW hD hS hL hG)

theorem coefficient_height (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (H : OriginalBounds F) (q : List Bool)
    (index : Fin (coordinateDegree (F.spatial q) (F.rule q)))
    (k : ℕ) (u v : Fin (count (F.birth q) (F.width q))) :
    (IntegralMixedCutMatrix.coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q)
      (.squarefree (I.coordinate q) index) k u v).natAbs ≤
        2 ^ height (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q)
          (F.cap q) (H.nodes q) (H.bankHeight q) := by
  let C := IntegralMixedCoordinateBounds.height (F.ambient q) (H.rank q) (H.sourceWidth q)
    (H.spatialDegree q) (F.cap q) (H.nodes q) (H.bankHeight q)
  have Hcoeff (j : ℕ) (r t : Fin (count (F.birth q + 1) (F.width q))) :
      (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q)
          (F.rule q) (I.coordinate q)).coeff j) r t).natAbs ≤ 2 ^ C := by
    rw [IntegralMixedSquarefreeMatrixSource.coordinateImage, Polynomial.coeff_map]
    exact (IntegralMixedVirtualBounds.coefficient_height F I H.bankHeight H.sourceHeight H.bank H.coefficient
      q j r t).trans (Nat.pow_le_pow_right (by decide)
      (budget_le F I H.bankHeight H.sourceHeight H.bank H.coefficient q (H.rank q) (H.sourceWidth q)
        (H.spatialDegree q) (H.nodes q) (H.rank_bound q) (H.width_bound q) (H.degree_bound q)
        (H.leading q) (H.expression_nodes q) (H.expression_coefficients q) (H.scales q)
        (H.slope q) (H.source_le_bank q)))
  have Hdeg : (IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q)
      (F.rule q) (I.coordinate q)).natDegree ≤ coordinateDegree (F.spatial q) (F.rule q) :=
    Polynomial.natDegree_map_le.trans (coordinate_degree _ _ _ _)
  have Hnil := IntegralPrincipalHeightBounds.principal_height
    (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
    (IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q))
    (coordinateDegree (F.spatial q) (F.rule q)) C index.val Hdeg Hcoeff
  have HK : coordinateDegree (F.spatial q) (F.rule q) ≤
      IntegralMixedExceptionalBounds.K (F.ambient q + 1) (H.spatialDegree q) :=
    IntegralCriticalFactorCeiling.dimension_mono (by omega) (H.degree_bound q)
  have Hbudget := IntegralPrincipalHeightBounds.height_mono HK (H.rank_bound q) (Nat.le_refl C)
  by_cases Hk : k < 2 ^ F.width q
  · rw [← IntegralMixedCutNilpotent.coefficient (F.state q) (F.birth_bound q) (F.rule q)
      (.squarefree (I.coordinate q) index) (F.scalar_cap q) ⟨k, Hk⟩ u v]
    have HV := Hnil (pairIndex (F.birth q) (F.width q) (u, ⟨k, Hk⟩))
      (pairIndex (F.birth q) (F.width q) (v, 0))
    rw [IntegralMixedSquarefreeMatrixSource.nilpotent_value]
    rw [PrincipalSubresultant.psc_def] at HV
    convert HV.trans (Nat.pow_le_pow_right (by decide) Hbudget) using 1 <;> rfl
  · rw [IntegralMixedCutNilpotent.coefficient_outside _ _ _ _ (F.scalar_cap q) k (by omega),
      Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

noncomputable def rawBounds (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (H : OriginalBounds F) (index : ∀ q, Fin (coordinateDegree (F.spatial q) (F.rule q)))
    (hkind : ∀ q, F.kind q = .squarefree (I.coordinate q) (index q)) : RawBounds F where
  height q := height (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q)
    (F.cap q) (H.nodes q) (H.bankHeight q)
  bound q k u v := by
    rw [hkind]
    exact coefficient_height F I H q (index q) k u v

theorem rawBounds_height_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (H : OriginalBounds F) (index : ∀ q, Fin (coordinateDegree (F.spatial q) (F.rule q)))
    (hkind : ∀ q, F.kind q = .squarefree (I.coordinate q) (index q))
    (hn : UnaryFn F.ambient) (hM : BinaryFn H.rank) (hW : UnaryFn H.sourceWidth)
    (hD : BinaryFn H.spatialDegree) (hS : BinaryFn F.cap)
    (hL : BinaryFn H.nodes) (hG : BinaryFn H.bankHeight) :
    BinaryFn (rawBounds F I H index hkind).height :=
  height_binary hn hM hW hD hS hL hG

end LeanCanny.Algebra.IntegralMixedSquarefreeHeightBounds
