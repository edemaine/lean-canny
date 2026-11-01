/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueDoubleNilpotent
public import LeanCanny.Algebra.IntegralMixedVirtualOriginalRows
public import LeanCanny.Algebra.IntegralMixedSquarefreeMatrixSource
public import LeanCanny.Algebra.RelativeValueSystemMap

/-! # The literal native rows of the double-nilpotent value Gram matrix

The actual matrix uses coordinate polynomials from the virtual critical
source and the full mapped original row. Homogenization, the reciprocal
value equation and the Macaulay construction are preserved by the two
coefficient maps. This identifies the required row-entry arithmetic
without an arbitrary Gram matrix or a polynomial coefficient oracle.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueDoubleSystem
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCoordinateSquarefree
open IntegralMixedCutSource IntegralMixedVirtualSweepSource Polynomial MvPolynomial
open scoped Classical

noncomputable def coordinates (F : Family) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :=
  (IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q) j).toMvPolynomial j

noncomputable def system (F : Family) (q : List Bool)
    (i : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :=
  RelativeValueSystemMap.reciprocal
    (AffineRingCoordinates.homogeneousRows (coordinates F q)
      (fun _ => coordinateDegree (F.spatial q) (F.rule q)))
    (RelativeValueSystemMap.homogeneousTest (IntegralMixedVirtualOriginalRows.row F q i) (F.spatial q).degree)
    (F.spatial q).degree

noncomputable def mappedSystem (F : Family) (q : List Bool)
    (i : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)) :=
  (system F q i j).map (AdjoinRoot.mk (Polynomial.X ^ (2 ^ F.width q)))

theorem first_system (F : Family) (q : List Bool)
    (i : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)) :
    (RelativeProjectiveValueGram.system
      (AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows
        (coordinate (F.state q) (F.birth_bound q) (F.rule q)))
        (fun _ => coordinateDegree (F.spatial q) (F.rule q)))
      (RelativeAffineGridValueGram.test (IntegralMixedSweepRows.row (F.state q) (F.birth_bound q) (F.rule q) i)
        (F.spatial q).degree) (F.spatial q).degree j).map
          (Polynomial.mapRingHom (AdjoinRoot.mk (Polynomial.X ^ (2 ^ F.width q)))) = system F q i j := by
  rw [RelativeValueSystemMap.existing_system]
  unfold system
  congr 1
  · funext k
    rw [RelativeValueSystemMap.homogeneous]
    have HR : (fun k => (RelativeAffineGridValueGram.rows
        (coordinate (F.state q) (F.birth_bound q) (F.rule q)) k).map
          (AdjoinRoot.mk (Polynomial.X ^ (2 ^ F.width q)))) = coordinates F q := by
      funext k
      rw [RelativeAffineGridValueGram.rows, RelativeValueSystemMap.coordinate]
      rfl
    rw [HR]
  · change (RelativeValueSystemMap.homogeneousTest _ _).map _ = _
    rw [RelativeValueSystemMap.test]
    rfl

theorem matrix_eq (F : Family) (q : List Bool)
    (i : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :
    IntegralMixedValueDoubleNilpotent.matrix (F.state q) (F.birth_bound q) (F.rule q) i =
      ProjectiveGramEliminant.gram (MacaulayFullBox.matrix (mappedSystem F q i)
        (RelativeProjectiveValueGram.degrees
          (fun _ => coordinateDegree (F.spatial q) (F.rule q)) (F.spatial q).degree)
        (IntegralMixedGridValue.width (F.spatial q) (F.rule q))) := by
  unfold IntegralMixedValueDoubleNilpotent.matrix IntegralMixedValueMatrixSource.nilpotentMatrix
    IntegralMixedValueMatrixSource.matrix
  rw [ProjectiveGramEliminant.gram_map, MacaulayFullBox.matrix_map,
    ProjectiveGramEliminant.gram_map, MacaulayFullBox.matrix_map]
  congr 1
  congr 1
  funext j
  rw [first_system]
  rfl

end LeanCanny.Algebra.IntegralMixedValueDoubleSystem
