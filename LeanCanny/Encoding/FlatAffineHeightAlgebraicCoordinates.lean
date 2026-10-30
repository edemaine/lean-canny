/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialSampleSliceDegree
public import LeanCanny.Encoding.IntegerPolynomialSampleSliceRootCount
public import LeanCanny.Encoding.FlatAffineHeightExceptional
public import LeanCanny.Encoding.FlatAffineHeightOrdinals

/-! # Native coordinate coefficient signs at actual exceptional heights

Original affine records supply both the exceptional-height root labels and
every varying-height coordinate polynomial. Complete sampling retains all
exceptional roots, including repeated heights and singular endpoint fibers.
Their coordinate coefficient signs and actual degrees are native. No
endpoint regularity or specialized coefficient oracle is assumed.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightAlgebraicCoordinates
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def family (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : BoundedAlgebraicSlice.Family where
  polynomial := FlatAffineHeightGrid.indexed F height
  degree := FlatAffineHeightExceptional.degree F
  parameterDegree := FlatAffineHeightExceptional.degree F
  mass := FlatAffineHeightExceptional.exponent F
  polynomial_degree := FlatAffineHeightExceptional.indexed_degree_le F height
  coefficient_degree := FlatAffineHeightExceptional.indexed_inner_le F height
  coefficient_mass := FlatAffineHeightExceptional.indexed_mass_le F height

noncomputable def access {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : (family F height).Access :=
  ⟨FlatAffineHeightGrid.indexedReader h height hh, FlatAffineHeightExceptional.degree_binary h,
    FlatAffineHeightExceptional.degree_binary h, FlatAffineHeightExceptional.exponent_binary h⟩

theorem coefficientSignEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (IntegerPolynomialSampleSlice.coefficientSign (FlatAffineHeightCells.source F hcone height) (family F height)) :=
  IntegerPolynomialSampleSlice.coefficientSignEvaluator (FlatAffineHeightCells.access h hcone height hh) (access h height hh)

theorem degreeEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun u => BinaryNatCode.encode (IntegerPolynomialSampleSlice.specialized
      (FlatAffineHeightCells.source F hcone height) (family F height) u).natDegree) :=
  IntegerPolynomialSampleSlice.degreeEvaluator (FlatAffineHeightCells.access h hcone height hh) (access h height hh)

theorem rootCountEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun u => BinaryNatCode.encode (IntegerPolynomialSampleSlice.RootCount.count
      (FlatAffineHeightCells.source F hcone height) (family F height) u)) :=
  IntegerPolynomialSampleSlice.RootCount.count_evaluator (FlatAffineHeightCells.access h hcone height hh) (access h height hh)

theorem specialized_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (z : List Bool) (t : ℝ) :
    (family F height).slice z t ≠ 0 := by
  change (FlatAffineHeightGrid.indexed F height z).map (ParameterTarski.evalHom t) ≠ 0
  rw [FlatAffineHeightGrid.indexed, FlatAffineHeightGrid.coordinate_comp]
  exact FlatAffineHeightOrdinals.specialized_ne_zero F hcone height (pairFst z) t _

theorem valid_specialized_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    (hu : u ∈ IntegerPolynomialSampleSlice.valid (FlatAffineHeightCells.source F hcone height)) :
    IntegerPolynomialSampleSlice.specialized (FlatAffineHeightCells.source F hcone height) (family F height) u ≠ 0 := by
  rw [IntegerPolynomialSampleSlice.specialized, ite_eq_left hu]
  exact specialized_ne_zero F hcone height _ _

theorem endpoint_label_exists (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height u) = 0) :
    ∃ w, ∃ hw : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineHeightCells.source F hcone height)) u w,
      (SquareSampleCompleteVertices.candidate
        (IntegerPolynomialSampleInput.input (FlatAffineHeightCells.source F hcone height)) u w hw).val (0 : Fin 1) = a :=
  IntegerPolynomialSampleInput.root_complete (FlatAffineHeightCells.source F hcone height) u
    (FlatAffineHeightSlabExceptional.ne_zero F hcone height u) a ha

end LeanCanny.Encoding.FlatAffineHeightAlgebraicCoordinates
