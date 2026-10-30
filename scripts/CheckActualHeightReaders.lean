import LeanCanny.Encoding.FlatAffineHeightValues
import LeanCanny.Connectivity.FlatAffineHeightArcs
import LeanCanny.Encoding.FlatAffineHeightTrailing
import LeanCanny.Encoding.FlatAffineHeightSlabExceptional
import LeanCanny.Encoding.FlatAffineHeightCells
import LeanCanny.Encoding.FlatAffineHeightOrdinals

/-! Actual-source integration, including the depth-zero affine power tower.
Run with `lake env lean -DwarningAsError=true scripts/CheckActualHeightReaders.lean`.
-/

open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open scoped Classical

namespace ActualHeightReaderRegression
noncomputable section

private def F : Inputs where
  source := ⟨fun _ => [], fun _ => 0, fun _ => 1⟩
  depth _ := 0
  width _ := 0
  direction _ := []
  level _ := []

private lemma access : F.Access := by
  refine ⟨⟨constFn_mem_FP [], UnaryFn.const 0, BinaryFn.const 1⟩,
    UnaryFn.const 0, UnaryFn.const 0, SpaceFunction.ofFP _ (constFn_mem_FP []),
    SpaceFunction.ofFP _ (constFn_mem_FP []), ?_⟩
  intro u
  change (ETR.TermView.term []).arity ≤ 0
  decide

private def selected (u : List Bool) : Fin (FlatAffineFullSourcePositive.count F u) :=
  ⟨0, FlatAffineFullSourcePositive.count_pos F u⟩

private lemma selected_unary : UnaryFn (fun u => (selected u).val) := UnaryFn.const 0

private lemma cone : FlatAffinePowerPositive.ConeCertificate F := by
  intro u t
  exact Fin.elim0 t

-- Every coordinate is supplied from the actual original row program; invalid
-- indices are guarded internally. No coordinate modular reader is a premise.
example : SpaceFunction (SymbolicFixedTableEntryBits.coefficient
    (DiagonalParameterBits.selected (FlatAffineFullSourcePositive.count F)
      (FlatAffineHeightGrid.coordinate F selected))) :=
  FlatAffineHeightGrid.coefficientEvaluator access selected selected_unary

-- The value reader also constructs the selected test, both homogenizations,
-- and both reciprocal Gram determinants from that same source access.
example : CertifiedPolynomial.BivariateReader
    (FlatAffineHeightValues.family F selected selected).affine.homogeneous.annihilator :=
  FlatAffineHeightValues.reader access selected selected selected_unary selected_unary

-- The depth-zero dummy is retained: the cone condition is vacuous, while the
-- actual coordinate and value certificates are nonzero.
example : (FlatAffineHeightGrid.coordinate F selected [] (selected [])).natDegree =
    FlatAffineHeightValues.coordinateDegree F [] :=
  FlatAffineHeightValues.coordinate_degree_eq F cone selected [] (selected [])

example : (FlatAffineHeightValues.family F selected selected).affine.homogeneous.annihilator [] ≠ 0 :=
  FlatAffineHeightValues.ne_zero F cone selected selected []

-- The arc construction uses the same computed value certificates.
example : Connectivity.FlatAffineHeightArcs.exceptional F selected [] ≠ 0 :=
  Connectivity.FlatAffineHeightArcs.exceptional_ne_zero F cone selected []

example : {t : ℝ | SymbolicScaledSquarefree.scalarEvaluation t
    (Connectivity.FlatAffineHeightArcs.exceptional F selected []) = 0}.Finite :=
  Connectivity.FlatAffineHeightArcs.finite_exceptional F cone selected []

-- Degree and integer-height budgets are computed from the actual source.
example : BinaryFn (FlatAffineHeightValueBounds.heightBound F selected) :=
  FlatAffineHeightValueBounds.heightBound_binary access selected selected selected_unary

-- The lowest coefficient and its parameter polynomial are computed internally.
example : SpaceFunction (PolynomialTrailingCoefficientBits.index
    (FlatAffineHeightTrailing.polynomial F selected selected)) :=
  FlatAffineHeightTrailing.indexEvaluator access selected selected selected_unary selected_unary

example : SpaceFunction (PrimitivePairBits.coefficient (fun u =>
    (FlatAffineHeightTrailing.polynomial F selected selected u).trailingCoeff)) :=
  FlatAffineHeightTrailing.coefficientEvaluator access selected selected selected_unary selected_unary

example : (FlatAffineHeightTrailing.polynomial F selected selected []).trailingCoeff ≠ 0 :=
  FlatAffineHeightTrailing.trailing_ne_zero F cone selected selected []

-- Every nonzero principal factor is computed in space; the selected GCD
-- order is never an assumed FP metadata routine.
example : SpaceFunction (PrimitivePairBits.coefficient (FlatAffineHeightSlabExceptional.polynomial F selected)) :=
  FlatAffineHeightSlabExceptional.evaluator access selected selected_unary

example : FlatAffineHeightSlabExceptional.polynomial F selected [] ≠ 0 :=
  FlatAffineHeightSlabExceptional.ne_zero F cone selected []

example : BinaryFn (FlatAffineHeightSlabExceptional.degreeBound F) :=
  FlatAffineHeightSlabExceptional.degreeBound_binary access selected

example : BinaryFn (FlatAffineHeightSlabExceptional.massBound F) :=
  FlatAffineHeightSlabExceptional.massBound_binary access selected

example (t : ℝ) (ht : SymbolicScaledSquarefree.scalarEvaluation t
    (FlatAffineHeightSlabExceptional.polynomial F selected []) ≠ 0) :
    SymbolicScaledSquarefree.scalarEvaluation t (Connectivity.FlatAffineHeightArcs.exceptional F selected []) ≠ 0 :=
  FlatAffineHeightSlabExceptional.avoids (SymbolicScaledSquarefree.scalarEvaluation t) F cone selected [] ht

example : SpaceFunction (fun u => BinaryNatCode.encode (FlatAffineHeightCells.roots F cone selected u).card) :=
  FlatAffineHeightCells.countEvaluator access cone selected selected_unary

example : SpaceFunction (fun q => BinaryNatCode.encode
    (IntegerPolynomialRootQueriesBits.cellCode (FlatAffineHeightCells.source F cone selected) q)) :=
  FlatAffineHeightCells.cellEvaluator access cone selected selected_unary

example : IntegerPolynomialRootQueriesBits.cellLanguage (FlatAffineHeightCells.source F cone selected) ∈ PSPACE :=
  FlatAffineHeightCells.cell_mem_PSPACE access cone selected selected_unary

example : UnaryFn (IntegerPolynomialRootQueriesBits.labelWidth (FlatAffineHeightCells.source F cone selected)) :=
  IntegerPolynomialRootQueriesBits.labelWidth_unary (FlatAffineHeightCells.access access cone selected selected_unary)

-- Short coordinate records distinguish every original endpoint root, even
-- when that endpoint is exceptional and its fiber is singular.
example : UnaryFn (fun u => FlatAffineFullSourcePositive.count F u * FlatAffineHeightOrdinals.width F u) :=
  FlatAffineHeightOrdinals.length_unary access

example (t : ℝ) : Function.Injective (fun x : Connectivity.PolynomialGridArcs.Fiber
    (Connectivity.IntegerGridArcs.realRows (Connectivity.FlatAffineHeightArcs.rows F selected [])) t =>
      FlatAffineHeightOrdinals.word F selected [] t x.val) :=
  FlatAffineHeightOrdinals.fiber_word_injective F cone selected [] t

end
end ActualHeightReaderRegression
