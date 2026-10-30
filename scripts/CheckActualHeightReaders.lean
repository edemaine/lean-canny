import LeanCanny.Encoding.FlatAffineHeightValues
import LeanCanny.Connectivity.FlatAffineHeightArcs
import LeanCanny.Encoding.FlatAffineHeightTrailing

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

end
end ActualHeightReaderRegression
