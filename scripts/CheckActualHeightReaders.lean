import LeanCanny.Encoding.FlatAffineHeightValues
import LeanCanny.Connectivity.FlatAffineHeightArcs
import LeanCanny.Encoding.FlatAffineHeightTrailing
import LeanCanny.Encoding.FlatAffineHeightSlabExceptional
import LeanCanny.Encoding.FlatAffineHeightCells
import LeanCanny.Encoding.FlatAffineHeightOrdinals
import LeanCanny.Encoding.FlatAffineEndpointRows
import LeanCanny.Algebra.FrozenAffineMidpointSpace
import LeanCanny.Encoding.FlatAffineEndpointGram
import LeanCanny.Encoding.FlatAffineEndpointGrid
import LeanCanny.Encoding.FlatAffineEndpointTrailing
import LeanCanny.Encoding.FlatAffineEndpointValidity
import LeanCanny.Encoding.FlatAffineEndpointCells
import LeanCanny.Encoding.FlatAffineEndpointSamples
import LeanCanny.Encoding.FlatAffineHeightAlgebraicCoordinates
import LeanCanny.Encoding.FlatAffineEndpointAdjacentComplete
import LeanCanny.Encoding.FlatAffineEndpointFiniteMidpoint
import LeanCanny.Encoding.FlatAffineEndpointFiniteMatching
import LeanCanny.Encoding.FlatAffineEndpointFiniteEdges
import LeanCanny.Encoding.FlatAffineEndpointRankWord
import LeanCanny.Encoding.FlatAffineEndpointFiniteRankBranch
import LeanCanny.Encoding.FlatAffineEndpointBranchRelation
import LeanCanny.Connectivity.FlatAffineEndpointMarkerIncidence
import LeanCanny.Encoding.FlatAffineEndpointAlgebraicMarker

/-! Actual-source integration, including the depth-zero affine power tower.
Run with `lake env lean -DwarningAsError=true scripts/CheckActualHeightReaders.lean`.
-/

open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open scoped Classical

namespace ActualHeightReaderRegression
noncomputable section
set_option backward.isDefEq.respectTransparency false

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

example : SpaceFunction (FlatAffineEndpointPreparation.record F selected) :=
  FlatAffineEndpointPreparation.recordEvaluator access cone selected selected_unary

private def lastCopy (r : List Bool) : Fin (FlatAffineEndpointRows.arity F r) :=
  Fin.last (3 * FlatAffineEndpointRows.originalCount F r)

private lemma lastCopy_unary : UnaryFn (fun r => (lastCopy r).val) :=
  (UnaryFn.const 3).mul (FlatAffineEndpointRows.originalCount_unary access)

-- The source internally supplies the retained equation, the embedded tower
-- row, and the frozen-height subtraction. All raw exponent/modulus words work.
example : SpaceFunction (FixedWidthRowBits.value (FlatAffineEndpointRows.arity F) (fun _ => 2)
    (fun r => FlatAffineEndpointPreparation.system F selected r (lastCopy r)) pairSnd pairFst) :=
  FlatAffineEndpointRows.evaluator access selected selected_unary lastCopy lastCopy_unary (UnaryFn.const 2)
    pairSnd_mem_FP pairFst_mem_FP

example (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
    (FlatAffineHeightSlabExceptional.polynomial F selected []) = 0) :
    AffineFiniteCoordinates.NoInfinity
      (FlatAffineEndpointPreparation.system F selected (FlatAffineEndpointPreparation.record F selected []))
      (FlatAffineEndpointPreparation.degrees F (FlatAffineEndpointPreparation.record F selected [])) :=
  FlatAffineEndpointPreparation.noInfinity_record F cone selected [] a ha

example : SpaceFunction (FixedWidthRowBits.value (fun u => 3 * FlatAffineFullSourcePositive.count F u + 1)
    (fun _ => 2) (fun u => FrozenAffineCopies.midpoint (selected u)) pairSnd pairFst) :=
  FrozenAffineMidpointBits.evaluator (FlatAffineFullSourcePositive.count_unary access) (UnaryFn.const 2)
    selected selected_unary pairSnd_mem_FP pairFst_mem_FP

example : CertifiedPolynomial.BivariateReader (fun r => Geometry.AffineShiftCoordinates.coordinate
    (FlatAffineEndpointPreparation.system F selected r)
    (fun i => if i = FlatAffineEndpointGram.active F selected r then Polynomial.X else 0)
    (FlatAffineEndpointPreparation.degrees F r) (FlatAffineEndpointRows.zero F r)) :=
  FlatAffineEndpointGram.reader (F := F) access selected (FlatAffineEndpointRows.zero F) selected_unary
    (show UnaryFn (fun r => (FlatAffineEndpointRows.zero F r).val) from UnaryFn.const 0)

example : SpaceFunction (SymbolicFixedTableEntryBits.coefficient
    (DiagonalParameterBits.selected (FlatAffineEndpointRows.arity F) (FlatAffineEndpointGrid.coordinate F selected))) :=
  FlatAffineEndpointGrid.coefficientEvaluator (F := F) access selected selected_unary

private def midpointIndex (r : List Bool) : Fin (FlatAffineFullSourcePositive.count F (pairFst r)) := selected (pairFst r)
private lemma midpointIndex_unary : UnaryFn (fun r => (midpointIndex r).val) := selected_unary.comp pairFst_mem_FP

example : CertifiedPolynomial.BivariateReader (FlatAffineEndpointValues.family F selected midpointIndex).affine.homogeneous.annihilator :=
  FlatAffineEndpointValues.reader access selected selected_unary midpointIndex midpointIndex_unary

example : BinaryFn (FlatAffineEndpointValueBounds.heightBound F) :=
  FlatAffineEndpointValueBounds.heightBound_binary access selected midpointIndex

example : SpaceFunction (PrimitivePairBits.coefficient
    (fun r => (FlatAffineEndpointTrailing.polynomial F selected midpointIndex r).trailingCoeff)) :=
  FlatAffineEndpointTrailing.coefficientEvaluator access selected selected_unary midpointIndex midpointIndex_unary

example (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F selected []) = 0) :
    (FlatAffineEndpointTrailing.polynomial F selected midpointIndex (FlatAffineEndpointPreparation.record F selected [])).trailingCoeff ≠ 0 :=
  FlatAffineEndpointTrailing.ne_zero F cone selected midpointIndex [] a ha

example : SpaceDecider {r | FlatAffineEndpointValidity.Valid F selected r} :=
  FlatAffineEndpointValidity.decider access cone selected selected_unary

example (u : List Bool) : FlatAffineEndpointValidity.Valid F selected (FlatAffineEndpointPreparation.record F selected u) :=
  FlatAffineEndpointValidity.record_valid F selected u

-- One streamed product stabilizes every midpoint comparison while retaining
-- every original endpoint height. No endpoint coordinates are runtime oracles.
example : SpaceFunction (PrimitivePairBits.coefficient (FlatAffineEndpointExceptional.polynomial F selected)) :=
  FlatAffineEndpointExceptional.evaluator access selected selected_unary

example : BinaryFn (FlatAffineEndpointExceptional.degreeBound F) :=
  FlatAffineEndpointExceptional.degreeBound_binary access selected

example : BinaryFn (FlatAffineEndpointExceptional.massBound F) :=
  FlatAffineEndpointExceptional.massBound_binary access selected

example : SpaceFunction (fun r => BinaryNatCode.encode (FlatAffineEndpointCells.roots F cone selected r).card) :=
  FlatAffineEndpointCells.countEvaluator access cone selected selected_unary

example : IntegerPolynomialRootQueriesBits.cellLanguage (FlatAffineEndpointCells.source F cone selected) ∈ PSPACE :=
  FlatAffineEndpointCells.cell_mem_PSPACE access cone selected selected_unary

example (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F selected r) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F selected (pairFst r)) = 0) :
    a ∈ FlatAffineEndpointCells.roots F cone selected r :=
  FlatAffineEndpointCells.endpoint_mem F cone selected r hr a ha

-- Algebraic candidates use source-derived derivative coefficients. Their
-- native labels retain repeated roots and require no isolating rationals.
example : SpaceFunction (fun r => BinaryNatCode.encode (FlatAffineEndpointSamples.roots F cone selected r).card) :=
  FlatAffineEndpointSamples.countEvaluator access cone selected selected_unary

example : UnaryFn (SquareSampleCompleteVertices.width (FlatAffineEndpointSamples.input F cone selected)) :=
  FlatAffineEndpointSamples.vertexWidth_unary access cone selected selected_unary

example : SquareSampleCompleteVertices.language (FlatAffineEndpointSamples.input F cone selected) ∈ PSPACE :=
  FlatAffineEndpointSamples.vertex_mem_PSPACE access cone selected selected_unary

example : SquareSampleCompletePolynomialTest.language (FlatAffineEndpointSamples.input F cone selected)
    (IntegerPolynomialSampleInput.test (FlatAffineEndpointSamples.source F cone selected)
      (FlatAffineEndpointCells.source F cone selected)) .pos ∈ PSPACE :=
  IntegerPolynomialSampleInput.sign_mem_PSPACE (FlatAffineEndpointSamples.access access cone selected selected_unary)
    (FlatAffineEndpointCells.access access cone selected selected_unary) .pos

-- The original source supplies signs and actual degrees after specializing
-- any coordinate at a labeled exceptional height, including singular ones.
example : SpaceFunction (IntegerPolynomialSampleSlice.coefficientSign
    (FlatAffineHeightCells.source F cone selected) (FlatAffineHeightAlgebraicCoordinates.family F selected)) :=
  FlatAffineHeightAlgebraicCoordinates.coefficientSignEvaluator access cone selected selected_unary

example : SpaceFunction (fun u => BinaryNatCode.encode (IntegerPolynomialSampleSlice.specialized
    (FlatAffineHeightCells.source F cone selected) (FlatAffineHeightAlgebraicCoordinates.family F selected) u).natDegree) :=
  FlatAffineHeightAlgebraicCoordinates.degreeEvaluator access cone selected selected_unary

example (u : List Bool) (a : ℝ) : (FlatAffineHeightAlgebraicCoordinates.family F selected).slice u a ≠ 0 :=
  FlatAffineHeightAlgebraicCoordinates.specialized_ne_zero F cone selected u a

example : SpaceFunction (fun u => BinaryNatCode.encode (IntegerPolynomialSampleSlice.RootCount.count
    (FlatAffineHeightCells.source F cone selected) (FlatAffineHeightAlgebraicCoordinates.family F selected) u)) :=
  FlatAffineHeightAlgebraicCoordinates.rootCountEvaluator access cone selected selected_unary

-- The source computes both algebraic cuts, checks both complete labels,
-- and validates the prepared degree record for either adjacent side.
example (right : Bool) : FlatAffineEndpointAdjacentSamples.language F cone selected right ∈ PSPACE :=
  FlatAffineEndpointAdjacentSamples.mem_PSPACE access cone selected selected_unary right

-- A joint frame retains both algebraic heights and all three spatial copies.
-- Native validity and signs include singular tuples and reject bad records.
example : SpaceFunction (FlatAffineEndpointFiniteFrame.record F selected) :=
  FlatAffineEndpointFiniteFrame.recordEvaluator access cone selected selected_unary

example : SpaceDecider {s | FlatAffineEndpointFiniteFrame.Valid F selected s} :=
  FlatAffineEndpointFiniteFrame.validDecider access cone selected selected_unary

example : GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone selected) ∈ PSPACE :=
  FlatAffineEndpointFiniteSample.mem_PSPACE access cone selected selected_unary

example : UnaryFn (SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone selected)) :=
  FlatAffineEndpointFiniteSample.width_unary access cone selected selected_unary

private def jointIndex (s : List Bool) : Fin (FlatAffineFullSourcePositive.count F (pairFst (pairFst s))) :=
  selected (pairFst (pairFst s))

private lemma jointIndex_unary : UnaryFn (fun s => (jointIndex s).val) :=
  selected_unary.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)

example (sigma : SignType) : FlatAffineEndpointFiniteMidpoint.language F cone selected jointIndex sigma ∈ PSPACE :=
  FlatAffineEndpointFiniteMidpoint.mem_PSPACE access cone selected selected_unary jointIndex jointIndex_unary sigma

-- Both height coordinates and the chosen spatial projections are compared
-- by streamed Thom signs; a universal scan checks every endpoint candidate.
example : SquareSampleCompleteCoordinateEquality.language (FlatAffineEndpointFiniteSample.input F cone selected) ∈ PSPACE :=
  SquareSampleCompleteCoordinateEquality.mem_PSPACE (FlatAffineEndpointFiniteSample.sampleAccess access cone selected selected_unary)

example : FlatAffineEndpointFiniteMatching.language F cone selected ∈ PSPACE :=
  FlatAffineEndpointFiniteMatching.mem_PSPACE access cone selected selected_unary

example : FlatAffineEndpointFiniteHeights.endpointLanguage F cone selected ∈ PSPACE :=
  FlatAffineEndpointFiniteHeights.endpoint_mem_PSPACE access cone selected selected_unary

example : FlatAffineEndpointFiniteHeights.sampleLanguage F cone selected ∈ PSPACE :=
  FlatAffineEndpointFiniteHeights.sample_mem_PSPACE access cone selected selected_unary

example (right : Bool) : FlatAffineEndpointFiniteAdjacent.language F cone selected right ∈ PSPACE :=
  FlatAffineEndpointFiniteAdjacent.mem_PSPACE access cone selected selected_unary right

example (right : Bool) : FlatAffineEndpointFiniteEdges.language F cone selected right ∈ PSPACE :=
  FlatAffineEndpointFiniteEdges.mem_PSPACE access cone selected selected_unary right

private def rankIndex (c : List Bool) : Fin (FlatAffineEndpointFiniteSide.originalCount F (FlatAffineEndpointFiniteRanks.frame c)) :=
  jointIndex (FlatAffineEndpointFiniteRanks.frame c)

private lemma rankIndex_unary : UnaryFn (fun c => (rankIndex c).val) :=
  jointIndex_unary.comp FlatAffineEndpointFiniteRanks.frame_FP

example : SpaceFunction (fun q => BinaryNatCode.encode
    (FiniteWordProjectionRank.rank (FlatAffineEndpointFiniteRanks.data F cone selected rankIndex) q)) :=
  FlatAffineEndpointFiniteRanks.evaluator access cone selected selected_unary rankIndex rankIndex_unary

example : SpaceFunction (FlatAffineEndpointRankWord.word F cone selected) :=
  FlatAffineEndpointRankWord.evaluator access cone selected selected_unary

example : UnaryFn (fun b => FlatAffineEndpointRankWord.arity F b * FlatAffineEndpointRankWord.width F cone selected b) :=
  FlatAffineEndpointRankWord.length_unary access cone selected selected_unary

example : FlatAffineEndpointRankWordEquality.language F cone selected ∈ PSPACE :=
  FlatAffineEndpointRankWordEquality.mem_PSPACE access cone selected selected_unary

example : FlatAffineEndpointSampleSlab.language F cone selected ∈ PSPACE :=
  FlatAffineEndpointSampleSlab.mem_PSPACE access cone selected selected_unary

example : FlatAffineEndpointBranchLabels.language F cone selected ∈ PSPACE :=
  FlatAffineEndpointBranchLabels.mem_PSPACE access cone selected selected_unary

example : LeanCanny.Encoding.FlatAffineEndpointBranchRelation.language F cone selected ∈ PSPACE :=
  LeanCanny.Encoding.FlatAffineEndpointBranchRelation.mem_PSPACE access cone selected selected_unary

-- Endpoint markers retain an actual point even at a singular endpoint.
-- Auxiliary joint copies may differ; only the designated point is compared.
example (k : Fin 3) : FlatAffineEndpointCopyEquality.language F cone selected k ∈ PSPACE :=
  FlatAffineEndpointCopyEquality.mem_PSPACE access cone selected selected_unary k

example : FlatAffineEndpointMarkers.language F cone selected ∈ PSPACE :=
  FlatAffineEndpointMarkers.mem_PSPACE access cone selected selected_unary

example : FlatAffineEndpointMarkerEquality.language F cone selected ∈ PSPACE :=
  FlatAffineEndpointMarkerEquality.mem_PSPACE access cone selected selected_unary

example (right : Bool) : FlatAffineEndpointIncidenceQuery.language F cone selected right ∈ PSPACE :=
  FlatAffineEndpointIncidenceQuery.mem_PSPACE access cone selected selected_unary right

example : SpaceFunction (FlatAffineEndpointAlgebraicMarker.record F cone selected) :=
  FlatAffineEndpointAlgebraicMarker.recordEvaluator access cone selected selected_unary

example : SquareSampleCompleteParameterEquality.language (FlatAffineEndpointFiniteSample.input F cone selected) ∈ PSPACE :=
  SquareSampleCompleteParameterEquality.mem_PSPACE (FlatAffineEndpointFiniteSample.sampleAccess access cone selected selected_unary)

example (Q : BoundedAlgebraicSlice.Family) (A : Q.Access) :
    SpaceFunction (SquareSampleCompleteParameterSlice.coefficientSign (FlatAffineEndpointFiniteSample.input F cone selected) Q) :=
  SquareSampleCompleteParameterSlice.coefficientSignEvaluator (FlatAffineEndpointFiniteSample.sampleAccess access cone selected selected_unary) A

end
end ActualHeightReaderRegression
