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
import LeanCanny.Encoding.FlatAffineEndpointChildSamples
import LeanCanny.Encoding.FlatAffineEndpointMarkerComplete
import LeanCanny.Encoding.FlatAffineEndpointParentComplete
import LeanCanny.Connectivity.FlatAffineEndpointDescriptorIncidence
import LeanCanny.Encoding.FlatAffineSlabGraphAlgorithms
import LeanCanny.Encoding.FlatAffineSlabGraphEdges
import LeanCanny.Encoding.FlatAffineEndpointBranchLabelComplete
import LeanCanny.Connectivity.FlatAffineSlabGraphBranchLabels
import LeanCanny.Connectivity.FlatAffineSlabConnectivity
import LeanCanny.Connectivity.FlatAffineGapConnectivity
import LeanCanny.Connectivity.FlatAffineSlabBranchParents
import LeanCanny.Connectivity.FlatAffineSlabCoordinateSignReader
import LeanCanny.Encoding.FlatAffineSingularSliceSamples
import LeanCanny.Encoding.FlatAffineSingularChildLabels
import LeanCanny.Connectivity.CoordinateAffineComponentCover
import LeanCanny.Encoding.CoordinateAffineSliceRegularity
import LeanCanny.Encoding.FlatAffineSingularSliceChoice
import LeanCanny.Connectivity.CoordinateAffineTerminalReachability
import LeanCanny.Connectivity.CoordinateAffineTerminalConnectivity
import LeanCanny.Connectivity.FlatAffineSlabFrozenPrefixes
import LeanCanny.Connectivity.FlatAffineSlabPrefixLabels
import LeanCanny.Connectivity.FlatAffineSlabSliceRegularity
import LeanCanny.Connectivity.FlatAffineSlabComponentSampling
import LeanCanny.Connectivity.FlatAffineSlabParentBranches
import LeanCanny.Connectivity.FlatAffineSlabParentSections
import LeanCanny.Connectivity.FlatAffineSlabSaturation
import LeanCanny.Connectivity.FlatAffineSlabAncestorFilter
import LeanCanny.Encoding.FlatAffineLastHeightRow
import LeanCanny.Encoding.FlatAffineBranchOriginalAncestorMatch
import LeanCanny.Connectivity.FlatAffineSlabComputedParents
import LeanCanny.Connectivity.FlatAffineSlabEndpointPrefixes
import LeanCanny.Connectivity.FlatAffineScaledSlabSliceRegularity
import LeanCanny.Connectivity.CoordinateDoubleAffineComponentCover
import LeanCanny.Encoding.CoordinateDoubleAffineSliceRegularity

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

example : NamedRationalParents.Access (FlatAffineEndpointNamedParents.source F cone selected) :=
  FlatAffineEndpointNamedParents.access access cone selected selected_unary

example (C : FlatAffineEndpointChildSamples.Controls) (A : C.Access) :
    NamedParentChildSelection.language (FlatAffineEndpointChildSamples.inputs F cone selected C) ∈ PSPACE :=
  FlatAffineEndpointChildSamples.mem_PSPACE access cone selected selected_unary A

example (C : FlatAffineEndpointChildSamples.Controls) (A : C.Access) :
    NamedRationalParents.Access (NamedParentChildNext.next (FlatAffineEndpointChildSamples.inputs F cone selected C)) :=
  FlatAffineEndpointChildSamples.nextAccess access cone selected selected_unary A

-- The concrete bit graph charges its own native validity, equality, and
-- attachment queries, including all searches performed inside them.
example : UnaryFn (FlatAffineSlabGraphCodes.width F cone selected) :=
  FlatAffineSlabGraphCodes.width_unary access cone selected selected_unary

example : FlatAffineSlabGraph.validLanguage F cone selected ∈ PSPACE :=
  FlatAffineSlabGraph.valid_mem_PSPACE access cone selected selected_unary

example : FlatAffineSlabGraph.edgeLanguage F cone selected ∈ PSPACE :=
  FlatAffineSlabGraph.edge_mem_PSPACE access cone selected selected_unary

example : FlatAffineSlabGraph.connectedLanguage F cone selected ∈ PSPACE :=
  FlatAffineSlabGraph.connected_mem_PSPACE access cone selected selected_unary

-- Context validity uses scalar labels only, including empty interior fibers.
example : FlatAffineSlabGraphContext.language F cone selected ∈ PSPACE :=
  FlatAffineSlabGraphContext.mem_PSPACE access cone selected selected_unary

-- The original source supplies complete curves and checked joint references;
-- no spatial branch family or reference table is assumed.
example (c : List Bool) (hc : c ∈ FlatAffineSlabGraphContext.language F cone selected) :
    Finite (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.Index F cone selected c) ∧
      Nonempty (LeanCanny.Connectivity.FlatAffineSlabGraphBranches.Family F cone selected c) :=
  LeanCanny.Connectivity.FlatAffineSlabGraphBranches.exists_family F cone selected c hc

-- This language concerns the actual closed root slab, with its cover and all
-- graph queries constructed from the original source, rather than supplied.
example : LeanCanny.Connectivity.FlatAffineSlabConnectivity.language F cone selected ∈ PSPACE :=
  LeanCanny.Connectivity.FlatAffineSlabConnectivity.mem_PSPACE access cone selected selected_unary

example (c : List Bool) (hc : c ∈ FlatAffineSlabGraphContext.language F cone selected) :
    IsPreconnected (Set.univ : Set (LeanCanny.Connectivity.FlatAffineSlabGraphBranches.Space F cone selected c)) ↔
      c ∈ FlatAffineSlabGraph.connectedLanguage F cone selected :=
  LeanCanny.Connectivity.FlatAffineSlabConnectivity.connected_iff F cone selected c hc

-- Endpoint and sample labels are computed from the frame and gap index.
example : UnaryFn (FlatAffineSlabGraphContextChoice.width F cone selected) :=
  FlatAffineSlabGraphContextChoice.width_unary access cone selected selected_unary

example : SpaceFunction (FlatAffineSlabGraphContextChoice.value F cone selected) :=
  FlatAffineSlabGraphContextChoice.evaluator access cone selected selected_unary

example : LeanCanny.Connectivity.FlatAffineGapConnectivity.language F cone selected ∈ PSPACE :=
  LeanCanny.Connectivity.FlatAffineGapConnectivity.mem_PSPACE access cone selected selected_unary

example (s : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F selected s)
    (k : Fin ((FlatAffineEndpointSampleSlab.roots F cone selected s).card + 1))
    (h0 : 0 < k.val) (hk : k.val < (FlatAffineEndpointSampleSlab.roots F cone selected s).card) :
    pair s (BinaryNatCode.encode k.val) ∈ LeanCanny.Connectivity.FlatAffineGapConnectivity.language F cone selected ↔
      IsPreconnected (LeanCanny.Connectivity.FlatAffineGapConnectivity.solutionSetAt F cone selected s (BinaryNatCode.encode k.val)) :=
  LeanCanny.Connectivity.FlatAffineGapConnectivity.bounded_gap_correct F cone selected s hs k h0 hk

-- Interior branch descriptors also compute actual rational parent names for
-- recursive sample-fiber queries, with native ancestry-aware child routines.
example : NamedRationalParents.Access (FlatAffineCurrentNamedParents.source F cone selected) :=
  FlatAffineCurrentNamedParents.access access cone selected selected_unary

example : SpaceFunction (FlatAffineBranchChoice.value F cone selected) :=
  FlatAffineBranchChoice.evaluator access cone selected selected_unary

example : SpaceFunction (FlatAffineBranchChoice.parentRecord F cone selected) :=
  FlatAffineBranchChoice.parentEvaluator access cone selected selected_unary

example (C : FlatAffineEndpointChildSamples.Controls) (A : C.Access) :
    NamedParentChildSelection.language (FlatAffineBranchChildSamples.inputs F cone selected C) ∈ PSPACE :=
  FlatAffineBranchChildSamples.mem_PSPACE access cone selected selected_unary A

example (C : FlatAffineEndpointChildSamples.Controls) (A : C.Access) :
    NamedRationalParents.Access (NamedParentChildNext.next (FlatAffineBranchChildSamples.inputs F cone selected C)) :=
  FlatAffineBranchChildSamples.nextAccess access cone selected selected_unary A

-- The source computes the coordinate-zero exceptional factors and reads
-- actual coordinate signs from complete labels and short branch descriptors.
example : SpaceFunction (PrimitivePairBits.coefficient (FlatAffineHeightCoordinateTrailing.polynomial F selected)) :=
  FlatAffineHeightCoordinateTrailing.evaluator access selected selected_unary

example : BinaryFn (FlatAffineHeightCoordinateTrailing.degreeBound F) :=
  FlatAffineHeightCoordinateTrailing.degreeBound_binary access

example : SpaceFunction (SquareSampleCompleteCoordinateSign.value (FlatAffineEndpointFiniteSample.input F cone selected)) :=
  SquareSampleCompleteCoordinateSign.evaluator (FlatAffineEndpointFiniteSample.sampleAccess access cone selected selected_unary)

example : SpaceFunction (FlatAffineBranchCoordinateSign.value F cone selected) :=
  FlatAffineBranchCoordinateSign.evaluator access cone selected selected_unary

example (sigma : SignType) : FlatAffineBranchCoordinateSign.language F cone selected sigma ∈ PSPACE :=
  FlatAffineBranchCoordinateSign.mem_PSPACE access cone selected selected_unary sigma

-- Complete ancestry is computed from the actual source, including the
-- zero-depth seed. Next-stage tests retain singular children as well.
example : SpaceFunction (FlatAffinePowerPrefix.value F cone F.depth (fun u => Nat.le_refl (F.depth u))) :=
  FlatAffinePowerPrefix.evaluator access cone access.depth (fun u => Nat.le_refl (F.depth u))

example (C : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next F)) :
    FlatAffineCompleteChildLabels.language F C ∈ PSPACE :=
  FlatAffineCompleteChildLabels.mem_PSPACE access C

example (C : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next F)) :
    FlatAffineSingularChildLabels.language F C ∈ PSPACE :=
  FlatAffineSingularChildLabels.mem_PSPACE access C

example (u w : List Bool) (hw : FlatAffineCompleteVertices.Valid F cone u w) :
    FlatAffineCompleteVertices.vertexEquiv (FlatAffineCompleteRootStages.truncate F F.depth)
      (FlatAffineCompleteRootStages.cone_prefix F cone F.depth (fun u => Nat.le_refl (F.depth u))) u
      ⟨FlatAffinePowerPrefix.value F cone F.depth (fun u => Nat.le_refl (F.depth u)) (pair u w),
        FlatAffinePowerPrefix.value_valid F cone F.depth (fun u => Nat.le_refl (F.depth u)) u w hw⟩ =
    FlatAffineCompleteRootStages.project F F.depth u (Nat.le_refl (F.depth u))
      (FlatAffineCompleteVertices.vertexEquiv F cone u ⟨w, hw⟩) :=
  FlatAffineAncestorLabels.value_original F cone F.depth (fun u => Nat.le_refl (F.depth u)) u w hw

-- The original generated source supplies compactness at every actual parent.
example (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u) :
    IsCompact (FlatAffineCompleteComponentSamples.slice F u x) :=
  FlatAffineSliceCompact.compact F u x

-- Coordinate-prefix cover labels have native validity and widths from the
-- actual source alone; no compactness or normal-independence oracle is passed.
example : FlatAffineCompleteChildLabels.language
    (CoordinateAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => []))
    (LeanCanny.Connectivity.CoordinateAffineComponentCover.cone F.source F.depth (fun _ => 100) (fun _ => [])) ∈ PSPACE :=
  LeanCanny.Connectivity.CoordinateAffineComponentCover.valid_mem_PSPACE F.source F.depth (fun _ => 100) (fun _ => [])
    access.source access.depth (UnaryFn.const 100) (SpaceFunction.ofFP _ (constFn_mem_FP [])) access.sourceArity

example : UnaryFn (FlatAffineCompleteVertices.width
    (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => [])))
    (LeanCanny.Connectivity.CoordinateAffineComponentCover.cone F.source F.depth (fun _ => 100) (fun _ => []))) :=
  LeanCanny.Connectivity.CoordinateAffineComponentCover.width_unary F.source F.depth (fun _ => 100) (fun _ => [])
    access.source access.depth (UnaryFn.const 100) (SpaceFunction.ofFP _ (constFn_mem_FP [])) access.sourceArity

-- Native global slice regularity is decided by complete singular-child
-- search. A singular query also computes an actual ancestry-checked witness.
example : FlatAffineSliceRegularity.singularLanguage
    (CoordinateAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => []))
    (CoordinateAffineSliceRegularity.cone F.source F.depth (fun _ => 100) (fun _ => [])) ∈ PSPACE :=
  CoordinateAffineSliceRegularity.singular_mem_PSPACE access.source access.depth
    (UnaryFn.const 100) (SpaceFunction.ofFP _ (constFn_mem_FP [])) access.sourceArity

example : FlatAffineSliceRegularity.regularLanguage
    (CoordinateAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => []))
    (CoordinateAffineSliceRegularity.cone F.source F.depth (fun _ => 100) (fun _ => [])) ∈ PSPACE :=
  CoordinateAffineSliceRegularity.regular_mem_PSPACE access.source access.depth
    (UnaryFn.const 100) (SpaceFunction.ofFP _ (constFn_mem_FP [])) access.sourceArity

example (C : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next F)) :
    SpaceFunction (FlatAffineSingularSliceChoice.value F C) :=
  FlatAffineSingularSliceChoice.evaluator access C

example (C : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (FlatAffineCompleteChildLabels.parentCone F C) u v)
    (hq : pair u v ∈ FlatAffineSliceRegularity.singularLanguage F C) :
    FlatAffineCompleteRootStages.newest F u (FlatAffineCompleteVertices.vertexEquiv (FlatAffineCompleteRootStages.next F) C u
      ⟨FlatAffineSingularSliceChoice.value F C (pair u v), (FlatAffineSingularSliceChoice.value_valid F C u v hq).1⟩).val ∘ Sum.inl ∈
      FlatAffineSingularSliceSamples.singular F u
        (FlatAffineCompleteVertices.vertexEquiv F (FlatAffineCompleteChildLabels.parentCone F C) u ⟨v, hv⟩) :=
  FlatAffineSingularSliceChoice.value_singular F C u v hv hq

-- The terminal stage fixes every coordinate except the final one. The
-- actual source gives finitely many points and native point reachability.
example (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots
    (CoordinateAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => [])) u) :
    Finite (FlatAffineCompleteComponentSamples.slice
      (CoordinateAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => [])) u x) :=
  (CoordinateAffineTerminalSamples.finite_card_le F.source F.depth (fun _ => 100) (fun _ => []) u x
    (by change (3 : ℕ) ≤ 100; decide)).1

example : LeanCanny.Connectivity.CoordinateAffineTerminalReachability.language F.source F.depth (fun _ => 100) (fun _ => []) ∈ PSPACE :=
  LeanCanny.Connectivity.CoordinateAffineTerminalReachability.mem_PSPACE access.source access.depth
    (UnaryFn.const 100) (SpaceFunction.ofFP _ (constFn_mem_FP [])) access.sourceArity

example (C : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next F)) :
    SpaceDecider (FlatAffineChildSpatialEquality.language F C) :=
  FlatAffineChildSpatialEquality.decider access C

-- The terminal whole-set algorithm uses a constructed accessible cover,
-- including its clopen path saturation for subsequent endpoint attachments.
example : LeanCanny.Connectivity.CoordinateAffineTerminalConnectivity.language F.source F.depth (fun _ => 100) (fun _ => []) ∈ PSPACE :=
  LeanCanny.Connectivity.CoordinateAffineTerminalConnectivity.mem_PSPACE access.source access.depth
    (UnaryFn.const 100) (SpaceFunction.ofFP _ (constFn_mem_FP [])) access.sourceArity

example (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid
    (CoordinateAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => []))
    (FlatAffineCompleteChildLabels.parentCone
      (CoordinateAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => []))
      (CoordinateAffineSliceRegularity.cone F.source F.depth (fun _ => 100) (fun _ => []))) u v) :
    pair u v ∈ LeanCanny.Connectivity.CoordinateAffineTerminalConnectivity.language F.source F.depth (fun _ => 100) (fun _ => []) ↔
      IsPreconnected (LeanCanny.Connectivity.FlatAffineCompactComponentCover.Slice
        (CoordinateAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => []))
        (CoordinateAffineSliceRegularity.cone F.source F.depth (fun _ => 100) (fun _ => [])) u v hv) :=
  LeanCanny.Connectivity.CoordinateAffineTerminalConnectivity.packet F.source F.depth (fun _ => 100) (fun _ => []) u v
    (by change (3 : ℕ) ≤ 100; decide) hv

-- The varied row itself computes the frozen depth and its complete sampler.
-- The zero-depth seed remains a total native sampler as well.
example : UnaryFn (FlatAffineShiftPrefixInput.depth F selected) :=
  FlatAffineShiftPrefixInput.depth_unary access selected selected_unary

example : (FlatAffineShiftPrefixInput.input F cone selected).Access :=
  FlatAffineShiftPrefixInput.inputAccess access cone selected selected_unary

example (u : List Bool) : FlatAffineShiftPrefixInput.depth F selected u ≤ F.depth u :=
  FlatAffineShiftPrefixInput.depth_le F selected u

-- Complete joint samples and short branch descriptors compute exact frozen
-- ancestor labels through the original native coefficient programs.
example : (FlatAffineJointPrefixChoice.target F cone selected).Access :=
  FlatAffineJointPrefixChoice.targetAccess access cone selected selected_unary

example : SpaceFunction (FlatAffineJointPrefixChoice.value F cone selected) :=
  FlatAffineJointPrefixChoice.evaluator access cone selected selected_unary

example : SpaceFunction (FlatAffineBranchPrefixChoice.value F cone selected) :=
  FlatAffineBranchPrefixChoice.evaluator access cone selected selected_unary

example : FlatAffineBranchAncestorMatch.language F cone selected ∈ PSPACE :=
  FlatAffineBranchAncestorMatch.mem_PSPACE access cone selected selected_unary

example (k : Fin 3) : SpaceFunction (FlatAffineJointCopyPrefixChoice.value F cone selected k) :=
  FlatAffineJointCopyPrefixChoice.evaluator access cone selected selected_unary k

example : FlatAffineEndpointAncestorMatch.language F cone selected ∈ PSPACE :=
  FlatAffineEndpointAncestorMatch.mem_PSPACE access cone selected selected_unary

private def firstHeight (u : List Bool) : Fin (FlatAffineFullSourceTower.arity F u) :=
  ⟨0, by unfold FlatAffineFullSourceTower.arity; omega⟩

example : UnaryFn (fun u => (FlatAffineLastHeightRow.row F firstHeight u).val) :=
  FlatAffineLastHeightRow.row_unary access firstHeight (UnaryFn.const 0)

example : FlatAffineShiftPrefixInput.inputs (FlatAffineCompleteRootStages.next F)
    (FlatAffineLastHeightRow.row F firstHeight) = F := FlatAffineLastHeightRow.inputs_eq F firstHeight

private def coordinateF := CoordinateAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => [])
private theorem coordinateAccess : coordinateF.Access :=
  CoordinateAffinePrefix.access access.source access.depth (UnaryFn.const 100)
    (SpaceFunction.ofFP _ (constFn_mem_FP [])) access.sourceArity
private theorem coordinateCone : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next coordinateF) :=
  CoordinateAffineSliceRegularity.cone F.source F.depth (fun _ => 100) (fun _ => [])

example : SpaceFunction (FlatAffineBranchParentChoice.value coordinateF coordinateCone firstHeight) :=
  FlatAffineBranchParentChoice.evaluator coordinateAccess coordinateCone firstHeight (UnaryFn.const 0)

example : FlatAffineBranchOriginalAncestorMatch.language coordinateF coordinateCone firstHeight ∈ PSPACE :=
  FlatAffineBranchOriginalAncestorMatch.mem_PSPACE coordinateAccess coordinateCone firstHeight (UnaryFn.const 0)

example (G : Inputs) (C : FlatAffinePowerPositive.ConeCertificate G)
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count G u)) (c : List Bool)
    [Fintype (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.Index G C height c)]
    [LinearOrder (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.Index G C height c)]
    (B : LeanCanny.Connectivity.FlatAffineSlabGraphBranches.Family G C height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language G C height)
    (hold : (height (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c)).val <
      FlatAffineFullSourceTower.count G (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c))
    (j : LeanCanny.Connectivity.FlatAffineSlabGraphArcs.Index G C height c) :
    FlatAffineBranchPrefixChoice.value G C height (B.sampleQuery false j) =
      FlatAffineBranchPrefixChoice.value G C height (B.sampleQuery true j) :=
  B.native_prefix_same hc hold j

-- The actual coordinate records discharge every normal assumption in the
-- retained-slab regularity theorem; the source and parent may be singular.
example (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool)
    (C : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count
      (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)) u))
    (c : List Bool)
    (B : LeanCanny.Connectivity.FlatAffineSlabGraphBranches.Family
      (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)) C height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language
      (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)) C height)
    (h : Fin (P.dim (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) + 4))
    (hheight : height (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) =
      FlatAffinePowerSingularHeightCurves.rowIndex (CoordinateAffinePrefix.inputs P depth objective level)
        (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) h)
    (hactive : h ∈ FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) (depth (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots (CoordinateAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c))
    (t : Set.Ioo (FlatAffineSlabGraphContext.endpointValue _ C height false c)
      (FlatAffineSlabGraphContext.endpointValue _ C height true c))
    (y : Fin (P.dim (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) + 4) → ℝ)
    (hy : y ∈ FlatAffineShiftedSlice.slice (CoordinateAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) x h t.val) :
    Function.Surjective (LeanCanny.Geometry.FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
      (BoundedFullCriticalSamples.polynomial P (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c))
      (FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level)
        (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) (depth (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c)))
      (FlatAffineFullSourceTower.direction (CoordinateAffinePrefix.inputs P depth objective level)
        (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) (depth (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c))) y) :=
  B.shifted_slice_regular (CoordinateAffinePrefix.inputs P depth objective level) C height c hc h hheight
    (CoordinateAffineSliceControls.normal P depth objective level _ _) hactive x t y hy

-- Actual coordinate objectives also discharge the component-sampling premise.
example (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool)
    (C : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count
      (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)) u))
    (c : List Bool)
    (B : LeanCanny.Connectivity.FlatAffineSlabGraphBranches.Family
      (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)) C height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language
      (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)) C height)
    (h : Fin (P.dim (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) + 4))
    (hheight : height (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) =
      FlatAffinePowerSingularHeightCurves.rowIndex (CoordinateAffinePrefix.inputs P depth objective level)
        (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) h)
    (hactive : h ∈ FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) (depth (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots (CoordinateAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c))
    (t : Set.Ioo (FlatAffineSlabGraphContext.endpointValue _ C height false c)
      (FlatAffineSlabGraphContext.endpointValue _ C height true c))
    (y : Fin (P.dim (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) + 4) → ℝ)
    (hy : y ∈ FlatAffineShiftedSlice.slice (CoordinateAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) x h t.val) :
    ∃ j : LeanCanny.Connectivity.FlatAffineSlabGraphBranches.ParentIndex
        (CoordinateAffinePrefix.inputs P depth objective level) C height c x,
      JoinedIn (FlatAffineShiftedSlice.slice (CoordinateAffinePrefix.inputs P depth objective level)
        (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) x h t.val) y
        (FlatAffineShiftedSlice.spatialPoint (CoordinateAffinePrefix.inputs P depth objective level)
          (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) (B.curve j.val t.val)) :=
  B.sample_parent_branch (CoordinateAffinePrefix.inputs P depth objective level) C height c hc h hheight
    (CoordinateAffineSliceControls.normal P depth objective level _ _) hactive
    (CoordinateAffineSliceControls.objective_independent P depth objective level _ _) x t y hy

-- The original native source supplies compact coarser slices and a proper
-- height map even at singular parents and endpoint levels.
example (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (FlatAffineFullSourceTower.arity F u)) :
    IsProperMap (FlatAffineShiftedSlice.projection F u x h) :=
  FlatAffineShiftedSlice.projection_proper F u x h

-- Construct the full original component saturation from actual coordinate records.
example (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool)
    (C : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count
      (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)) u))
    (c : List Bool)
    (B : LeanCanny.Connectivity.FlatAffineSlabGraphBranches.Family
      (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)) C height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language
      (FlatAffineCompleteRootStages.next (CoordinateAffinePrefix.inputs P depth objective level)) C height)
    (h : Fin (P.dim (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) + 4))
    (hheight : height (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) =
      FlatAffinePowerSingularHeightCurves.rowIndex (CoordinateAffinePrefix.inputs P depth objective level)
        (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) h)
    (hactive : h ∈ FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) (depth (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots (CoordinateAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c))
    : Nonempty (LeanCanny.Connectivity.ComponentSlabCover.InteriorData
      (FlatAffineShiftedSlice.projection (CoordinateAffinePrefix.inputs P depth objective level)
        (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) x h)
      (FlatAffineSlabGraphContext.endpointValue _ C height false c)
      (FlatAffineSlabGraphContext.endpointValue _ C height true c)
      (LeanCanny.Connectivity.FlatAffineSlabGraphBranches.ParentIndex
        (CoordinateAffinePrefix.inputs P depth objective level) C height c x)) := by
  obtain ⟨D, _, _, _⟩ := LeanCanny.Connectivity.FlatAffineSlabSaturation.exists_interior_data
    (CoordinateAffinePrefix.inputs P depth objective level) C height c B hc h hheight
    (CoordinateAffineSliceControls.normal P depth objective level _ _) hactive
    (CoordinateAffineSliceControls.objective_independent P depth objective level _ _) x
  exact ⟨D⟩

-- Doubled midpoint rows retain singular components and have native global
-- regularity decisions from the original readers alone.
example : FlatAffineSliceRegularity.regularLanguage
    (CoordinateDoubleAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => []))
    (CoordinateDoubleAffineSliceRegularity.cone F.source F.depth (fun _ => 100) (fun _ => [])) ∈ PSPACE :=
  CoordinateDoubleAffineSliceRegularity.regular_mem_PSPACE access.source access.depth
    (UnaryFn.const 100) (SpaceFunction.ofFP _ (constFn_mem_FP [])) access.sourceArity

example (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots
    (CoordinateDoubleAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => [])) u) :
    Finite (ConnectedComponents (FlatAffineCompleteComponentSamples.slice
      (CoordinateDoubleAffinePrefix.inputs F.source F.depth (fun _ => 100) (fun _ => [])) u x)) :=
  (LeanCanny.Connectivity.CoordinateDoubleAffineComponentCover.finite_components
    F.source F.depth (fun _ => 100) (fun _ => []) u x).1

-- Slab regularity also applies to the actual doubled records.
example (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool)
    (C : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth objective level)))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth objective level)) u))
    (c : List Bool)
    (B : LeanCanny.Connectivity.FlatAffineSlabGraphBranches.Family
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth objective level)) C height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth objective level)) C height)
    (h : Fin (P.dim (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) + 4))
    (hheight : height (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) =
      FlatAffinePowerSingularHeightCurves.rowIndex (CoordinateDoubleAffinePrefix.inputs P depth objective level)
        (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) h)
    (hactive : h ∈ FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) (depth (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots (CoordinateDoubleAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c))
    (t : Set.Ioo (FlatAffineSlabGraphContext.endpointValue _ C height false c)
      (FlatAffineSlabGraphContext.endpointValue _ C height true c))
    (y : Fin (P.dim (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) + 4) → ℝ)
    (hy : y ∈ FlatAffineShiftedSlice.slice (CoordinateDoubleAffinePrefix.inputs P depth objective level)
      (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) x h t.val) :
    Function.Surjective (LeanCanny.Geometry.FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
      (BoundedFullCriticalSamples.polynomial P (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c))
      (FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth objective level)
        (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) (depth (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c)))
      (FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth objective level)
        (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c) (depth (LeanCanny.Connectivity.FlatAffineSlabGraphArcs.original c))) y) :=
  B.shifted_slice_regular_scaled (CoordinateDoubleAffinePrefix.inputs P depth objective level) C height c hc h hheight (fun _ => 2) (fun _ => by decide)
    (CoordinateDoubleAffinePrefix.normal P depth objective level _ _) hactive x t y hy


end
end ActualHeightReaderRegression
