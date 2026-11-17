module

public import LeanCanny.CountingHierarchy.Controlled
public import LeanCanny.CountingHierarchy.ControlledSigns
public import LeanCanny.CountingHierarchy.ControlledCoefficients
public import LeanCanny.CountingHierarchy.CoefficientEvaluation
public import LeanCanny.CountingHierarchy.TraceExponential
public import LeanCanny.CountingHierarchy.CharacteristicCoefficientEvaluation
public import LeanCanny.CountingHierarchy.QuotientCharacteristicSpecialization
public import LeanCanny.CountingHierarchy.PurePowerResidueMap
public import LeanCanny.CountingHierarchy.SparseRootSelection
public import LeanCanny.CountingHierarchy.QuotientSimpleRoot
public import LeanCanny.CountingHierarchy.NormPolynomialEvaluation
public import LeanCanny.CountingHierarchy.CriticalMinimumValue
public import LeanCanny.CountingHierarchy.PowerTraceCharacteristic
public import LeanCanny.CountingHierarchy.UnityWeightedSum
public import LeanCanny.CountingHierarchy.CriticalFeasibility
public import LeanCanny.CountingHierarchy.QuotientMassBounds
public import LeanCanny.CountingHierarchy.QuotientParameterDegree
public import LeanCanny.CountingHierarchy.BoundedCriticalFeasibility
public import LeanCanny.CountingHierarchy.QuotientNormSpecialization
public import LeanCanny.CountingHierarchy.RootLabelProductCriterion
public import LeanCanny.CountingHierarchy.RationalSignProductBounds
public import LeanCanny.CountingHierarchy.FiniteCriticalCriterion
public import LeanCanny.CountingHierarchy.SparseRootLabelEvaluation
public import LeanCanny.CountingHierarchy.NativeNormBounds
public import LeanCanny.CountingHierarchy.QuotientDeterminantEvaluation
public import LeanCanny.CountingHierarchy.ControlledFeasibility

public import LeanCanny.CountingHierarchy.ExistentialUpperBound
public import LeanCanny.CountingHierarchy.FingerprintRootSelection
public import LeanCanny.CountingHierarchy.FingerprintIntegerRootLabels
public import LeanCanny.CountingHierarchy.DegreePieceClosedLift
public import LeanCanny.CountingHierarchy.CoordinateFingerprintSelection
public import LeanCanny.CountingHierarchy.AlgebraicFiberSeparation
public import LeanCanny.CountingHierarchy.MonicPowerSubstitution
public import LeanCanny.CountingHierarchy.CandidateCoordinateCoverage
public import LeanCanny.CountingHierarchy.PrescribedRootLabelEvaluation
public import LeanCanny.CountingHierarchy.FingerprintLabelBounds
public import LeanCanny.CountingHierarchy.FiberCoerciveMinimum
public import LeanCanny.CountingHierarchy.FingerprintLabelPolynomial

public import LeanCanny.CountingHierarchy.ControlledBoundedProduct
public import LeanCanny.CountingHierarchy.ControlledDegreePiece
public import LeanCanny.CountingHierarchy.RelativeDegreePieceGeometry
public import LeanCanny.CountingHierarchy.CoordinateCandidateEvaluation
public import LeanCanny.CountingHierarchy.NativePrescribedLabelBounds

public import LeanCanny.CountingHierarchy.RelativeTwoTestCriterion
public import LeanCanny.CountingHierarchy.ControlledCoordinateCandidate
public import LeanCanny.CountingHierarchy.ControlledPrescribedLabel
public import LeanCanny.CountingHierarchy.ControlledCoordinateLift
public import LeanCanny.CountingHierarchy.IndexedSystemFeasibility
public import LeanCanny.CountingHierarchy.NatTupleWitnessEncoding

public import LeanCanny.CountingHierarchy.RealCircuit
public import LeanCanny.CountingHierarchy.IndexedSystemFunction

/-! # Counting-hierarchy access to implicit real-algebraic constructions

The counting-hierarchy result follows OpenAI,
*Existential–universal real sentences in the counting hierarchy* (October 4, 2026):
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/etr-counting-hierarchy.pdf
The historical `LeanCanny` namespace records the host project, not authorship.

The controlled-polynomial access layer uses CSLib Frontier's fixed-oracle
counting hierarchy. It includes coefficient extraction, factorial residues, and
indexed coefficients of the truncated exponential of divided negative traces.
The pure-power quotient has a proved monomial basis and a trace--residue
identity over arbitrary coefficient rings. The finite exponential is identified with actual characteristic coefficients
by Newton recurrence. The constructed uniform trace evaluator and characteristic coefficient
algorithm cost five and eight additional function levels respectively. The
finite real-feasibility criterion constructs short root labels and an actual
integer quotient determinant from source degree and log-mass bounds. Constructed
native evaluators and polynomial-width coded witnesses prove real feasibility
of every controlled F_a family in C_(a+26) P. The native modular tree evaluator
and equation compiler place the encoded ETR language and all of ∃ℝ in C_26 P.
The source-derived two-test construction decides controlled two-block zero
avoidance in C_(a+60) P. A fiber-preserving native Boolean compiler gives the
total encoded language ∃∀ℝ in C_60 P, and the same bound
for every language polynomial-time many-one reducible to it. Shared arithmetic
circuits retain their intermediate wires through a proved gate-equation bridge
and native matrix writers, with C_26 P and C_60 P bounds for native circuit families.
-/
