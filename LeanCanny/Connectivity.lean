import LeanCanny.Connectivity.Encoding
import LeanCanny.Connectivity.FormulaPathCover
import LeanCanny.Connectivity.EndpointValidation
import LeanCanny.Connectivity.AccessibleArc
import LeanCanny.Connectivity.RegularRootArcs
import LeanCanny.Connectivity.SlabCover
import LeanCanny.Connectivity.BitFrontierCover
import LeanCanny.Geometry.RootBranchCount
import LeanCanny.Geometry.ProjectionCriticalBranches
import LeanCanny.Geometry.ComponentCriticalSampling
import LeanCanny.Geometry.PolynomialComponentTransport
import LeanCanny.Connectivity.PolynomialSlabCover
import LeanCanny.Connectivity.EndpointAttachment
import LeanCanny.Geometry.PolynomialHypersurfaceSweep
import LeanCanny.Algebra.FixedLevelRegularSpecialization
import LeanCanny.Geometry.CoordinateSlice
import LeanCanny.Connectivity.CoordinateSlabCover
import LeanCanny.Connectivity.OneDimensionPoint
import LeanCanny.Geometry.BoundedCriticalCoordinates
import LeanCanny.Geometry.RegularCoordinateRootCount
import LeanCanny.Geometry.CoordinateSweepBounds
import LeanCanny.Geometry.SingularParameterBounds
import LeanCanny.Geometry.UniformCriticalRegularityBounds
import LeanCanny.Algebra.ParameterizedCriticalCoefficientSpace
import LeanCanny.Algebra.ProjectiveDirectionGrid
import LeanCanny.Encoding.FermatCriticalDirection
import LeanCanny.Encoding.CriticalRegularLevel
import LeanCanny.Geometry.IntegerRegularSweepCertificate
import LeanCanny.ETR.ComplexCircuitPSPACE
import LeanCanny.ETR.ComplexCircuitBuilders
import LeanCanny.ETR.ComplexDyadicPSPACE
import LeanCanny.ETR.ComplexDifferentialEncoding
import LeanCanny.ETR.ComplexTermDifferential
import LeanCanny.ETR.ComplexHessianFamily
import LeanCanny.ETR.ComplexKernelRowEncoding
import LeanCanny.ETR.ComplexSampledPSPACE
import LeanCanny.Encoding.FermatSweepKernelCertificate
import LeanCanny.Encoding.FermatAffineKernelBridge
import LeanCanny.Encoding.FermatFrozenSource
import LeanCanny.Encoding.FermatInfinityQuery
import LeanCanny.Encoding.FermatDirectionChoice
import LeanCanny.Encoding.FermatTermPreparation
import LeanCanny.Geometry.CompactSublevelComponents
import LeanCanny.Geometry.CircleSublevelLift
import LeanCanny.Geometry.PurePowerSublevelLevels
import LeanCanny.Geometry.EffectiveSublevelComponents
import LeanCanny.Encoding.GeneralRegularLevel
import LeanCanny.Geometry.BoundedRegularComponents
import LeanCanny.Encoding.BoundedRegularControls
import LeanCanny.Encoding.BoundedDirectionChoice
import LeanCanny.Geometry.LiftPaths
import LeanCanny.Connectivity.BoundedMarkedCover
import LeanCanny.ETR.ComplexCircuitFreezeSlice
import LeanCanny.Encoding.BoundedFullGeometry
import LeanCanny.Encoding.BoundedConstrainedQuery
import LeanCanny.Encoding.BoundedWitnessQuery
import LeanCanny.Connectivity.BoundedEndpointLocator
import LeanCanny.Connectivity.BoundedPieceQueries
import LeanCanny.Encoding.BoundedFullDirectionChoice
import LeanCanny.Encoding.BoundedFullCriticalSamples
import LeanCanny.Encoding.BoundedCriticalSampleQuery
import LeanCanny.Encoding.BoundedCriticalSeparator
import LeanCanny.Encoding.BoundedCriticalLabels
import LeanCanny.Encoding.BoundedCriticalCoefficient
import LeanCanny.Encoding.BoundedProjectionCoefficient
import LeanCanny.Encoding.BoundedProjectionRationalCount
import LeanCanny.Encoding.BoundedSampleLabelCertificate
import LeanCanny.Encoding.BoundedProjectionRootSeparation
import LeanCanny.Encoding.BoundedProjectionThom
import LeanCanny.Encoding.BoundedProjectionDerivativeSigns
import LeanCanny.Encoding.BoundedProjectionMoments
import LeanCanny.Encoding.BoundedProjectionRecordSpan
import LeanCanny.Encoding.BoundedProjectionBasisGram
import LeanCanny.Encoding.BoundedProjectionBasisPencil
import LeanCanny.Encoding.BoundedProjectionHashChoice
import LeanCanny.Encoding.BoundedProjectionSignatureProbe
import LeanCanny.Encoding.BoundedProjectionSignatureRead
import LeanCanny.Encoding.BoundedProjectionOrderedRoot
import LeanCanny.Encoding.BoundedProjectionTestSign
import LeanCanny.Encoding.BoundedAlgebraicSliceDegree
import LeanCanny.Encoding.BoundedAlgebraicSlicePrincipal
import LeanCanny.Algebra.PolynomialPseudoRemainderReader
import LeanCanny.Encoding.BoundedAlgebraicSliceTarskiPSPACE
import LeanCanny.Encoding.BoundedAlgebraicFiberRoot
import LeanCanny.Encoding.BoundedAlgebraicFiberSignCut
import LeanCanny.Encoding.BoundedAlgebraicFiberThom
import LeanCanny.Encoding.BoundedAlgebraicFiberMoments
import LeanCanny.Encoding.BoundedAlgebraicFiberRecordGram
import LeanCanny.Encoding.BoundedAlgebraicFiberBasisGram
import LeanCanny.Connectivity.AlgebraicSliceSystemReachability
import LeanCanny.ETR.FormulaBooleanCircuitBridge
import LeanCanny.Connectivity.FormulaAlgebraicSlice
import LeanCanny.Connectivity.FormulaRationalSlice
import LeanCanny.Encoding.BoundedProjectionFeatureMoments
import LeanCanny.Encoding.BoundedComplexSampleQuery
import LeanCanny.Encoding.BoundedComplexSeparator
import LeanCanny.Encoding.BoundedCriticalCoordinate
import LeanCanny.Encoding.BoundedCriticalRationalCoordinates
import LeanCanny.Encoding.BoundedCriticalSampleCount
import LeanCanny.Encoding.BoundedCriticalSampleIsolation
import LeanCanny.Encoding.BoundedCriticalSampleMoments
import LeanCanny.Encoding.BoundedCriticalSampleRankBasis
import LeanCanny.Encoding.BoundedCriticalSampleDescriptors
import LeanCanny.Encoding.BoundedCriticalSampleTestSign
import LeanCanny.Encoding.BoundedCriticalSampleCoordinateSign
import LeanCanny.Encoding.BoundedCriticalSampleFormula
import LeanCanny.Encoding.BoundedCriticalSampleSliceRootCount
import LeanCanny.Encoding.BoundedCriticalSampleLineZero
import LeanCanny.Encoding.BoundedCriticalSampleBlockTerm
import LeanCanny.Encoding.BoundedCriticalSampleBlockCriticalGeometry
import LeanCanny.Encoding.BoundedCriticalSampleJointGeometry
import LeanCanny.Encoding.BoundedCriticalSampleJointCoordinateCoefficient
import LeanCanny.Encoding.BoundedCriticalSampleChildParameters
import LeanCanny.Encoding.BoundedCriticalSampleChildEquationCount
import LeanCanny.Encoding.BoundedCriticalSampleChildRegularCount
import LeanCanny.Encoding.BoundedCriticalSampleChildParentQueries
import LeanCanny.Encoding.BoundedCriticalSampleChildRankBasis
import LeanCanny.Encoding.BoundedCriticalSampleChildHashChoice
import LeanCanny.Encoding.BoundedCriticalSampleChildDescriptors
import LeanCanny.Encoding.BoundedCriticalSampleChildActualSamples
import LeanCanny.Connectivity.CriticalSampleChildCoverage
import LeanCanny.Connectivity.CriticalSampleChildPairs
import LeanCanny.Encoding.BoundedCriticalSampleChildTermSign
import LeanCanny.Connectivity.CriticalSampleOriginalSlice
import LeanCanny.ETR.ComplexBlockKernelGeometry
import LeanCanny.Encoding.BoundedCriticalSampleBlockRegularity
import LeanCanny.Encoding.FermatCommonCriticalDirection
import LeanCanny.Connectivity.CriticalSampleSelectedDirection
import LeanCanny.Encoding.BoundedFullBlockRegularity
import LeanCanny.Encoding.BoundedFullBlockDirectionChoice
import LeanCanny.Encoding.BoundedFullSampleBlockScaling
import LeanCanny.Encoding.BoundedFullSampleChildDescriptorGeometry
import LeanCanny.Encoding.BoundedFullSampleChildActualSamples
import LeanCanny.Connectivity.FullSampleChildPairs
import LeanCanny.Encoding.FullSampleNextBlock
import LeanCanny.Encoding.FullSampleNextStage
import LeanCanny.Encoding.NamedParentChildSamples
import LeanCanny.Encoding.NamedRationalSeed
import LeanCanny.Geometry.TriangularPolynomialRegularity
import LeanCanny.Encoding.FlatFullSourceCoordinate
import LeanCanny.Encoding.FlatFullSourcePlan
import LeanCanny.Encoding.FlatFullSourceCriticalCoefficient
import LeanCanny.Encoding.FlatFullSourceCoefficient
import LeanCanny.Encoding.FlatFullSourcePositive
import LeanCanny.Encoding.FlatFullSourcePositiveCoordinateCoefficient
import LeanCanny.Encoding.FlatFullSourceSampleRegularFilter
import LeanCanny.Encoding.FlatFullSourceSampleVertices
import LeanCanny.Encoding.FlatFullSourceSampleDerivativeSigns
import LeanCanny.Algebra.FixedWidthLinearCoefficientSpace
import LeanCanny.Encoding.BoundedFullSampleChildParentQueries
import LeanCanny.Encoding.BoundedCriticalSampleFiberRecordGram
import LeanCanny.Encoding.BoundedCriticalSampleFiberBasisGram
import LeanCanny.Encoding.BoundedCriticalSampleFiberFeatureMoments
import LeanCanny.Encoding.BoundedCriticalSampleFiberSignatureRead
import LeanCanny.Encoding.BoundedCriticalSampleFiberCellQueries
import LeanCanny.Encoding.BoundedCriticalSampleFiberLineTest
import LeanCanny.Connectivity.CriticalSampleSliceBooleanReachability
import LeanCanny.Connectivity.CriticalSampleSliceCellSignLanguage
import LeanCanny.Connectivity.FormulaCriticalSampleLineGeometry
import LeanCanny.Connectivity.FormulaCriticalSampleLinePoint

/-! # Connectivity development

Checked input encodings, finite closed path covers, frontier incidence, and native polynomial-space
implicit-graph algorithms. Canonical input recognition is polynomial time;
singleton endpoint validation is in native PSPACE on all bitstrings. For
supplied formula-defined covers, ETR supplies the validity and intersection
tests. Proper regular root systems have complete finite global branches;
bounded continuous algebraic branches extend to their finite endpoints. These
arcs and accessible endpoint-slice covers preserve slab connectivity through
their frontier graph. Effective frontier graphs have native polynomial-space
connectivity tests. Explicit polynomial systems have the expected analytic
Jacobian. Proper polynomial level functions give spatial critical curves with
an integer projection direction and finitely many exceptional levels. Regular
compact fibers have finitely many path components, all sampled by the critical
equations. Fiber connection between continuous sections is constant on each
preconnected regular-value region; the exceptional levels are constructed
algebraically. Saturating the critical branches gives a finite clopen cover of
the entire regular slab, with both connectivity tests reduced to one sample
fiber. Each saturated component has a connected limit in both endpoint fibers,
including singular ones. A recursive accessible slice cover turns this limit
connection into a path and attaches boundary points to a branch endpoint.
Saturating recursive endpoint covers by finite graph reachability gives clopen
path components. Attaching these to the interior pieces gives a closed path
cover of the entire original closed slab. Its final label families form a sum;
overlap and validity require no closure queries. Membership in a recursive
clopen component is computed by the native polynomial-space graph algorithm
given a locator for an original piece containing the queried point.
Coordinate sweeps on fixed proper polynomial hypersurfaces have constructed
finite exceptional value sets, proper projections, and actual regular product
charts. Fixed-level generic critical projections also retain finite simple
roots and coordinate annihilators over coefficient fields containing a sweep
parameter. Uniform specialization now constructs one integer direction and one
exceptional parameter factor for the entire polynomial slice family. Its
spatial root system is proper on a fixed compact hypersurface; complete critical
arcs extend continuously to exceptional endpoints. Their saturated components
give the original coordinate slab a finite clopen path cover. Overlap tests are
connections in an actual polynomial slice in one fewer coordinate. Recursive
endpoint component covers give a finite closed path cover of the whole closed
coordinate slab, with both connectivity tests preserved. Concrete Macaulay
numerator coefficients now give bounded nonzero coordinate equations at regular
affine roots, also for the integer spatial critical slice systems. Both variable
degrees, coefficient bits, and the coordinate-specialization factor are bounded.
These certificates bound regular root fibers by a product of coordinate degrees,
with an explicit binary label-width allowance.
The same constructed coordinate polynomials also annihilate singular finite
fibers over algebraically closed extensions, with the same root-count budget.
Constrained coercive minimization constructs bounded integer annihilators for
finite projected zero sets even when their spatial fibers have positive
dimension. For a regular integer hypersurface this gives a bounded exceptional
coordinate-sweep factor. Input bounds for the generic direction and critical
system query encodings remain required. For integer systems with finitely many
singular parameter values, a new bounded exceptional factor replaces any
qualitative regularity witness, allowing positive-dimensional bad fibers.
Applying this bound to the parameter-ring critical systems still requires
native access to their coefficient encodings. Integer parameter substitution
now preserves evaluation and spatial Jacobians with bounded degree and mass;
qualitative regularity factors for the spatial critical systems can be replaced
by bounded factors for those same parameter-ring equations.
The generic field direction and regular-slice certificate now construct one
such bounded factor for the uniform spatial critical system. Its mass bound
still depends on the chosen direction allowance, which lacks an input bound.
Native coefficient programs now split the integer parameter block and evaluate
the actual spatial critical equations from a supplied source reader. Binary
degree guards and direction scalars avoid unary conversion of large values.
A root-free homogeneous system admits an integer specialization in a grid
bounded by its Macaulay column count and parameter degree, with an explicit
binary-length bound. Constructing the required root-free projective system
for the affine critical families remains required.
For a polynomial with a pure-power leading form, the original homogenized
critical equations now have a constructed root-free generic system at infinity.
Appending the spatial Jacobian gives a root-free square projective system when
the hypersurface is regular over field extensions. The bounded grid therefore
constructs an integer critical direction for this family, with a polynomial
binary-width bound. Its direction has a fixed-length record with native field
access, allowing binary source degrees. Establishing extension-field regularity
for pure-power leading sources now follows from a bounded critical-value
annihilator, including degenerate complex critical points. An explicit positive
dyadic level avoids every critical value and has a polynomial binary exponent
budget. Native polynomial-time metadata and modular denominator access are
provided. Clearing this denominator preserves the actual hypersurface and
extension-field regularity in an integer pure-power leading equation. Its
native coefficient evaluator uses one source call and modular arithmetic,
with no materialized denominator. The actual coordinate-slice polynomial preserves the leading form
and commutes with differentiation. A transcendental sweep value makes that
slice regular over every extension field, so the bounded integer direction
also applies to the generic slice family of the constructed dyadic source.
That actual parameter-ring family has a root-free specialization at a bounded
integer direction and sweep value. A short fixed-length record stores both,
with native polynomial-time field access. Validity asks only for emptiness of
the sampled complex projective bad-root fiber. Any valid sample certifies
generic Jacobian regularity through maximal-minor transfer; the minor itself
is not retained. The complex test is equivalent to finitely many normalized
affine charts. Its native decision procedure remains to be constructed.
Complex arithmetic networks now have an explicit native polynomial-time
compiler to real equations, preserving shared wires and integer payloads.
The completed ETR procedure supplies native feasibility and emptiness tests
for these compiled networks. Binary powers have shared networks with two
multiplications per exponent bit and polynomial-time encoders. The resulting
denominator-cleared equation has an exact native PSPACE test when appended to
an encoded source network. A shared derivative transformation preserves
acyclicity and computes the formal partial derivatives of all source wires.
Its native writer replaces each operation by four operations without expanding
the source polynomials. Source arithmetic terms now compile to acyclic shared
networks in native polynomial time, with bounds on all intermediate states and
constructed fresh-wire metadata. Their denominator-cleared equations have
native PSPACE tests, and their derivative networks compute the actual formal
partial derivatives of the original terms.
The sampled validity predicate now has an exact determinant-free description:
normalized kernel vectors detect affine singular critical roots, and explicit
pure-power equations detect roots at infinity. The spatial Jacobian's actual
degree is strictly below its assigned homogenization degree, so its appended
row vanishes at infinity. This split allows coefficient specialization maps
with a kernel, including evaluation at the finite sweep sample. The infinity
charts now have shared binary-power circuits with exact completion and root
semantics, native polynomial-time query writers, and native PSPACE feasibility
and emptiness tests. Their direction coefficients are read from the actual
fixed-width record and kept binary; the nonzero leading scalar cancels from
the equations. Repeated shared differentiation computes exact Hessians of the
original source. Initialized copies share input coordinates and use disjoint
auxiliary ranges, with native polynomial-time encoders. Kernel-row circuits
compute the critical equations and Hessian-vector sums. The actual affine
chart predicate expands into these gradient and Hessian equations. Complete
normalized critical-kernel queries now have exact shared-circuit semantics,
native polynomial-time encoders, and native PSPACE tests for compiled source
terms. The original compiler's wires can now be reindexed to freeze the actual
record's swept coordinate, with an exact coordinate-slice polynomial identity.
Shared pure-power sums and dyadic scaling append to this source in one acyclic
program. Its native encoder, output metadata, and critical-kernel tests retain
both binary exponent words. Its exact coefficient-map identity now identifies
the source with the finite-coordinate Fermat certificate. The affine and
infinity tests give a native PSPACE checker for the original Valid predicate.
A bounded fixed-width search selects a valid direction-and-sample record for
the constructed regular integer source, with no supplied validity algorithm.
For an encoded low term, its normalized size supplies a degree twice an odd number and
coefficient-mass control. This gives native record preparation from the
source reader and unary dimension, and generic-slice regularity whenever
the term's variables fit that dimension.
For compact decreasing sublevel neighborhoods, component intersections now
recover the exact zero-set component, even at singular zeros. Distinct zero
components separate at some positive tolerance.
Adding two squared slack coordinates gives a level equation with connected
circle fibers over its sublevel set, including singleton fibers at radius
zero. Its continuous section constructs a quotient projection preserving
exact connected components and whole-space preconnectedness.
For nonnegative smooth energies with compact sublevels, a positive interval
free of critical values preserves the component relation on the original
zeros. Arbitrary integer polynomials now have bounded critical-value
annihilators, including positive-dimensional critical loci. These give an
explicit dyadic component tolerance whose exponent has native polynomial-time
computation from dimension, degree and mass controls. This result concerns
connections between zeros; path recovery for the original zero set remains
required. Two even pure-power slack coordinates retain the same critical
values and properness. When the degree is twice an odd number, a constructed
coordinate homeomorphism transfers the circle lift's component preservation.
For bounded polynomial zeros, an explicit sphere equation gives a nonnegative
energy with compact sublevels and derived degree, mass and radius controls.
Its circle projection preserves components and preconnectedness. A bounded
positive pure-power perturbation preserves connections between original zeros
throughout the safe level window. Shifting before the existing integer
regularization keeps the resulting level inside that window. The constructed
proper pure-power hypersurface is regular over rational field extensions and
preserves the component relation between lifted original points. A shared
source-circuit writer computes all large coefficients from binary exponent
words, with exact finite-coordinate slice semantics. The original encoded
term supplies degree and mass allowances. Native affine and infinity tests
validate the constructed source's record, and bounded search selects one in
polynomial space. Selection and actual source serialization compose in
polynomial space.
Circle fibers, including singleton fibers, also preserve exact paths. The
coordinate homeomorphisms transfer this to pure-power slack variables and
the bounded sphere zero source. This path correspondence concerns the set
being lifted; recovery from a positive perturbed sublevel remains required.
A single polynomial marks the source points representing original zeros.
Every marked point is joined to the lift of its original projection. Bounded
original connectedness is therefore equivalent to connectivity between marked
source points. The native graph test quantifies over marked endpoint pieces
while retaining every valid piece for traversal, so additional source
components need not be proved absent. The transfer through an accessible
cover is proved; the actual recursive cover and its query writers remain
required.
Shared source circuits can also freeze a coordinate at an existing parameter
wire. Reindexing preserves their operation count, and the writer has native
polynomial-time bounds. Its polynomial interpretation is the exact coordinate
slice at the parameter value in any commutative ring, including irrational
real values. The critical-level formulas selecting those values and the full
recursive query construction remain required.
The full varying-coordinate bounded regular source now has its own shared
writer from original term, unary dimension and binary radius. It requires no
sample or record reader. Both the source polynomial and the marking energy
are computed on explicit wires with native polynomial-time encoders and
unary address bounds. Exact integer polynomial identities identify their
finite coordinate order; the permutation preserves the pure-power leading
shape, extension-field regularity and properness. This supplies the source
family for recursive queries; selecting critical parameters and constructing
the actual covers remain required.
Real-input shared-circuit queries now force zero imaginary parts on all input
wires. Acyclic gate assignments have the exact integer polynomial interpretation,
so the full source and marking tests characterize real points, with native
polynomial-time encoders and polynomial-space evaluators. Boolean coordinate
constraints share that same real assignment, including inequalities and singleton
endpoint formulas. The finite-coordinate bridge proves constrained source and
marking correctness without expanding the source polynomials. Actual recursive
piece formulas and critical-parameter selection remain required.
Formula witnesses now occupy a wire family disjoint from the entire source
program. Native parity reindexing and explicit input-link gates implement this
layout, preserving arbitrary existential formula witnesses. The full source
and marked-source tests therefore also have native polynomial-space evaluators
when the formula uses variables beyond the spatial coordinates and initial
circuit inputs. Constructing the recursive formulas remains required.
Explicit input-link ports now restore the original coordinate order in those
queries. The marked projection retains the original coordinates, so singleton
endpoint formulas describe its exact fibers. Native marked-piece tests and
bounded label search locate a piece meeting an endpoint fiber whenever the
pieces cover it. The algorithm charges the actual source and formula writers;
coverage and singleton validity are correctness conditions. The recursive
piece family itself remains to be constructed.
Witness-defined piece intersections now use independent parity copies of the
two formulas. Duplicate input links identify their entire spatial tuples with
one actual source circuit, while leaving all further witnesses independent.
The links remain correct when their count exceeds the initial source frame.
Exact geometric nonemptiness, marking, adjacency and marked-adjacency tests
therefore have native polynomial-space certificates from the source and piece
writers. The actual recursive pieces and their formula writers remain required.
Shared Hessian programs now also differentiate the full varying-coordinate
source directly. Their normalized complex critical-kernel charts have native
polynomial-time writers and polynomial-space feasibility and emptiness tests.
Direction scalars come from actual fixed-width binary records with a width
derived from the source controls. Exact polynomial identities identify the
finite-coordinate critical systems, independently of unused input-frame slots.
Native bounded search now selects a fixed-length full-source direction record
whose normalized complex critical-kernel charts are all empty. Existence uses
the constructed source's regular pure-power form, and both selection and
subsequent critical-query serialization have native polynomial-space bounds.
The selected direction now also gives analytically simple real critical
samples of this exact source. Concrete coordinate eliminants bound their
number by an exponential in a natively computed polynomial label width.
Every source point is joined to one of these samples in its own component;
the source is preconnected exactly when every pair of samples is joined.
The same bound therefore counts its connected components, without a supplied
root-finiteness assumption. The complete complex critical sample set now has
the same explicit count bound. Finiteness follows algebraically by adjoining
the inverse Jacobian determinant; singular components elsewhere are allowed.
Native bounded search now selects an integer projection record separating all
complex samples and also their embedded real subset. Its collision tests use
two independent complex sample circuits and compare both components. Native
Boolean queries expose both real and imaginary spatial coordinates, charging
the actual selected direction and separator. Arbitrary bounded weight records
now give nonzero integer projection equations annihilating every complex sample,
with native modular coefficient readers and uniform degree and coefficient bounds.
Unit records supply individual coordinate equations, and the complex separating
projection uses the same native backend. A native checked degree table feeds
these equations into a balanced primitive tree. Its common parameter and rational
coordinates recover every complex sample and every real sample, with nonzero
denominators, native coefficient readers, and explicit degree and mass bounds.
Even denominator powers now clear the original critical equations on these
coordinates, with native readers and explicit bounds. Their simultaneous zeros
at parameter roots correspond bijectively to the actual real and complex
critical samples. Native zero sign-pattern counting computes the exact number
of real critical samples. Dense binary ordinal labels now cover exactly these
samples, with native validity and rational-cut comparisons on their common
parameter. Source-derived dyadic cells have cut counts equal to the sample rank
and rank plus one; their precision and numerator-size allowances have native
binary writers. The potentially long dyadic numerators are not serialized.
Selected derivative-sign moments now sum over exactly these filtered sample
roots, using native coefficient readers and streamed sign-pattern counts.
Their full Thom signatures separate the samples, and monomials with support
bounded by the existing short label width span all rational-valued functions
on them. Short binary records realize every spanning monomial. Their native
Gram entries sum over the filtered samples, and prefix-rank queries select a
basis with native access to each short record. Native weighted moments and
Gram determinants now
select injective integer descriptors for the actual samples. Their serialized
words have a unary polynomial length bound, native validity, and native ordered
enumeration covering exactly one full sample per ordinal below the actual
count. Two native determinant-coefficient signs now recover arbitrary supplied
parameter-polynomial signs at an actual-sample descriptor or hash-order ordinal.
Descriptor validity and the exact sample count guard the native PSPACE sign
languages. Test polynomials supply native modular readers and binary degree
and mass bounds; no point-sign or moment oracle is assumed.
Indexed tests preserve this same descriptor frame while varying the test
polynomial. Native numerator and denominator readers recover the signs of
every actual sample coordinate, with guarded descriptor and coordinate-index
languages and a hash-order ordinal reader. Coordinate index words are
normalized before selecting the rational coordinate polynomial.
Native rational substitution now also evaluates supplied encoded arithmetic
terms at these samples, using zero beyond the actual tuple dimension.
Boolean circuits evaluate arbitrary supplied formulas with these native atom
decisions. Their guarded descriptor and ordinal languages give native PSPACE
formula-marking queries on the actual sample set.
Actual sample descriptors now also serve as algebraic bases for bivariate
slices. Native coefficient signs, actual degrees, signed principal tests,
pseudo-remainder seeds, and Tarski queries preserve the descriptor while
attaching query records. Unit and squared moments give native distinct-root
and prescribed-sign counts in these fibers. This backend retains exactly
the selected actual sample, with no assumed degree stability.
Native rational-coordinate families now free one coordinate of an actual
sample while keeping all the others fixed. Native term substitution gives
their line polynomials with derived bounds; all coordinate denominators stay
nonzero. Native PSPACE zero-existence queries validate the descriptor and
free coordinate, including terms vanishing on the entire line.
Arbitrary contiguous blocks now have multivariate term families with native
collected-coefficient readers. Derived exponent widths prevent collisions
between free variables, and degree and coefficient-mass bounds have native
binary controls. Signs and zeros agree with the term throughout the block;
freezing its first variable at the sample value agrees with the smaller block.
Native modular readers now construct the spatial critical equations of these
block polynomials, with degree and coefficient-mass controls derived from the
original term and candidate direction width. Only spatial variables are
differentiated; the actual sample parameter stays fixed. Specialization gives
the exact critical equations of the actual lower-dimensional polynomial slice.
Invalid pivots and rows, including empty blocks, return zero. Finite regular
child samples over the actual parent are constructed below.
The original parent parameter is separable, so its derivative is nonzero at
every root. A constructed joint integer system retains that parameter equation
alongside the spatial critical rows, with common native degree, mass, exponent,
and label controls. Its native coefficient reader uses a spatial mask for the
parent row and guarded width conversion for critical rows. Joint regularity
at a parent root is exactly spatial regularity; the parent contributes no new
singularity. The regular candidate subset is finite with the derived label
bound even if other roots form positive-dimensional sets. Regular critical
points over actual sample parameters are included in that family.
Concrete nonzero integer equations now annihilate every coordinate of these
regular candidates. Their degree and coefficient-bit allowances have native
binary controls. Native augmented-row, implicit Macaulay, determinant, and
lowest-coefficient readers compute their modular coefficients directly from
the original joint source. This construction does not require regularity or
finiteness of the other parent fibers.
The indexed coordinate equations now feed a native exact-degree preparation
and a balanced primitive-element tree. Their child parameter is separable,
with native coefficient readers and bounds for the parameter and rational
coordinates. Every regular joint candidate is recovered with nonzero
denominators, and distinct parameter roots decode to distinct tuples.
Filtering by the joint equations and regularity gives an exact bijection
with the regular candidates, retaining their finite cardinality bound.
Native univariate tests now impose all joint equations on child parameter
roots. They preserve zeros and signs through fixed even denominator powers,
with derived binary bounds and native coefficient readers. Their exact
filtered-root count and existence language are native PSPACE constructions.
The joint Jacobian now has native partial-derivative and determinant readers,
source-derived bounds, and an exact univariate regularity test. Counting
equation roots minus singular roots gives a native exact count and PSPACE
existence decision for regular joint candidates, without an all-roots-regular
promise. Arbitrary native sign-pattern counts and sparse sign products now
run on precisely these regular roots. Parent derivative probes pull back
through the retained rational coordinate with unchanged signs; agreement
of all derivative signs identifies exactly the intended parent. Selected
parent-sign patterns and moments have native readers and bounds. The regular
child parameter's derivative signs now separate its roots. Short sparse sign
records span all root functions; their native Gram rank equals the regular
child count. Native prefix-rank searches select short records forming a basis,
with one record read at a time. Native selected triple moments and modular
weighted sums now construct a Gram-pencil determinant. Its distinct-root
count tests injectivity, and native bounded search selects separating hash
parameters after computing the regular-child count internally. The resulting
signed integer descriptors are injective and have a source-derived unary
length bound. Native rational cuts now count their values below, at, and
above a threshold. Native hash-order enumeration is bijective with the
regular joint candidates, and a PSPACE validity test rejects noncanonical
words and gives each accepted word a unique candidate. Native determinant
probes now read polynomial signs at these labels. Binary-indexed probes keep
the original root set, basis, and hash fixed. Comparing all parent derivative
signs with a binary-counted scan gives a native PSPACE test selecting exactly
the regular children over the specified actual parent. Both descriptors are
validated. The selected finite geometric samples are exactly the regular
spatial critical points over that parent. On a compact regular slice, a
normalized direction whose critical points are all regular makes every point
reachable from a sample with an accepted short label. Constructing the
recursive sources and cover remains open. The selected children now
surject onto slice components and bound their number. Native pair scans
charge descriptor enumeration, actual-parent selection, and a supplied
slice-path procedure, reducing whole-slice connectivity to that procedure.
Original arithmetic terms now have native sign queries at these selected
children. Two even denominator clearings retain the parent coordinates
outside the free block and insert exactly the child point inside it. Both
labels and their parent relation are validated; arbitrary source records,
malformed term fallback, and unused coordinates retain total semantics.
At an actual parent, the cleared slice polynomial is a positive constant
times the original frozen-coordinate term polynomial. Its whole critical
zero set and analytic regularity are preserved, including singular and
positive-dimensional sets. The native child-pair reduction therefore also
applies directly to the original term's slice and recursive path predicate.
Shared block circuits now give a native regularity validator for the
normalized first-coordinate critical system under generated real formula
constraints. Every kernel chart is checked; neither finiteness nor a
singularity-testing oracle is assumed. Formula witnesses remain independent
of every circuit auxiliary. Its specialization is exactly the original
frozen-coordinate polynomial. Generated parent constraints now include the
actual selected sample circuit, real-input guards, and zero-extension links.
Every actual parent and arbitrary free tuple admit witnesses. Acceptance
of the resulting native validator is exactly critical regularity of every
actual-parent slice, without supplied labels or a finiteness promise.
Finite families of pure-power-leading sources now have one bounded common
direction under explicit regularity over coefficient-field extensions. The
family size multiplies the integer-grid allowance and adds only its bit
length to the record width. The actual parent count bound gives short common
records with native readers. Native bounded search now tests every critical
root over every actual parent and succeeds under those source hypotheses.
The selected record has native readers and a normalized packet for the
existing child-source writers. Its acceptance supplies the original-slice
critical-regularity premise. Applying the source hypotheses to the recursive
sources and constructing the recursive cover remain open.
Shared-circuit block validation now also accepts the actual constructed full
regular source, retaining its binary powers and native program bounds. Its
generated parent constraints give exact critical-regularity validation over
all actual parent samples. Every contained free block inherits the source's
pure-power leading form and lower-degree bound; frozen pure powers contribute
only a constant. Slice regularity does not follow from this shape: critical
endpoint slices can still be singular and require separate treatment.
Native bounded direction selection now uses the actual shared source and
its derived shape and degree bounds. A contained block needs coefficient-field
slice regularity for success; the unfrozen initial source derives that
regularity. Native readers and selected kernel-query writers retain the same
source, parent family, and chosen direction. Shared-source child descriptors
and the recursive cover remain required.
Full-source block coefficients now use dense monomial ranks and the existing
modular source reader, followed by fixed even denominator clearing. Native
coordinate codes have independent source-derived widths. Exact multivariate
coefficient recovery and degree/mass budgets are proved. At every actual
parent, specialization is a positive constant times the same shared-source
block used by the validator. Its zero set, critical roots, and both regularity
predicates are preserved, including singular roots. Child critical and joint
equations now have native coefficient readers, including space-computed
directions, and common degree, mass, exponent-width, and label bounds.
Their joint roots and regularity at actual parents agree with the original
block critical system. Regular candidates have the derived finite label
bound without an all-roots-regular premise. Native nonzero coordinate
eliminants now feed exact-degree preparation and a separable child parameter,
with native rational coordinates and derived bounds. Every regular critical
point of the original block has a unique parameter recovering its complete
tuple. The complete recursive cover remains required. The selected-direction
adapter supplies these
child sources, charging the native search in their coefficient readers.
Accepted records give regularity and unique parameters for all actual-parent
critical roots. Contained blocks use slice regularity for selection success;
the initial whole source supplies success without a separate certificate.
Native joint-equation and Jacobian filters now characterize regular child
parameters. Exact counts and PSPACE existence decisions charge the source,
coordinate, derivative, determinant, and selected-direction readers.
Signed queries exclude singular contributions. Parent derivative-sign probes
preserve the retained coordinate, and their full signature identifies its
root. Selected-sign moments are native; candidate fibers may be singular.
Sparse records, native basis and hash selection, and determinant cuts now
give canonical bounded child descriptors. Validity is in native PSPACE,
enumeration covers exactly the regular joint candidates, and accepted words
name unique tuples. Every regular original block critical point has exactly
one valid bounded descriptor; accepted selected directions cover all of
their actual-parent critical points, including the initial whole source.
Native polynomial and binary-indexed sign readers now operate at these
descriptors. Parent validation and a binary derivative-sign scan select
exactly the specified actual parent. Accepted words name unique finite
samples in bijection with the original block's regular critical points over
that parent. Selected directions cover all its critical points, with native
valid bounded words; the initial whole source supplies success itself.
Bivariate fibers over actual samples now have short ordered root labels with
native validity. Their derivative signatures separate the roots; short sparse
records span all root functions. Native record moments and Gram entries
preserve both the actual sample descriptor and its original record, and the
Gram rank equals the distinct child-root count. Native prefix-rank scans now
select short records forming a basis on those roots. Selected Gram, triple,
and derivative-weighted moments include the native row searches in their
space bounds, with no supplied basis table. Native short separating hashes
now enumerate every distinct child root in hash order. Two native determinant
signs recover each binary-indexed derivative sign at those roots, with guarded
PSPACE sign languages rejecting invalid bases and ordinals. Native rank
conversion orders the child labels by their real coordinates. Arbitrary
bivariate tests and their binary-indexed derivatives now have native signs
at these ordered roots. Native one-sided signs agree throughout intervening
cells for zero or factor tests. Constructed coordinate-line term queries
evaluate the original term on the actual sample tuple with its free coordinate
updated, with native coordinate and child-label validation. Indexed factors
now construct a zero-aware root product at that same sample. Its ordered
point cells and gaps, including exterior rays and rootless fibers, give an
accessible sign-invariant cover with native labels, signs, and incidence.
Boolean sign circuits select the actual solution-set cells; native graph
queries decide fiber connectivity and cell-label paths, with validation of
the parent descriptor and endpoint widths. Original formulas in rational
coordinates now have these native connectivity and path queries over actual
samples, with denominator guards excluding poles. For constructed coordinate
lines, the denominators never vanish and the queries concern exactly the
original formula on the updated sample tuple. A coordinate-line embedding
transfers both connectivity and paths to the formula's intersection with
that line in tuple space. The free coordinate is validated as well.
Native root-sign counts now locate arithmetic endpoint values in the same
cell cover. Fresh-variable comparison polynomials are constructed from the
endpoint terms and original sample readers. Point path queries compute both
endpoint labels internally and reject endpoints outside the solution set,
including excluded endpoints queried against themselves. Their correctness
packets give paths in the actual formula line in tuple space.
Constructing new sample bases
recursively and assembling the full higher-dimensional cover remain required.
Native real critical-sample queries test these
exact equations with arbitrary independent formula witnesses. Both selected
sample-circuit serialization and constrained sample feasibility compose with
the native direction selector in polynomial space. Two independently varying
sample circuits detect collisions of a weighted projection. Native bounded
search selects polynomial-length binary weights separating every sample;
the exact pair queries charge both direction and separator selection.
A concrete nonzero integer Macaulay polynomial now annihilates every selected
sample projection. Its degree and coefficient-bit bounds have native binary
controls. Ordered real roots give unique fixed-width sample labels with exact
mathematical decoding. Modular specialization of the large powers of two now
gives a polynomial-sized term for the exact integer regular source modulo each
queried modulus. Collected coefficients, coordinate rotation, and derivative
readers give native polynomial-space access to the full source and its actual
selected critical equations, including direction selection. The complete
homogeneous projection system now supplies an implicit integer Macaulay matrix.
Native determinant coefficients and binary bounded zero tests select its first
nonzero characteristic coefficient, giving modular access to the actual
projection polynomial with both record searches charged in space. Distinct real
root counts and counts below signed rational cuts now have native space bounds.
Fixed-width root-label comparisons with these cuts agree exactly with the
selected samples' projections, including the polynomial's extraneous roots.
Rational isolating certificates now identify an actual sample with the requested
label and additional formula witnesses, rejecting extraneous roots. Their checker
has a native space bound, every matching sample has a certificate, and acceptance
identifies a unique sample. An explicit separation bound now fixes a common
dyadic isolating grid, including repeated projection roots. Its precision and
grid-index bit allowance have native binary controls, and every matching sample
has an accepted certificate on that grid. Constructing the required endpoint
digits within polynomial space remains open. As a symbolic alternative,
derivative-sign signatures uniquely identify the actual samples, including
repeated projection roots. Binary-indexed iterated derivatives have native
modular coefficient readers and uniform degree and mass bounds. Sign patterns
of polynomially many chosen derivative features have native
root-count and realizability tests, including extraneous projection roots.
Sparse sign monomials span all rational-valued functions on the projection roots;
their support is bounded by the polynomial label width and their exponents
by two. Product Tarski queries compute their moments in native polynomial space.
Fixed-width, unit-padded factor records now represent every required sparse
monomial. All records form a canonical spanning matrix; its Gram matrix has
rank equal to the number of distinct projection roots. Its integer entries
have native polynomial-space evaluators and explicit magnitude bounds, and its
dimension has a native binary control. Native characteristic-coefficient zero
scans compute every row-prefix rank. Symmetry identifies the characteristic
trailing degree with nullity, including empty and singular matrices. Bounded
rank searches select exactly one row for each rank number; these rows form a
basis of all rational root functions and distinguish every projection root.
Their Gram entries have native polynomial-space evaluators that include the
row-selection searches.
One bounded prime and parameter give separating residue labels with a native
polynomial width control. The corresponding integer weighted sums also have
polynomial bit bounds. Their weighted Gram pencil has the full distinct-root
count exactly when the sums separate all projection roots. Native triple
moments and streamed weighted entries supply its coefficients, with uniform
degree and coefficient budgets. A native real-root counter tests separation;
bounded search computes separating parameters after computing the actual
root count. The resulting integer hash is injective and has polynomial bit
length. Native rational-cut queries test an individual hash and count hashes
below it. A native signed-value enumerator covers every projection root
bijectively for valid ordinals. Moments weighted by one derivative sign
have native readers. Native modular determinant coefficients and bounded CRT
sign extraction recover that sign at an enumerated hash, with a proved nonzero
denominator. Short root ordinals enumerate all distinct realizable signatures;
a native polynomial-space reader returns any indexed derivative sign without
storing the complete signature. Orders above the degree bound return zero.
An ascending one-bit Thom-sign scan compares two labels in real order. Native
comparison counts compute their geometric root ranks, and bounded search
inverts those ranks. Derivative signs can therefore be read directly at each
real-order root index, consistently retaining extraneous projection roots.
Arbitrary implicit integer-polynomial tests have native sign queries at those
roots, using only their original modular coefficient readers and binary degree
and mass bounds. Selected-basis moments and determinant probes are computed
internally; rational-cut comparisons are a concrete instance.
Implicit bivariate polynomials also have native coefficient signs, actual
degrees, zero-polynomial flags, and leading signs after specialization at an
ordered algebraic root. These queries permit degree drops and reuse the
original bivariate modular readers. Signed principal-subresultant queries
compute both actual degrees internally and specialize parameter-polynomial
determinants at the same ordered root. Fixed even pseudo-remainder iterates
over parameter polynomials also have native bivariate coefficient readers.
The symbolic head degree may exceed the declared reduction degree.
Algebraic-slice Tarski queries and their zero, positive, and negative decisions
are native. Actual degrees, derivative products, bounded seeds, principal
signs, and descending statistics are computed from the original modular
bivariate coefficient readers, without a symbolic-degree stability assumption.
Three scalar Tarski moments give native distinct-root and single-sign counts
in algebraic fibers. Their roots have ordered binary labels bounded by the
original outer degree, with native validity and rational-cut comparison
deciders. The comparisons preserve the chosen base root and count repeated
fiber roots once.
Nine internally computed product moments also count two simultaneous sign
constraints. In particular, native queries count roots of a slice equation
below a rational cut where another slice polynomial has a prescribed sign.
Binary-indexed outer derivatives have native bivariate coefficient readers
with uniform parameter-degree and mass bounds. Their algebraic-slice moments
and single-sign counts are native. Derivative signatures distinguish all
distinct fiber roots, and sparse sign monomials of logarithmic support span
every rational-valued root function. Native indexed bivariate product readers
now supply sparse derivative-product moments from the original coefficients.
The feature count is polynomially bounded, while derivative orders remain
binary; the computed integer is the exact sign-monomial sum over distinct
fiber roots. Fixed-width records of polynomial length span every rational
fiber-root function. Their full Gram matrix has rank equal to the distinct-root
count; concatenated record moments give native entries on all raw base queries.
Native prefix-rank scans select one basis record at a time. The selected rows
span all fiber-root functions and distinguish every pair of roots; native
selected-Gram entries recompute both row searches. Triple and derivative-weighted
moments supply native integer Gram pencils and pointwise probes. Bounded native
search chooses short separating integer labels, with the actual root count
computed internally. Native cut queries enumerate these labels in hash order;
two determinant-coefficient signs recover one derivative sign at the denoted
fiber root. Every realizable signature receives a short ordinal, without storing
the full signature. Streamed Thom comparisons compute real-order ranks; native
bounded search converts each geometric root ordinal into its hash ordinal and
reads derivative signs at exactly the original ordered fiber root.
The same determinant probes now read arbitrary bivariate polynomial signs at
these roots from the original coefficient readers. Their native sign languages
reject invalid fiber ordinals.
Native derivative scans also compute either one-sided sign at these roots,
including singular endpoints. A right-sided query gives the sign on the entire
interval between consecutive roots when the test is zero or divides the
specialized root polynomial. The validated cell-sign languages are in native
PSPACE and require no nearby rational sample or full Taylor expansion.
For indexed bivariate tests, a native zero-aware product now constructs their
common root polynomial. Factors becoming zero at the selected algebraic base
point are replaced by one. At valid base roots the product is nonzero and its
real roots are exactly the union of the factor roots. Its coefficients and
distinct-root count are native, with explicit binary bounds. Uniform indexed
queries compute each test's sign on intervening cells; their native languages
validate both factor indices and product-root ordinals.
The product roots now construct a complete finite real-cell cover: root
singletons, all intervening gaps, both exterior rays, and the whole line when
there are no roots. Every factor sign is constant on every cell. Restricting
these cells to any predicate of the factor signs gives an accessible cover of
the actual solution set, with both connectivity tests transferred to its
relative frontier graph. Explicit short cell labels have native validity
checking, including base-root validation. Native incidence tests validate both
labels and compute the exact point-gap neighbor relation. Relative incidence
retains precisely those edges whose two cells are present in the solution set.
Native factor-sign readers now cover point cells, both rays, every interior
gap, and the whole line in rootless fibers. Their validated languages reject
invalid base roots, factors, and cell labels. Binary-counted native scans select
the cells where every factor has a requested sign, including the common zero
set. Unused words denote empty pieces in a constructed bit frontier cover.
The native graph algorithm decides whole-set connectivity and paths between
labeled cells in these actual solution sets, including empty systems and
singular roots. Endpoint widths and algebraic base validity are checked.
Native Boolean circuits also select cells by arbitrary combinations of factor
signs. Gate metadata is read from the original source; atom decisions use the
native cell-sign routine. Selection is exactly nonemptiness of the restricted
cell in the circuit-defined solution set. Its constructed native incidence
graph now gives PSPACE decisions for whole-set connectivity and paths between
labeled cells, with base and endpoint validation. Original formula syntax now
has native indexed gate readers, using reverse bracket positions. Atomic terms
and requested signs are preserved, and root-gate truth is proved equivalent to
the original formula. Malformed inputs use the falsum view. Native formula
extractors also support larger source records. Matching atom polynomial
families now evaluate the preserved terms in indexed bivariate coordinates,
with derived degree and mass bounds and native coefficient readers.
Specialization identifies their Boolean-selected cells with the original
formula's actual solution set. Rational-coordinate atoms now use fixed even
denominator powers, with native readers and derived bivariate bounds.
Denominator roots refine the cells, and a native guard circuit excludes every
pole. Whole-set connectivity in these guarded rational coordinates has a
native PSPACE algorithm. Constructing the full recursive coordinate
families and query records remains required.
The recursive connection tests remain open.
Constructing the complete recursive cover remains required.
Component-preserving reduction from arbitrary Boolean inputs and singular
endpoint slices and the full recursive query
encodings remain required.
Each sweep fiber is homeomorphic to its polynomial slice in one fewer
coordinate. Properness and regularity pass to this lower-dimensional equation.
Dimension-zero connectivity algorithms are proved, and both connectivity
tests for arbitrary Boolean formulas in one coordinate have native
polynomial-space algorithms, including singleton endpoint validation.
The effective semialgebraic roadmap construction is not yet
supplied. In particular, neither
`Connectivity.pointLanguage` nor `Connectivity.connectedLanguage` has a PSPACE
membership theorem here.
-/
