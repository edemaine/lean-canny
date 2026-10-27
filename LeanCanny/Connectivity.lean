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
root-finiteness assumption. Native real critical-sample queries now test these
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
The complete signature is an indexed function; a polynomial-space representation and
enumeration of its realizable values still require a streamed sign-determination
algorithm. The recursive connection tests remain open.
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
