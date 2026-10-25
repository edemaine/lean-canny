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
