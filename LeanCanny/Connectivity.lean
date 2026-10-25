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
The effective semialgebraic roadmap construction is not yet
supplied. In particular, neither
`Connectivity.pointLanguage` nor `Connectivity.connectedLanguage` has a PSPACE
membership theorem here.
-/
