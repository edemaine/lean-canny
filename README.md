# lean-canny

A Lean formalization of the theorem that the
Existential Theory of the Reals (ETR) is in PSPACE,
or stated in terms of complexity-theory classes: ∃ℝ ⊆ PSPACE.
This theorem is from John Canny's 1988 technical report
[*Some Algebraic and Geometric Computations in PSPACE*](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/6041.html)
(stored in this repo as [`canny-tr.pdf`](canny-tr.pdf)), published as a
[STOC ’88 paper](https://doi.org/10.1145/62212.62257) (pp. 460–467).

The main results in [`ETR/CoercivePSPACE.lean`](LeanCanny/ETR/CoercivePSPACE.lean) are:

```lean
LeanCanny.ETR.etr_mem_PSPACE : LeanCanny.ETR.language ∈ LeanCanny.PSPACE
LeanCanny.ETR.existsReal_subset_PSPACE : LeanCanny.ExistsReal ⊆ LeanCanny.PSPACE
```

These are unconditional theorems for the project's encoded ETR language and
[Complexitylib](https://github.com/cslib-community/complexitylib)'s machine-based PSPACE class. The coefficient algorithms,
metadata preparation, recursive evaluation, and final sign decisions are
constructed internally. The development uses Lean 4.36.0-rc1 with pinned
Mathlib, CSLib, and Complexitylib dependencies.

This establishes the report's ETR PSPACE upper bound. The report's roadmap,
connectivity, and motion-planning algorithms remain outside the completed result.
The proof uses a coercive one-parameter sampling construction; it does not
formalize every intermediate construction in the report verbatim.

The formalization also identifies a [gap in Canny's coordinate-recovery
argument](RESEARCH.md#gap-in-cannys-symmetric-coordinate-recovery): three
collinear solutions can produce a cubic GCD where the construction requires a
linear one, regardless of the projection coefficients. The completed PSPACE
proof avoids this failed step.

For an independently readable, checked statement, see
[`Abstract.lean`](LeanCanny/Abstract.lean). A reader can inspect its definitions
and theorem statements to assess the claimed result; Lean verifies the proofs
through [`AbstractBridge.lean`](LeanCanny/AbstractBridge.lean) and the development.

## Proof outline

1. **Compile ETR to one integer equation.** The binary grammar, normalization,
   and equation compiler have native polynomial-time certificates. Correctness
   covers every bitstring; malformed formulas are rejected. Degree, arity,
   encoded length, and coefficient-mass bounds are derived from the input.
2. **Construct bounded critical samples.** For the compiled polynomial q,
   minimize `q² + s * Σ Xᵢ^(2D+2)` as positive s tends to zero. Its gradient has
   finite fibers for every nonzero s. Bounded integer coordinate annihilants
   give a source-size root radius, so satisfiability is equivalent to eventual
   bounded critical samples with the required residual and penalty bounds.
3. **Compute annihilants and primitive coordinates.** A fixed full Macaulay
   block determinant supplies nonzero coordinate annihilants. Native modular
   readers feed actual integer degree/GCD/direction preparation. A uniform
   recursive symbolic evaluator computes the prepared primitive parameter;
   indexed pair readers and ordered matrix products compute its rational
   coordinates. All child computation costs and malformed metadata cases are
   included in the space certificates.
4. **Decide eventual signs.** Even denominator clearing preserves the sample
   equations and inequalities. Native readers compute the resulting integer
   bivariate queries without storing their expanded coefficients. The
   infinitesimal root/sign decision procedure decides four sign patterns in
   PSPACE. Their union is exactly ETR; closure under polynomial-time reductions
   gives `ExistsReal ⊆ PSPACE`.

Selected entry points:

| Stage | Modules |
| --- | --- |
| Encoding and compilation | [`Grammar`](LeanCanny/ETR/Grammar.lean), [`EquationCompilerFP`](LeanCanny/ETR/EquationCompilerFP.lean), [`Complexity`](LeanCanny/ETR/Complexity.lean) |
| Bounded sample semantics | [`CoerciveSourceSampling`](LeanCanny/ETR/CoerciveSourceSampling.lean), [`CoerciveRootRadius`](LeanCanny/Geometry/CoerciveRootRadius.lean) |
| Actual annihilator and query coefficients | [`CoerciveNativeOriginalResidue`](LeanCanny/ETR/CoerciveNativeOriginalResidue.lean), [`CoerciveQueryCoefficient`](LeanCanny/ETR/CoerciveQueryCoefficient.lean) |
| Native preparation and symbolic parameter | [`CoerciveIntegerPreparation`](LeanCanny/ETR/CoerciveIntegerPreparation.lean), [`CoerciveTableCorrectness`](LeanCanny/ETR/CoerciveTableCorrectness.lean), [`CoerciveParameterCoefficient`](LeanCanny/ETR/CoerciveParameterCoefficient.lean) |
| Coordinates and cleared queries | [`CoerciveCoordinatePairReaders`](LeanCanny/ETR/CoerciveCoordinatePairReaders.lean), [`CoerciveClearedQueryCoefficient`](LeanCanny/ETR/CoerciveClearedQueryCoefficient.lean) |
| Final decision | [`CoerciveInfinitesimalSemantics`](LeanCanny/ETR/CoerciveInfinitesimalSemantics.lean), [`CoercivePSPACE`](LeanCanny/ETR/CoercivePSPACE.lean) |

[`SpaceFunction`](LeanCanny/Computation/SpaceFunction.lean) wraps
Complexitylib's `ComputableTidilyInPolySpace`.
[`SpaceDecider`](LeanCanny/Computation/SpaceDecider.lean) carries membership in
its native PSPACE class. Polynomial-time reductions and all FP controls also
use Complexitylib directly. Space composition charges the original readers;
no free coefficient oracle or execution-time bound on a space-bounded child
is assumed.

## Alternative constructions

The default `LeanCanny` library and `import LeanCanny` contain the completed
coercive ETR proof and formal abstract. The optional `LeanCannyAlternatives`
library is available through `import LeanCanny.Alternatives`; it also imports
the completed result. All source modules retain their existing paths.

The repository also develops Canny's compact tube and generic projection
constructions, projective elimination, finite-root sign feasibility, and
nonsingular tube sampling. These are independently proved ingredients and
alternative samplers. The tube route's effective epsilon/delta/direction and
retained-level choices are unresolved; the completed ETR theorem uses the
coercive route and does not depend on those choices.

Further work includes relating this encoding to other ETR presentations,
proving the NP lower inclusion, and formalizing the report's roadmap and
connectivity consequences. The alternative library remains checked by the full
verification commands below.
See [`RESEARCH.md`](RESEARCH.md) for prior work,
proof details, and the unused tube route's precise gaps.

## Connectivity development

The separate `LeanCannyConnectivity` target (`import LeanCanny.Connectivity`)
develops point-to-point path reachability and whole-space connectivity for
semialgebraic sets. **Neither geometric language has a PSPACE theorem yet.**

The checked ingredients are:

- Formula-based inputs with unary dimension and unique-solution endpoint
  descriptions, including irrational algebraic endpoints. Canonical point and
  whole-space encodings have polynomial-time recognizers.
- An unconditional native PSPACE theorem for singleton endpoint validation on
  canonical point inputs. Inconsistent, nonunique, and out-of-dimension endpoint
  descriptions are rejected, as are malformed bitstrings.
- Native polynomial-space implicit-graph reachability and whole-graph
  connectivity, allowing polynomial-space adjacency and invalid records.
  The transfer applies to accessible frontier covers with nonclosed pieces.
- A finite closed path-cover theorem identifying topological connectivity with
  intersection-graph connectivity.
- A frontier-incidence theorem for finite decompositions whose pieces need not
  be closed. Bounded continuous algebraic curve branches extend to finite
  endpoints, which proves the required boundary accessibility for their arcs.
  Proper regular root projections give complete finite global branches across
  an open interval. Nonzero coordinate equations bound their number by a
  product of degrees; a simultaneous nonzero specialization exists in every
  nonempty open interval.
- A slab-gluing theorem combines those arcs with accessible endpoint-fiber
  covers and preserves paths and whole-space connectivity. Arc-to-slice
  incidence is exactly endpoint membership. Endpoint roots may be singular.
- Explicit polynomial equations have the expected analytic Jacobian. For a
  proper polynomial level function, an integer direction and a nonzero level
  polynomial give regular finite critical fibers outside finitely many levels.
  These choices are proved qualitatively; their input-size bounds remain open.
- Regular compact levels have finitely many path components. Every point can
  reach a critical sample within its own component; one integer direction
  gives finite sample sets covering all components at every retained level.
- Fiber connection between continuous sections of a proper polynomial is
  constant on each connected region avoiding its constructed exceptional
  levels. Critical values outside the chosen region are allowed.
- Saturating the critical branches gives a finite clopen path cover of every
  point in an original regular polynomial slab. Point connectivity and
  whole-slab connectivity reduce to the finite critical samples in one fiber.
  Nonzero coordinate annihilators are constructed for the same chosen integer
  direction, so the indexing branches extend continuously to both endpoints.
- Each saturated component has a compact connected limit in both endpoint
  fibers, including singular ones. A recursive finite accessible slice cover
  joins all its limit points to the extended branch through that slice.
- Recursive slice covers yield clopen path components by finite graph
  saturation. Attaching each interior component to its two endpoint components
  gives a finite closed path cover of the entire original closed slab, with
  both connectivity tests preserved. The final labels form a sum of the
  interior and endpoint label families. Overlap and validity have descriptions
  containing no closure queries. Component membership uses native PSPACE
  reachability once a piece containing the queried point is located.
- Coordinate sweeps on fixed proper polynomial hypersurfaces have constructed
  finite exceptional value sets and local product charts on the retained
  intervals. Their fibers are homeomorphic to proper polynomial slices in one
  fewer coordinate, and regularity passes to those slices. Generic critical
  projections on a fixed level have finite simple roots and coordinate
  annihilators for one integer direction. Uniform specialization constructs
  one integer direction and a finite exceptional set for the whole slice
  family. Its complete spatial critical arcs extend to both endpoints.
  Saturation gives a clopen path cover of the original coordinate slab;
  overlap tests are connections in one lower-dimensional slice. Recursive
  endpoint component covers complete the closed slab. Concrete coordinate
  eliminants now have bounded spatial and parameter degrees, coefficient
  bits, and specialization factors, also for singular finite fibers over
  algebraically closed extensions. Constrained coercive limits bound finite
  coordinate images even when spatial fibers have positive dimension. These
  bounds construct exceptional factors for regular integer hypersurface
  sweeps and integer systems with finitely many singular parameter values.
  Integer parameter substitution preserves evaluation and spatial Jacobians
  with bounded degree and mass. The chosen direction now has a constructed
  bounded regularity factor for its actual parameter-ring critical equations.
  Input bounds for that direction and the full recursive query encodings
  remain open.
  Native coefficient access now splits the parameter exponent block and
  evaluates the actual spatial critical equations from a source reader.
  Derivative guards and direction scalars retain binary encodings of large
  values; recursive records and graph query writers remain required.
  For pure-power-leading hypersurfaces regular over field extensions, the
  direction now has an explicit polynomial bit-width bound and a bounded
  record with native field access. Constructing these hypotheses from general
  Boolean inputs remains required.
- Shared complex arithmetic networks with native polynomial-time compilation
  to real equations and native PSPACE feasibility tests. Binary powers use
  two multiplication gates per exponent bit. These give an exact test for
  the denominator-cleared equation `2^E * p - 1 = 0` appended to a source
  network. A polynomial-time derivative transformation computes formal
  partial derivatives while preserving shared intermediate values. The
  source-term compiler has a quadratic bound on its complete intermediate
  state and constructs its fresh-wire metadata. Its derivative networks
  compute the actual source partial derivatives. The full bad-root query
  networks remain open. Certificate validity is now proved equivalent to
  excluding normalized affine Jacobian-kernel roots and roots of the explicit
  pure-power infinity system. This removes determinant homogenization from
  the required query writers. Infinity charts have native PSPACE tests using
  shared binary powers and actual fixed-width record readers. Affine charts
  expand into explicit gradient and Hessian kernel sums. Shared Hessian copies
  and kernel-row arithmetic form complete normalized critical-kernel queries,
  with exact semantics and native PSPACE tests for compiled source terms.
  Constructing the sampled Fermat source circuit remains required.
- Transfers from bit-indexed covers to the graph algorithms. For
  formula-defined pieces, the completed ETR theorem supplies nonemptiness and
  overlap tests, given polynomial-time writers for the queries. A
  polynomial-space scan locates pieces containing the described endpoints.
- Native recursion base cases: both connectivity tests in dimensions zero
  and one. On the real line, an ETR query detects a missing point between
  two points. Point queries include singleton validation and endpoint
  membership, retaining irrational endpoints and rejecting invalid descriptions.

The missing construction must produce suitable covers uniformly from input
formulas, handle Boolean constraints, singularities and unbounded sets, prove
component preservation, and bound the vertex records and all graph routines.
The regular-slab theorem does not establish this construction. Endpoint
validation is proved separately. Effective endpoint attachment still requires
the recursive slice covers and bounded query writers.
The current cover theorems state these obligations explicitly; they do not
establish them for arbitrary semialgebraic inputs. Empty spaces are accepted
by the whole-space connectivity convention.
The formula-cover interface is a sufficient criterion; the more general
bit-cover interface also permits implicit polynomial-space adjacency routines.

## Attribution and report integrity

The Sturm–Tarski proof adaptation and its changes are documented in
[`STURM_SOURCES.md`](STURM_SOURCES.md).

The report PDF [`canny-tr.pdf`](canny-tr.pdf) is from the
[Berkeley Technical Reports archive](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/Archive/CSD-88-439.pdf).
The downloaded file has 936,246 bytes and SHA-256
`7606d41dea23ac1160562a759c196267906d8aec0f754cd4998fdd14fcd185f8`.
The report retains its original rights; the source-code license does not apply to it.

## Build and verification

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build
```

[`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json)
record the versions used. The default entry point is [`LeanCanny.lean`](LeanCanny.lean).
`lake build` checks the completed coercive proof. To also build the retained
alternative constructions, run `lake build LeanCannyAlternatives`; their entry
point is [`Alternatives.lean`](LeanCanny/Alternatives.lean).
Build the connectivity extension with `lake build LeanCannyConnectivity`.

Import the formal abstract with `import LeanCanny.Abstract`, or build it with
`lake build --wfail LeanCanny.Abstract`. It is also included in the default build.

Complexitylib moved to `cslib-community/complexitylib` from its temporary
`complexitylib2` repository. This project retains the checked revision
`cb1b7ce8`; that revision still declares the Lake package `complexitylib2`.
The dependency URLs use the canonical repository. Updating to the renamed
`complexitylib` package also requires advancing the dependency pins.

For stricter verification:

```sh
lake build LeanCanny LeanCannyAlternatives LeanCannyConnectivity --wfail --iofail
lake env lean scripts/CheckCoreImports.lean
lake env lean scripts/CheckAxioms.lean
lake env lean scripts/CheckAbstract.lean
lake env lean scripts/CheckGrammar.lean
lake env lean scripts/CheckSpaceFoundation.lean
lake env lean scripts/CheckPolyTimeFoundation.lean
lake env lean scripts/CheckConnectivity.lean
```

The core import check enforces the separation from the optional tube route.
The axiom and space audits include all three library targets. The axiom audit checks
declarations in the `LeanCanny` namespace, local Nat
codec extensions, and their transitive dependencies, allowing only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms. The foundation
checks enforce the native Complexitylib time and space interfaces and reject
legacy machine dependencies. `CheckAbstract` also follows public definitions
and statement dependencies to reject hidden implementation references.
