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
  compute the actual source partial derivatives. Certificate validity is
  proved equivalent to
  excluding normalized affine Jacobian-kernel roots and roots of the explicit
  pure-power infinity system. This removes determinant homogenization from
  the required query writers. Infinity charts have native PSPACE tests using
  shared binary powers and actual fixed-width record readers. Affine charts
  expand into explicit gradient and Hessian kernel sums. Shared Hessian copies
  and kernel-row arithmetic form complete normalized critical-kernel queries,
  with exact semantics and native PSPACE tests for compiled source terms.
  Sampled-source circuits now compute the frozen low term, full pure-power
  sum, and dyadic regularization with native encoders and kernel tests. Their
  exact finite-coordinate identity identifies them with the Fermat certificate.
  The native affine and infinity tests now check its original validity
  predicate. A bounded search selects a valid direction-and-sample record for
  the constructed regular integer source; no validity or direction oracle is
  assumed. The component-preserving recursion and its query writers remain
  required. For encoded low terms, normalized syntax size now supplies the
  degree and mass controls used by record selection; their variable bound
  suffices for its geometric correctness.
- Transfers from bit-indexed covers to the graph algorithms. For
  formula-defined pieces, the completed ETR theorem supplies nonemptiness and
  overlap tests, given polynomial-time writers for the queries. A
  polynomial-space scan locates pieces containing the described endpoints.
- Component preservation from compact zero sets to a dyadic sublevel, for
  nonnegative polynomial energies with compact sublevels. Bounded critical-value
  annihilators cover singular and positive-dimensional critical loci, and the
  tolerance exponent has native polynomial-time computation. Two pure-power
  slack coordinates preserve sublevel components and regularity. Original
  zero-set path recovery and the full Boolean reduction remain required.
  Within a supplied radius, polynomial zeros now have a constructed compact
  energy and a proper regular pure-power source preserving components between
  lifted original points. A shared sampled source writer computes its coefficients
  from binary exponents. Its exact sampled polynomial identity supports
  native affine/infinity validation and bounded record selection; the selected
  sampled source is serialized in native polynomial space.
  The full varying-coordinate source and its marking polynomial now also
  have native polynomial-time shared-circuit writers, with exact geometric
  identities, regularity and properness in their actual coordinate order.
  Native real-input circuit tests now characterize source and marked points,
  including Boolean coordinate constraints in the same assignment. Their
  polynomial-space certificates charge the actual shared-circuit writers.
  A disjoint wire layout also permits arbitrary existential formula witnesses
  without collisions with circuit auxiliaries.
  Input-link ports restore the original coordinate order. Singleton endpoint
  formulas describe exact marked projection fibers, and native bounded search
  locates a piece meeting such a fiber when the pieces cover it.
  Piece intersections now share the full source point while retaining separate
  formula witnesses. Validity, marking and adjacency have native space
  certificates from the actual source and formula writers.
  Full-source critical-kernel charts also have native writers and space tests,
  reading direction scalars from fixed-width binary records.
  Native bounded search selects a full-source direction with no singular
  complex critical points. Both selection and serialization of its critical
  queries have polynomial-space certificates from the actual writers.
  This selected direction has finitely many simple real critical samples,
  meeting every source component. Concrete coordinate eliminants bound the
  sample and component counts by an exponential in a polynomial label width,
  computed natively from unary dimension and binary degree. The complete complex
  sample set now has the same bound, proved using algebraic finiteness of regular
  square-system roots. Native bounded search now selects an integer projection
  record separating all complex samples and their embedded real subset.
  Collision tests use two independent complex sample circuits and compare both
  components. Native Boolean queries expose both real and imaginary coordinates
  and charge the selected direction and separator. Arbitrary bounded weight
  records now have nonzero integer projection equations vanishing at every
  complex sample, with native modular coefficient readers and uniform degree
  and coefficient bounds. Unit records give individual coordinate equations;
  the complex separating projection shares this native backend. A natively
  computed and checked degree table feeds these equations into a balanced
  primitive tree. Its common parameter and rational coordinates recover every
  real and complex critical sample, with nonzero denominators, native coefficient
  readers, and explicit degree and mass bounds. Even denominator powers now
  clear the original critical equations, with native readers and explicit bounds.
  Filtering parameter roots by these equations gives a bijection with the actual
  real and complex critical samples. Native zero sign-pattern counting computes
  the exact number of real samples. Dense binary ordinal labels cover exactly
  these samples, with native validity and rational-cut comparisons on the common
  parameter. Source-derived dyadic cells have lower and upper cut counts equal
  to rank and rank plus one. Their precision and numerator-size allowances have
  native binary writers; potentially long numerators are not serialized.
  Selected derivative-sign moments now have native polynomial-space evaluators
  over exactly these filtered sample roots. Full Thom signatures separate the
  samples, and monomials with support bounded by the short label width span
  their rational-valued functions. Short binary records realize these monomials.
  Native Gram entries and prefix-rank queries select a basis, with native access
  to each short record. Native weighted moments and Gram determinants select
  injective integer descriptors for the actual samples. Their serialized words
  have a unary polynomial length bound, native validity, and native ordered
  enumeration naming exactly one full sample per ordinal below the actual
  count. Two native determinant-coefficient signs now recover supplied parameter-
  polynomial signs at these descriptors and hash-order ordinals. Native PSPACE
  sign languages reject invalid descriptors and out-of-range ordinals. Test
  polynomials supply native modular readers and binary degree and mass bounds,
  with no point-sign or moment oracle.
  Indexed tests now keep the same sample descriptors while varying the queried
  polynomial. Native numerator and denominator readers recover actual sample
  coordinate signs at descriptors and hash-order ordinals. Guarded coordinate
  languages reject invalid descriptors and out-of-range ordinals or indices.
  Redundant high zeroes in binary coordinate indices are normalized.
  Native rational substitution now evaluates encoded arithmetic terms on the
  same samples. Boolean circuits decide arbitrary supplied formulas from these
  atom signs, with native PSPACE marking flags at validated descriptors and
  ordinals. Variables beyond the actual sample tuple are interpreted as zero.
  Bivariate slices can now use these actual sample descriptors as algebraic
  bases. Native actual-degree scans, principal signs, pseudo-remainder seeds,
  and Tarski queries preserve the same sample while attaching query records.
  Distinct-root and prescribed-sign counts in these fibers are native, including
  degree drops and repeated roots.
  Constructed rational coordinate families now free one actual sample
  coordinate while retaining the others. Native term substitution gives line
  polynomials with exact sign semantics and no poles. Native PSPACE queries
  decide whether a term vanishes anywhere on the line, including identically
  zero terms, with descriptor and coordinate validation.
  Arbitrary contiguous coordinate blocks now have constructed multivariate
  term families with native collected-coefficient readers. Fixed-width
  encoding preserves independent free variables, with derived degree and
  coefficient-mass bounds and exact sign semantics at the same sample.
  Freezing the first variable at its sample value agrees with the smaller
  block. Native modular readers now construct the block's spatial critical
  equations, with derived degree and mass bounds. Specialization retains the
  actual sample parameter and gives the same lower-dimensional critical
  system. Invalid pivots and rows return zero, including empty blocks.
  Constructing finite regular child samples remains required.
  Bivariate fibers over actual samples now have short ordered root labels
  with native validity. Their separating derivative signatures have short
  spanning records; native sparse moments and Gram entries retain the same
  sample and original record. The Gram rank equals the distinct child-root
  count. Native prefix-rank scans now select short records forming a basis
  on the child roots. Selected Gram, triple, and derivative-weighted moments
  are native too, with no supplied basis table or rank oracle. Native short
  hashes now label every distinct child root. A streamed derivative-sign
  reader computes one signature entry at a hash-order ordinal; its PSPACE
  sign languages reject invalid bases and ordinals, including for sign zero.
  Native rank conversion now orders those labels by their real coordinates.
  General polynomial-test signs and binary-indexed test derivatives at child
  roots are native. One-sided signs also give signs throughout intervening
  cells for zero or factor tests. Constructed coordinate-line queries read
  original term signs on the updated sample tuple, with coordinate and child
  validity guards. Indexed factors now construct a zero-aware root product
  at the same actual sample. Its point cells, gaps, and exterior rays form
  a finite sign-invariant cover, with native labels, signs, and incidence.
  Boolean sign circuits select cells; native graph queries decide connectivity
  and cell-label paths in that actual fiber. Formula syntax now gives native
  connectivity and cell-label paths in guarded rational coordinates at these
  same samples. Constructed coordinate lines have no poles; their queries
  decide connectivity of the original formula on the updated sample tuple.
  The coordinate-line embedding preserves paths and connectivity in tuple
  space, with descriptor, coordinate, and endpoint validation.
  Native root-sign counts also locate arithmetic endpoint values at the
  actual sample. Constructed comparison polynomials let point path queries
  compute both cell labels internally. Endpoints outside the formula's
  solution set are rejected, including for zero-length paths.
  Recursive sample construction
  and the full higher-dimensional cover remain required.
  Source connectivity is equivalent to pairwise path connectivity of these samples. Their exact
  real critical equations now have native shared-circuit queries with
  independent formula witnesses. Selected sample serialization and constrained
  feasibility compose with direction selection in polynomial space. Independent
  paired sample circuits detect projection collisions. Native bounded search
  selects binary weights giving every critical sample a distinct projection;
  the record length and the entire search have polynomial-space certificates.
  A concrete nonzero integer polynomial annihilates every selected projection,
  with native degree and coefficient-bit allowances. Its ordered real roots
  give unique bounded sample labels and exact mathematical decoding. Native
  access to source and critical-equation coefficients now uses modular
  specialization and polynomial-sized terms, with the actual direction
  selector charged in space. The complete homogeneous projection system now
  supplies an implicit Macaulay matrix. Native determinant coefficients and
  binary bounded zero tests select its first nonzero characteristic coefficient,
  giving modular access to the actual projection polynomial with both record
  searches charged in space. Native counts of distinct real roots and roots
  below signed rational cuts now evaluate ordered root-label comparisons,
  consistently including extraneous projection roots. A native checker for
  rational isolating certificates now identifies the requested genuine sample
  and tests additional formula witnesses, rejecting extraneous roots. Every
  matching sample has such a certificate, and acceptance identifies a unique
  sample. Explicit separation bounds fix a common dyadic isolating grid, even
  with repeated roots. Its precision and grid-index bit allowance have native
  binary controls, and every matching sample has an accepted grid certificate.
  Computing its endpoint digits in polynomial space remains required.
  Symbolically, derivative-sign signatures now uniquely identify actual
  samples, including repeated projection roots. Their binary-indexed derivative
  polynomials have native modular coefficient access and uniform bounds.
  Native tests count roots and decide realizability for polynomially many
  chosen derivative signs, consistently retaining extraneous projection roots.
  Sparse sign monomials now span all rational-valued functions on the projection roots,
  using at most the polynomial label width in distinct features, each to power
  at most two. Their product Tarski moments have native polynomial-space readers.
  Polynomial-length factor records represent these monomials, including unit
  padding. The resulting canonical Gram matrix has rank equal to the number of
  distinct projection roots, with native integer-entry readers, a binary
  dimension control, and explicit entry bounds. Native modular characteristic
  coefficient scans now compute every row-prefix rank. Bounded rank searches
  select a basis of all rational root functions, one row per rank number,
  without storing the row table. The basis distinguishes every projection
  root, and its Gram entries have native polynomial-space readers, including
  the row-selection computations.
  Separating residue labels now have proved polynomial bit bounds: one prime
  modulus and one parameter determine all weights. The associated integer
  weighted sums also have polynomial bit bounds. A weighted Gram pencil has
  the full distinct-root count exactly when these sums separate the roots.
  Native selected triple moments and streamed weighted entries now supply all
  coefficients of that pencil, with explicit degree and coefficient bounds.
  A native real-root counter tests separation, and bounded search computes
  separating parameters after computing the actual root count. These give an
  injective integer hash of polynomial bit length. Native rational cuts now
  test individual hash values and count the values below a threshold. An
  ordered native hash enumerator labels every projection root bijectively.
  Native moments weighted by one derivative sign, modular determinant
  coefficients, and CRT sign extraction recover that sign at an enumerated
  hash. Short root ordinals enumerate every distinct realizable signature;
  a native polynomial-space reader returns any derivative sign without
  storing the complete signature. Orders above the degree bound return zero.
  A native one-bit Thom-sign scan compares labels in real order. Streamed
  comparison counts compute their geometric ranks, and bounded search inverts
  those ranks. Derivative signs can now be read at any real-order root index,
  consistently retaining extraneous projection roots.
  Arbitrary implicit univariate integer-polynomial tests now have native
  sign queries at these roots, given their modular coefficient readers and
  binary degree and mass bounds. The weighted moments and determinant probes
  are computed internally; rational-cut comparison is a concrete instance.
  After specialization at an ordered algebraic root, implicit bivariate
  polynomials have native coefficient-sign, actual-degree, zero-polynomial,
  and leading-sign queries, including degree drops. They reuse the original
  modular coefficient readers. Signed principal-subresultant queries compute
  the actual slice degrees internally and evaluate parameter-polynomial
  determinants at the same root. Fixed even pseudo-remainder iterates over
  parameter polynomials have native bivariate coefficient readers, allowing
  the symbolic head degree to exceed the declared reduction degree.
  Algebraic-slice Tarski evaluation and zero, positive, and negative decisions
  are native. Actual degrees, derivative products, bounded seeds, principal
  signs, and descending statistics are computed from the original modular
  bivariate readers, including degree drops and zero heads.
  Three scalar Tarski moments give native distinct-root and single-sign
  counts in those algebraic fibers. Ordered fiber-root labels are bounded
  by the original outer degree; their validity and comparison with an
  encoded rational cut have native polynomial-space deciders. Repeated
  roots count once, and invalid base or fiber ordinals are rejected.
  Nine native product moments also count two simultaneous sign constraints,
  including roots below a rational cut satisfying a prescribed polynomial
  sign. Product readers and all degree and mass bounds are constructed
  from the original bivariate readers.
  Binary-indexed outer derivatives now have native bivariate readers with
  uniform parameter-degree and mass bounds. After algebraic specialization,
  their Tarski moments and single-sign counts are native. Derivative signs
  distinguish all distinct fiber roots; sparse monomials with logarithmic
  support span every rational-valued root function. Native indexed bivariate
  product readers now compute sparse derivative-product moments from the
  original coefficients. Polynomially many selected derivative tests retain
  binary orders; the answer is their exact sign-monomial sum over distinct
  fiber roots. Fixed-width records of polynomial length span every rational
  fiber-root function. Their full Gram matrix has rank equal to the
  distinct-root count, with native entries computed by concatenated record
  moments on all raw base queries. Native prefix-rank scans select a basis
  one record at a time. The selected rows span all fiber-root functions and
  distinguish every pair of roots; selected-Gram entry queries recompute
  both searches in native polynomial space. Native triple and derivative-weighted
  moments supply integer Gram pencils and pointwise probes. Bounded native search
  chooses short separating integer labels, computing the actual root count
  internally. Native cuts enumerate these labels in hash order. Two
  determinant-coefficient signs recover one derivative sign at the denoted root;
  short ordinals label every realizable signature without storing it in full.
  Streamed Thom comparisons compute real-order ranks, and bounded native search
  converts geometric ordinals to hash ordinals. Derivative-sign queries therefore
  refer to exactly the original ordered fiber roots.
  Native determinant probes also read arbitrary bivariate polynomial signs at
  these roots from the original coefficient readers, rejecting invalid fiber
  ordinals in the sign languages.
  Native derivative scans compute both one-sided signs, including at singular
  endpoints. For a zero or factor test, a right-sided query gives its sign
  throughout the cell between consecutive fiber roots. These validated cell-sign
  languages are in native PSPACE, without constructing nearby rational samples
  or full Taylor expansions.
  An indexed bivariate family now supplies its common root polynomial natively:
  factors specializing to zero are replaced by one. The product is nonzero at
  valid base roots, and its real roots are exactly the union of all factor roots.
  Its coefficients and distinct-root count have native readers and explicit
  binary bounds. Uniform indexed queries compute each factor's sign on
  intervening cells and validate both factor and product-root indices.
  Its ordered roots construct a complete finite cell cover, including root
  singletons, exterior rays, and the whole line for an empty root set. Every
  factor sign is constant on each cell. Any Boolean combination of these signs
  therefore has a constructed accessible cover of its actual solution set,
  with both connectivity tests transferred to its relative frontier graph.
  Short cell labels have native validity checks, including base-root validation.
  Native incidence tests compute the exact point-gap neighbor relation and
  validate both labels. Relative incidence retains the edges whose two cells
  are present in the solution set, so excluded endpoints cannot join gaps.
  Native factor-sign readers cover every cell, including both rays and rootless
  fibers, and reject invalid factor indices and cell labels. A binary-counted
  native scan selects cells where every factor has the requested sign, including
  the common zero set. Unused words denote empty pieces in a constructed bit
  frontier cover. Native PSPACE algorithms decide whole-set connectivity and
  paths between labeled cells of these actual solution sets, with base-root and
  endpoint-width validation. Native Boolean circuits also select cells by
  arbitrary combinations of factor signs, with selection exactly nonemptiness
  in the actual circuit-defined solution set. Constructed native incidence
  graphs give PSPACE connectivity and cell-label path queries for these Boolean
  subsets. Original formula syntax now has native indexed gate readers and
  proved truth preservation, including nested negations and strict inequalities.
  Malformed words normalize to falsum; FP formula extractors support larger
  source records. Matching atom polynomial families now substitute indexed
  bivariate coordinates into the preserved arithmetic terms, with derived
  degree and mass bounds and native coefficient readers. Their specialized
  signs evaluate the original formula. Rational-coordinate atoms also have
  native coefficient readers and derived bounds. Fixed even denominator powers
  preserve their signs, and a native guard circuit excludes poles, whose roots
  refine the cells. This gives native PSPACE connectivity in the guarded
  rational coordinates. Full recursive coordinate families and query records
  remain required.
  The recursive connection tests remain open.
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
