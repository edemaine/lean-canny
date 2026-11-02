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
  Finite regular child samples are constructed as follows.
  The retained parent parameter is separable. A joint integer system now
  combines it with the spatial critical rows, with native coefficients and
  common degree, mass, exponent-width, and root-label bounds. Its Jacobian
  factors into the nonzero parent derivative and the spatial Jacobian.
  Regular joint candidates form a finite family with the derived label bound,
  even when other candidate roots form positive-dimensional sets.
  Constructed nonzero coordinate annihilators now have source-derived binary
  degree and coefficient-bit bounds and native modular coefficient readers.
  Binary-degree homogenization and implicit Macaulay controls retain the
  original joint coefficient costs through determinant and lowest-coefficient
  scans; no finite-root or regularity oracle is supplied.
  The indexed equations now have native exact-degree preparation and feed
  a separable child primitive parameter. Native rational coordinate readers
  recover every regular joint candidate, with nonzero denominators and
  source-derived bounds. Parameter roots encode distinct tuples; imposing
  the joint equations and regularity gives a bijection with the finite
  regular candidates. The joint equations now have native univariate tests
  with exact zero and sign semantics, bounded coefficient readers, and native
  counts and existence decisions for the child parameter roots passing them.
  The joint Jacobian now has native derivative and determinant coefficient
  readers, derived bounds, and an exact univariate regularity test. Subtracting
  singular roots gives native exact counts and PSPACE existence decisions for
  regular joint candidates, without an all-roots-regular promise. Native
  sign-pattern counts and sparse sign products now run on these regular roots.
  Native parent-derivative probes preserve signs through the retained rational
  coordinate, and matching all derivative signs identifies the intended parent.
  Selected parent-sign patterns and moments have native readers and bounds.
  The regular child parameter's derivative signs now separate its roots, and
  short sparse sign records span all root functions. Native Gram entries and
  prefix ranks select short records forming a basis, read one record at a
  time. Native triple moments and modular weighted sums construct a Gram
  pencil whose distinct-root count tests hash injectivity. Native search now
  selects bounded separating hash parameters using the internally computed
  regular-child count. The resulting signed integer descriptors are injective
  and have a source-derived unary length bound. Native rational cuts and
  hash-order enumeration now cover exactly the regular joint candidates.
  A PSPACE validity test rejects noncanonical words and gives each accepted
  word a unique candidate. Native determinant probes now read arbitrary
  polynomial signs at these labels, with binary-indexed tests retaining the
  same root set, basis, and hash. Native parent-derivative comparisons and a
  binary-counted scan validate both labels and select exactly the children
  over the specified actual parent. These labels give a finite family in
  bijection with the regular spatial critical points over that parent. For a
  compact regular slice and a normalized direction with all critical points
  regular, every point can reach a sample with an accepted short label.
  The selected children surject onto slice components and bound their number.
  Native pair scans validate the parent and both children; a supplied path
  procedure on the actual slice then decides whole-slice connectivity.
  Constructing the recursive sources and cover remains open.
  Native arithmetic-term sign queries now evaluate the original tuple with
  the selected child inserted in its free coordinate block. Both rounds of
  even denominator clearing have source-derived degree and mass bounds and
  native coefficient readers. The queries validate both labels and their
  parent relation, retaining total semantics on arbitrary source records.
  Exact positive constant scaling now relates the cleared slice to the
  original term, preserving all critical roots and their regularity.
  The native pair scan consequently reduces original-term slice connectivity
  to paths between selected children under the same geometric assumptions.
  Shared block circuits now validate the normalized first-coordinate critical
  system in native space under generated real formula constraints. Scanning
  every kernel chart detects singular points even in positive-dimensional
  critical sets, while keeping formula witnesses independent of auxiliary
  wires. Generated actual-parent constraints include the selected parent
  circuit, real-input guards, and zero-extension links. The resulting native
  validator accepts exactly when every critical root over every actual
  parent is regular. Eligible finite families of pure-power-leading sources
  now have bounded common-direction records with native readers; the parent
  count bound contributes only its bit width. Native bounded search now
  succeeds under those source hypotheses, testing every critical root over
  every actual parent. Native readers and a normalized packet pass the
  selected record to the existing child-source writers; acceptance supplies
  the original-slice critical-regularity premise. Proving the required source
  shape and regularity over field extensions for recursive inputs, and
  constructing the recursive cover, remain open.
  Shared-circuit block validation now applies to the actual constructed full
  regular source, retaining binary powers and native program bounds.
  Generated actual-parent constraints give exact critical-regularity tests
  for its blocks. Contained free blocks inherit the pure-power leading form
  and lower-degree bound. Frozen pure powers contribute only a constant;
  slice regularity remains separate, including at singular endpoint slices.
  Native bounded direction search now uses this shared source with derived
  shape and degree bounds. Coefficient-field slice regularity suffices for
  success; the unfrozen initial source derives it. Native selected-record
  readers and kernel-query writers preserve the same source and parent
  family. Child descriptors for the shared source remain required.
  Shared-source sample blocks now have native multivariate coefficient
  readers with derived degree and mass budgets. Fixed even denominator
  clearing preserves the exact source block up to a positive constant at
  every actual parent, retaining singular critical roots and regularity.
  Native critical and retained-parent joint coefficient readers now accept
  space-computed directions. Their degree, mass, exponent-width, and label
  bounds are derived. At actual parents, joint roots and regularity agree
  with the original block critical system, including singular roots.
  Regular candidates have the derived finite label bound. Native nonzero
  coordinate eliminants now feed exact-degree preparation and a separable
  child parameter with native rational coordinates and derived bounds.
  Every regular critical point of the original block has exactly one child
  parameter recovering its full tuple.
  A native selected-direction adapter now supplies these child sources and
  includes the direction search in their coefficient readers. Accepted
  records give unique parameters for all actual-parent critical roots.
  Contained blocks still need slice regularity for selection success;
  the initial whole source supplies success without a separate certificate.
  Native joint-equation and Jacobian filters now characterize regular child
  parameters, with exact counts and PSPACE existence decisions. Their native
  space bounds include the selected direction. Signed queries subtract
  singular contributions. Parent derivative-sign probes preserve the retained
  coordinate, and their full signature identifies its root. Selected-sign
  moments are native too.
  Native sparse-record basis and hash selection now construct canonical
  bounded child descriptors. Their validity is in PSPACE, and native
  enumeration covers exactly the regular joint candidates. Accepted words
  name unique tuples. Every regular original block critical point has one
  valid bounded descriptor; accepted selected directions cover all of their
  actual-parent critical points, including the initial whole source.
  Native polynomial and binary-indexed sign readers now operate at these
  descriptors. Parent validation and a binary derivative-sign scan select
  exactly the specified actual parent. Accepted words name unique finite
  samples in bijection with the original block's regular critical points over
  that parent. Selected directions give valid bounded words for every
  critical point, including on the initial whole source.
  Contained full-source blocks now inherit properness and compact real levels,
  including singular levels and empty blocks. Critical-system regularity also
  implies hypersurface regularity. Every point of an accepted selected slice
  can reach a sample with a valid bounded descriptor; the finite actual-parent
  samples bound its component count. Native pair scans charge enumeration,
  parent selection, and a supplied PSPACE path language. They transfer its
  correctness to whole-slice connectivity, including empty fibers. The initial
  whole source supplies all geometric sampling premises.
  A generic native rational-coordinate interface now accepts derived children
  as parents of the next full-source block. Ambient coordinates outside the
  sampled block are composed through the retained parent parameter; every
  coordinate has the exact original assignment and nonzero denominators at
  actual child parameters. Next-stage coefficients include these composition
  costs and have derived degree and mass bounds. Positive scaling preserves
  zero sets and critical regularity, and contained next-stage levels are
  compact. Generalized native critical and joint systems now retain a
  separable parent parameter, with exact root and regularity semantics.
  Native coordinate eliminants and primitive parameters give unique encodings
  for every regular next-stage critical point. The resulting ambient rational
  coordinates and separable parameter supply another native joint input,
  preserving ancestor coordinates and nonzero denominators at actual samples.
  Generalized native equation and Jacobian filters count exactly the regular
  candidates. Canonical bounded descriptors, enumeration, and polynomial sign
  readers now work over these rational parents. A named-parent interface
  validates the entire ancestry: a native derivative-sign scan identifies the
  retained parent, and each actual child supplies the same interface for the
  next stage. Names append ancestry without repeatedly doubling its length;
  the zero seed has an unconditional native certificate. This proves closure
  for each fixed stage. Direction selection, singular endpoints, and uniform
  bounds for input-dependent recursion remain open.
  A flat triangular polynomial tower now preserves uniform row degree and
  coefficient-mass bounds at arbitrary depth. At depth at most the ambient
  dimension it uses at most its square in variables. Its derivative is
  invertible exactly when every frozen stage is regular. Explicit finite
  indexing now preserves roots and Jacobians. Actual flat critical stages use
  the original full source, with linear constraints copying frozen coordinates.
  Their uniform degree, mass, and single-elimination budgets have native
  controls. A native plan check enforces contained nonempty blocks and pivots
  inside them. Native readers handle source blocks, critical differences, and
  linear copy rows. The complete indexed tower now has a native coefficient
  reader with derived exponent width, exact row semantics, and charged
  direction computation. Adding one dummy coordinate fixed at zero preserves
  roots and regularity, including the empty seed. Native coordinate elimination
  now uses the whole flat system, with derived degree and coefficient-bit
  budgets and no ancestral coefficient oracle. These equations now feed a
  balanced primitive construction with native rational coordinate readers and
  equation/Jacobian test polynomials. Accepted parameters correspond exactly
  to regular roots of the original tower, with native uniform budgets and a
  polynomial label-width bound. Native counts, canonical bounded descriptors,
  ordered enumeration, and polynomial sign readers are now constructed.
  Fixed-width vertex words name exactly the regular original roots.
  Separate affine-height critical stages now constrain actual linear heights,
  retaining ambient coordinates and Lagrange multipliers. Regular stage roots
  are critical on their slices. On regular slices, constrained maxima yield
  stage roots when the new height is independent of the old ones. Every point
  of a compact regular affine slice can reach such a root in its component.
  A shared ancestry tower supports old heights and midpoint levels with
  uniform row bounds and at most n*(2*n+1) variables. Signed direction and
  ancestral level records now have native controls and uniform budgets.
  Native scalar, source-block, derivative, and weighted-height coefficient
  readers now supply complete indexed row dispatch, including the dummy row
  at zero depth. Native homogenized rows and coordinate annihilators for the
  entire affine tower are constructed too, with derived uniform budgets.
  A reusable square-system sampler now feeds these exact equations into the
  balanced primitive construction, equation and Jacobian filters, regular-root
  counting, and short native labels. Removing the zero dummy gives a bijection
  with regular roots of the entire original affine tower. Native multivariate
  polynomial sign tests retain the same selected root and charge their readers.
  Full-tower regularity now holds exactly when all frozen stages are regular,
  and projects to every earlier prefix. Regular child stages extend parent
  roots with their coordinates retained. With explicit regularity hypotheses,
  each compact slice component reaches a short child label. At a nonsingular
  stage the slice constraints are surjective, with fewer active old heights
  than ambient coordinates. For a fixed affine slice, generic objective
  derivations and polynomial regularity guards now produce an integer height
  outside the old span whose regular-slice critical roots are nonsingular.
  The guarded regular-locus allowance remains qualitative. For homogeneous
  leading cones, a multiplier-power system now gives integer normals using
  at most (2*n+1)*(2*n+size(D)+2)+1 bits per coordinate. These normals extend
  transverse cone flags over every coefficient-field extension; pure-power
  leading forms supply the empty flag. When the affine slice is regular over
  field extensions and its leading-cone flag is transverse, a projective
  bad-root system now also gives nonsingular original critical stages with
  objective width (2*n+2)*(4*n+size(D)+5)+size(2*n+1). The retained determinant
  is the original Lagrange Jacobian, including at zero multipliers. The same
  objective extends the leading flag. Finite families share one direction,
  adding only their count's bit bound to the objective width. Native direction
  records charge the actual regular-parent count from source dimension,
  degree, and depth, independently of prior direction magnitudes. A shared
  arithmetic-circuit PSPACE test now detects all singular complex child roots
  at guarded real parents, including positive-dimensional fibers. Shared
  right-inverse guard circuits select exactly nonsingular real parent matrices,
  allowing complex auxiliary inverse entries. A combined native writer derives
  that Jacobian from the shared parent row program and retains the parent
  equation guards at the same assignment. Native source relocation preserves
  the original source, marking polynomial, and child derivatives after a
  parent prefix. Original affine critical stages now have native shared
  circuits with exact original-row identities and completions for every
  root, including singular roots and zero multipliers. Each derivative call
  copies only the original source. A charged writer captures actual signed
  normal records as shared binary integer constants. A single algebraically
  closed projective bad-root check certifies affine regularity and cone
  exclusion over all coefficient-field extensions. Native shared level
  families now read actual signed records and compute constant, ancestral-height,
  and midpoint levels in the original tower layout. Their output references
  and lengths depend only on source dimension. Native space-bounded
  concatenation emits whole families without copying earlier stages. Full
  affine query composition and direction selection remain open. A canonical
  reciprocal Gram determinant now gives bounded integer coordinate annihilators
  for all roots of affine systems without infinity roots, including singular
  roots. Stagewise original cone certificates exclude infinity roots of the
  entire multiplier-power tower. Every original critical root lifts to that
  tower over the complex numbers, proving finiteness of both complete towers
  without affine-slice smoothness. When the coordinate annihilators capture all
  roots, the equation-only native sampler counts exactly all system roots.
  The reciprocal determinant embeds in the existing nested determinant
  backend. Fixed-degree reflection has native coefficient access charging the
  Gram reader; actual power-tower Macaulay metadata has native controls. Native
  mixed-degree homogenized rows now read the actual positive power tower from
  the original source and charged signed records. FP exponent division handles
  multiplier powers, with linear inactive rows and a unique zero dummy at
  every depth. A native reciprocal row completes the homogeneous family for
  the Gram backend. The native full-box determinant and reflection now compose
  into a complete coefficient reader for these coordinate annihilators, retaining
  the original source and signed record costs. Actual rows retain the original
  mass budget, and native degree and coefficient-size budgets now bound these
  annihilators. Every field-valued root is retained without a Jacobian condition.
  The actual power tower now instantiates complete square sampling under stage
  cone certificates. Odd multiplier powers preserve ambient coordinates and
  biject its real roots with all original Lagrange roots. Native counts and
  existence tests therefore retain singular original roots. A regular coordinate
  grid preserves the same primitive parameter and rational coordinates. Native
  equation filtering now gives short vertices in bijection with all captured
  roots, including singular roots; original affine vertices preserve ambient
  coordinates. Coordinate objectives and prefix constraints now supply native
  cone certificates using explicit 0/1 direction records. Doubled coordinate
  towers also carry native exact height and midpoint records; their actual rows
  copy ancestral coordinates or put a current coordinate strictly between
  ordered ancestral bounds. Complete original roots project to prefixes and append frozen-stage roots. Their labels sample
  compact regular slice components without critical-stage Jacobian conditions.
  Singular constraint points give zero-objective-multiplier stage roots when
  the height normals are independent. Symbolic squarefree coordinate families
  now have complete finite anchored arcs off explicit finite exceptional sets.
  Auxiliary spatial regularity suffices; properness and endpoint roots come
  from the original equations. Constructed value annihilators make equation
  zero tests constant along a branch, so one original fiber indexes all
  retained arcs outside a constructed finite exceptional parameter set.
  Nonvanishing leading coefficients give properness of coordinate grids;
  monic grids are proper globally. Polynomial constant shifts of affine systems
  with infinity exclusion construct proper complete Gram coordinate grids and
  original-root arcs, including singular endpoints. Their coordinate and
  parameter degrees have uniform determinant bounds. Explicit integer-grid
  test-value annihilators have determinant degree bounds; their underlying
  Gram construction also has coefficient-mass bounds. Their trailing coefficients
  and squarefree coordinate factors construct a nonzero integer exceptional
  polynomial with degree and root-count bounds. The affine-height arcs now use
  this explicit polynomial. Their original endpoint fibers are finite even at
  exceptional parameters. Singleton endpoint roots and the constructed arcs
  give finite graphs of entire closed affine-height slabs, preserving paths
  and connectedness. Incidence reduces to vertex and arc endpoint equality,
  including isolated endpoint roots. Native value readers now start with the
  original bivariate coordinate polynomials and multivariate test. They compute
  homogenization and the reciprocal Gram determinant with binary degree
  allowances, retaining parameter coefficients and charging all original readers.
  The computed polynomial retains singular grid roots and is nonzero for exact
  positive coordinate degrees. Pairwise coordinate midpoint signs identify every
  arc endpoint among the finite endpoint roots, uniformly near either end.
  Value relations with nonvanishing trailing coefficients make these signs
  constant on retained intervals, including identically zero tests. Slab
  incidence therefore agrees with midpoint matching at one retained sample.
  The explicit squarefree exceptional factor constructs each scalar covering;
  uniqueness of its lifts preserves coordinate equality and root order along
  grid branches, including labels sharing some coordinates. Ordered transport
  preserves distinct-root ranks. One fixed-width ordinal per coordinate gives
  constant branch records that distinguish grid points and use n*W bits for
  coordinate degrees at most 2^W, including empty grids and zero-width records.
  Native affine-height coordinate readers now compute the exact reciprocal
  Gram certificates from original integer rows and polynomial shifts. Their
  canonical binary levels and unary widths are derived from source dimension
  and binary row allowances, with both source readers charged. Infinity exclusion
  makes the native determinant degree allowance exact for these coordinate
  polynomials, supplying the grid degrees without an actual-degree scan.
  The actual affine power tower now instantiates these readers for one varying
  row; its original signed-record program supplies all integer coefficients and
  the parameter shift is internal.
  Uniform indexed access now supplies its entire coordinate grid, rejecting
  invalid coordinates. The original source alone also supplies value readers
  for its shifted equations on that grid. Both Gram determinants are internal;
  the existing cone certificate proves nonvanishing, and every field-valued
  grid root satisfies the computed value relation without regularity.
  These same computed value polynomials now construct the exceptional factors
  for complete actual-source height arcs, so the native readers and geometric
  certificates agree. Their outer and parameter degrees have native binary bounds.
  Both Gram stages now also have derived coefficient-height budgets. A native
  lowest-nonzero-coefficient scan computes each actual trailing factor from the
  original source, with no trailing-index or coefficient-height oracle.
  A native complete slab exceptional polynomial now combines those trailing
  factors with every nonzero principal subresultant of each coordinate and its
  derivative. Zero factors are detected in space and replaced by one, so the
  construction requires no FP GCD-order oracle. Its streamed coefficient reader,
  binary degree bound, and coefficient-mass budget come from the original source;
  avoidance implies the geometric slab's exact exceptional conditions.
  Distinct-root counts and rational cuts now compute exact point/gap cell
  codes in native PSPACE, with source-derived unary label widths. Every gap
  avoids the geometric exceptional factors. Coordinate ordinal records also
  distinguish original roots at singular exceptional parameters, since the
  specialized coordinate polynomials remain nonzero. Their lengths are
  polynomially bounded from the source metadata, and the records stay constant
  along retained branches. Effective branch/endpoint membership and recursive
  coordinate metadata remain required.
  Endpoint midpoint comparisons now have an auxiliary integer system with
  two copies frozen at an algebraic height and a third copy available for the
  varying branch. The retained equation's actual degree is computed in space
  and stored in a record. Original source readers supply all extended rows
  and the linear midpoint tests. Exclusion at infinity and constancy of each
  frozen copy are proved, including repeated parameter roots and singular
  endpoint fibers. Effective matching on the adjacent retained interval
  remains required. A context-preserving coefficient interface now feeds the
  extended system into native varying-height coordinate Gram readers, with
  levels and widths computed from its prepared degree record. Uniform indexed
  access supplies its complete coordinate grid and rejects invalid coordinates.
  Native midpoint-value annihilators now retain all extended-grid values over
  every field, and genuine prepared endpoints make them nonzero. Derived height
  budgets through both Gram stages supply native trailing-factor scans.
  Degree-record validity is native as well. The same computed midpoint
  polynomials capture every pair of endpoint candidates, so their trailing
  factors make matching stable and one retained sample characterizes each
  actual slab endpoint edge. A native streamed product now combines every
  midpoint trailing factor with the original exceptional polynomial. It retains
  every original endpoint height and has source-derived binary degree and mass
  budgets. Native distinct-root and rational cell queries give refined gaps
  where every midpoint test is stable. Samples in either refined adjacent gap
  identify the original slab's endpoint edges; extra refinement roots require
  no new endpoint attachments. Both gaps approach their retained root, including
  the extreme roots. The derivative of the computed matching polynomial now
  supplies algebraic candidates in every bounded refined gap, by Rolle's
  theorem. Its coefficient reader and root counts are native. Complete
  scalar sampling gives these candidates short labels, native validity, and
  native polynomial-test signs, including repeated roots. A checked-promise
  sampler also keeps native access total on malformed preparation records;
  its guarded language rejects them. Indexed polynomial tests now preserve
  the complete source label while query fields select the test. They supply
  native coefficient signs, actual degrees, zero tests, and leading signs
  after algebraic specialization. The original affine source instantiates
  these queries for every coordinate at every exceptional height, without
  endpoint regularity assumptions; each specialized coordinate stays nonzero.
  Native principal-sign and Tarski routines now count roots in these algebraic
  fibers. Algebraic cuts count refined roots below independently labeled
  endpoints and samples. A native validator uses those ranks to check exact
  adjacency on either side, including repeated roots, and checks both labels
  and the prepared degree record. Every bounded refined endpoint gap has an
  accepted derivative-root label. Every accepted native sample identifies the
  original slab endpoint edge by midpoint matching on either side.
  Retaining a sample or boundary height as one further variable now gives a
  finite integer system containing the current point and both endpoint
  candidates. Native source readers compute its rows, exact degree-record
  validator, nonzero coordinate annihilators, and their degree and height
  budgets. Complete short labels cover every actual tuple, including singular
  roots. Native multivariate midpoint signs at those labels equal the original
  comparisons. Streamed coordinate Thom comparisons now identify fixed
  projections across labels, including repeated coordinate roots. A native
  universal scan fixes both heights, the current point, and the chosen
  endpoint while ranging over every other endpoint candidate. It decides
  exactly the geometric midpoint matching predicate in PSPACE. At an adjacent
  retained sample the result equals actual left or right slab attachment.
  Native scalar-coordinate comparisons now bind the independently encoded
  endpoint and sample heights to the joint tuple, preserving their original
  labels and retaining repeated roots. Combined queries check these identities
  and exact adjacency before deciding attachment. Every valid joint tuple in
  the requested gap has accepted scalar labels. The checked edge language is
  in native PSPACE, and its answers equal actual left or right slab attachment.
  Native coordinate-order comparisons now support least-label scans that
  count each projected value once, even when many complete labels share it.
  Fixing the two joint heights gives exactly the actual spatial fiber; its
  native coordinate ranks agree with ranks of a complete finite branch family.
  These geometric rank vectors distinguish branch points and stay constant
  along retained branches. A native fixed-width writer packages the coordinate
  ranks into short descriptors, with source-derived unary lengths. The assembled
  words now identify the same geometric branch across different retained
  samples. Native algebraic cuts validate each sample's original slab code;
  bounded native witness search validates the short descriptor labels. The
  checked branch relation is proved correct from the original affine equations
  and their computed exceptional polynomial. Native endpoint markers now denote
  actual points in their stated fibers, including singular endpoint fibers.
  The scalar candidates retain both exceptional heights and derivative roots;
  inside open gaps they are exactly the original derivative samples. Every
  endpoint point has a marker, including isolated points with empty neighboring
  fibers, by taking equal heights and three equal spatial copies.
  Projected Thom comparisons identify those points independently of auxiliary
  joint copies. A bounded native attachment query validates the short branch
  descriptor, adjacent heights, original slab, and endpoint marker. Its witness
  test is proved equivalent to actual left or right slab incidence together
  with the requested descriptor. Complete existential attachment queries are
  now equivalent to the actual descriptor-to-marker slab edges, independently
  of their witness tuples. A native bounded search also converts each complete
  point label to a scalar primitive-parameter slice record, recovering
  every original coordinate. Child coefficient signs, actual degrees, and root
  counts are native over these records. For endpoint markers, recovery preserves
  the original singular fiber. Complete point labels now supply actual named
  rational parents with native validity and derivative probes. Endpoint names
  validate the original frame and expose exactly the endpoint coordinates.
  Every endpoint point has such a bounded parent name with exact recovery,
  including isolated points absent from neighboring slabs.
  The existing ancestry-aware child routines now give native regular child
  samples over these markers, without parent endpoint regularity. A concrete
  bounded slab graph now encodes the branch and endpoint-marker vertices.
  Its native validity and adjacency charge point equality and attachment
  searches. Valid labels embed at the derived unary width, and encoded arc
  edges agree with the checked queries in both orientations. Validated branch
  words enumerate exactly a complete geometric sample fiber and distinguish
  its distinct branch points. Whole-graph connectivity and reachability with
  native endpoint readers are in PSPACE.
  Native scalar context checks now identify the two ordered boundaries of an
  original gap and validate both interior samples without requiring spatial
  roots. Each accepted context constructs complete continuous branches from
  the original equations, including their singular endpoint limits. Every
  branch has constructed native joint references at both samples, satisfying
  the sample and adjacency checks. Their injective descriptors enumerate
  exactly the branches and agree across the two samples.
  Every valid native graph vertex now denotes a unique actual curve or endpoint
  point, and every geometric piece has a bounded vertex. Native edges agree
  with relative frontier incidence, including duplicate markers and arbitrary
  padding. The assembled accessible cover transfers whole-graph connectivity
  to the actual closed root slab. Validated connectivity of these slabs is
  in native PSPACE, with no supplied cover or adjacency routine.
  Every bounded original gap now has an accepted context, computed by a native
  bounded search at a derived polynomial width. The resulting connectivity
  algorithm takes only the prepared frame and gap index and decides the
  actual original root set over the closure of that gap. Endpoint, sample,
  branch, and marker labels are computed internally.
  Short branch descriptors also compute native ancestry names for the actual
  interior sample points. Their rational coordinates recover precisely the
  constructed curve at the requested sample, independently of auxiliary tuple
  choices. Native child queries retain this ancestry and cover regular child
  roots over those points, without requiring the parent point to be regular.
  Coordinate trailing factors now refine the computed exceptional set. Every
  coordinate zero and sign test, including multiplier tests, is constant along
  an interior branch; a native reader computes it from the short descriptor.
  With independent slice normals, every singular slice point also has a
  complete native critical label with zero objective multiplier. Its singular
  locus is finite with the source-derived next-stage critical-root bound.
  Native projection tests now compare complete labels from different square
  samplers by their coordinate Thom signatures. Bounded search computes exact
  affine ancestor labels, preserving the original multiplier coordinates as
  well as the spatial blocks. The resulting native child selector retains
  every critical root over its named parent, including singular children.
  A native zero-objective-multiplier filter retains every singular slice point
  with that checked ancestry. Compact regular slices have joined accepted
  samples in every component; no regularity of the full critical root is needed.
  For independent affine normals, complete critical samples now meet every
  connected component of any compact slice, including singular components.
  A maximum on each component is either a regular constrained critical point
  or a retained singular point. This bounds the number of components by the
  native next-stage root bound, without asserting paths through singularities.
  Accepted child labels now index a constructed clopen connected cover of
  each such slice. Nonemptiness is precisely native child validity; overlaps
  are exact connections between their sampled points. For generated
  coordinate-prefix records, compactness, normal independence, and the cone
  certificates are derived, with native label validity and unary widths.
  The zero-objective child filter is also sound: every accepted point lies in
  the singular locus of its stated parent slice.
  Streamed complete-child searches now decide whether an entire generated
  coordinate-prefix slice is singular or regular, in native PSPACE. An accepted
  singularity query also computes an actual complete singular child label with
  its exact ancestry. These routines charge the original readers and derived
  widths, without a supplied regularity test or singular-point oracle.
  When a coordinate prefix fixes all but the last coordinate, every feasible
  point has a unique critical multiplier lift, including multiple roots.
  The actual next-stage root bound bounds every point of this terminal slice.
  Native spatial equality now gives PSPACE point reachability in these slices,
  checking the terminal coordinate flag and both exact parent ancestries.
  Their complete labels also construct an accessible bit cover with native
  edges, and its clopen path saturation supplies recursive endpoint pieces.
  Whole-set connectivity of the actual terminal slice is now in native PSPACE
  as well, including the empty case, without a supplied cover or adjacency code.
  The stage of a varied height row now computes the frozen prefix and its
  native complete sampler. Shifted roots project to that original prefix.
  Every constructed critical branch keeps the same earlier blocks over its
  entire closed slab, including singular endpoint limits. Its two retained
  joint sample references therefore have exactly the same frozen ancestor.
  Native projection search now computes that complete ancestor label from
  the joint sample or its short branch descriptor. Its decoded point is
  exactly the earlier blocks of the branch, and the two retained descriptor
  programs return identical ancestor words despite auxiliary witness choices.
  Coarsening a varied active coordinate height now gives a finite ordinary
  critical root set. A zero-objective branch would make its height parameter
  constant. Native coordinate zero tests thus exclude zero objective
  multipliers on retained open branches. Every singular point of a frozen
  parent's varying slice lifts to an actual zero-objective power root;
  completeness excludes it. The entire varying slice is therefore regular
  inside each retained open slab, without a supplied regularity test.
  These actual varying slices are compact. Every feasible point now has a
  path within its fiber to a constructed critical branch with precisely the
  stated frozen parent. The branches therefore sample every component of
  every interior varying fiber.
  Filtering by one exact original parent gives a finite branch family that
  still samples every interior fiber component. Its spatial branches stay
  in that parent's varying slice through both closed-slab endpoints.
  Removing the varied constraint constructs the compact original coarser
  slice and its proper height-difference projection. The parent branches
  supply continuous sections extending through both endpoints and meeting
  every interior fiber component. The specialized implicit charts now
  construct a component saturation covering the full original open slab.
  Its pieces are clopen and path connected, have connected limits at both
  endpoints, and overlap exactly when their critical samples connect in the
  retained fiber. Native recursive connection tests and endpoint covers remain.
  Given the two recursive endpoint component covers, this actual saturation
  now constructs a clopen path cover of the closed slab. Selected attachments
  retain an additive sum of the branch and endpoint label types.
  Exact ancestor filtering of short descriptors is now native PSPACE, by
  validation, computed ancestor words, and word comparison. It agrees at
  both retained samples. The native newest-height index recovers exactly
  the original parent depth and complete sampler.
  The computed word now decodes to the full original ancestor tuple,
  including multiplier slots. Native filtering is equivalent to equality
  of these decoded original ancestors.
  On the actual constructed family, the decoded native parent is exactly
  the parent used by the component saturation. Native filtering agrees with
  the defining predicate of its finite parent-specific branch index.
  Native ancestor readers also cover both endpoint copies. Marker filters
  use the endpoint's own ancestor. On an actual branch endpoint, its computed
  word equals the interior descriptor's word, including at singular limits;
  the corresponding native marker filter accepts that same ancestor.
  The coarsening and slab regularity arguments now allow independently
  scaled coordinate normals. Actual doubled midpoint records supply their
  own independence proofs, complete singular component covers, and native
  whole-slice regularity and singularity decisions. Their constructed slab
  saturations retain exact critical branch arcs and attach recursive endpoint
  covers, including singular endpoint fibers. Native context conversion
  re-encodes ancestor words in the original parent sampler, preserving the
  entire tuple. Canonical descriptor filters select the exact parent branch
  family, and both interior samples give the same original-context word.
  Actual endpoints retain that canonical word, and native endpoint marker
  filters accept the exact original parent at singular limits.
  Their terminal case retains every feasible point, including multiple roots,
  and constructs native reachability and whole-slice connectivity decisions
  together with clopen path covers.
  Native next-coordinate sweep records preserve every retained original and
  power equation. Their computed parent words preserve the entire tuple, and
  removing the newly active height recovers the original slice exactly. The
  source readers compute the coordinate, row, and canonical ancestor filters;
  the remaining-coordinate rank decreases strictly. Given recursive endpoint
  covers, the actual records construct the closed-slab component cover.
  Fixed-height and midpoint child records retain one or two critical blocks
  with frozen ancestral references. Their exact spatial slices add the
  selected coordinate height or midpoint equation, including at singular
  roots. Native projection re-encodes the full parent tuple in the original
  sampler. Both children decrease the coordinate rank, while depth plus
  twice the remaining rank does not increase.
  Native parent filters select precisely the children of the decoded original
  parent. Rank zero is exactly the native terminal guard.
  An original next-stage critical sample constructs its fixed-height child
  root and native word, preserving the full tuple and freezing the selected
  coordinate over the original parent.
  Paired next-stage samplers reuse the original coordinate annihilators and
  native coefficient readers. Their labels retain every pair of critical
  roots, and native projection recovers both original-context member words,
  including at singular roots. Computed parent-word comparison tests exact
  shared ancestry, including multipliers. A validated compatible pair now
  constructs its actual midpoint child root with one ancestry prefix and
  the appended right critical block. Its original parent and exact midpoint
  slice are proved. Native projection now computes the midpoint child word
  from the original readers, retaining the full original root and its exact
  midpoint slice. The child passes the original parent filter. Every pair
  of original critical roots with a shared parent has an accepted paired
  label and yields the constructed child, including at singular roots.
  A shared-source history now records each child choice with one bit. Native
  depth, objective, and level readers form a single complete sampler family.
  Appending history reproduces the existing child records on every retained
  stage. Frames and complete vertex words have one polynomial bound in the
  original source length across all valid histories. Native context search
  returns fixed-height and midpoint child labels to that same family,
  preserving every powered coordinate and the decoded original root.
  Exact slice membership, whole-slice connectivity, and paths between points
  are preserved under the coordinate casts. Uniform terminal algorithms
  decide both connectivity tests, with their stopping flag exactly rank zero.
  The full recursive component graph remains required.
  Scalar height extensions now have monic equations of a fixed selected
  degree and explicit finite free integer bases. At a valid specialization,
  including a drop in the formal polynomial degree, the new parameter
  recovers the requested height with a nonzero constant integer denominator.
  The construction allows nonreduced algebras and zero branches of the
  leading coefficient. Native inverse and denominator coefficient readers
  use the original modular matrix access and derived entry-height bounds.
  Explicit companion matrices reduce new-generator access to old coefficient
  matrices. A native streamed product computes their normalization columns,
  and normalization has binary-readable coefficient-height and matrix-entry
  bounds, derived from the old rank and coefficient bounds.
  A geometric odd-power schedule now keeps old scalar powers fixed and gives
  each new monic parameter row a pure-power leading term. Appending it
  preserves exclusion at infinity, including degenerate branches. Different
  odd coordinate powers preserve real connectivity through an ambient
  homeomorphism. Native coefficient access divides requested exponents
  coordinate by coordinate and retains the original reader's space charge;
  power substitution does not increase coefficient mass.
  Physical critical equations now take derivatives before applying the new
  coordinate and multiplier powers, with an exact equivalence on all real
  critical roots. Their coordinate leading cone permits independent source,
  gradient, and height powers. Bounded degree-decreasing reduction matrices
  yield relative characteristic annihilators from finite spanning relations,
  including dependent spanning families, with degree equal to the normal
  state count rather than the old parameter-algebra rank.
  Clearing a constant denominator keeps the reduction matrix integral.
  Rescaling its characteristic polynomial annihilates the original value
  and preserves the specialized degree. Its native coefficient reader
  combines the original coefficient and integer-residue readers using
  modular powers and products, including composite moduli.
  Concrete fixed-width reduction matrices now construct these annihilators
  directly from pure-power-leading equations, with no supplied reduction
  table. Oversized states have zero columns; every valid nonnormal step
  decreases spatial degree. Native binary-degree controls select a single
  shifted lower coefficient and preserve its space charge. The explicit
  spatial dimension has polynomial binary length, independent of earlier
  parameter-algebra ranks and coordinate powers. An integral Euler row
  operation puts coordinate-critical Fermat systems in this form without
  division. For coefficient parameter degree E, the resulting annihilator
  coefficients have degree at most N*(bound+1)*E. These estimates hold over
  arbitrary commutative coefficient rings, including nonreduced ones.
  Frozen rational slices now use one common integer denominator. Integral
  substitution preserves the original free spatial degree and puts the
  actual cleared critical rows into the same pure-power system. Constructed
  annihilators vanish at every such critical root and retain their explicit
  degree under characteristic-zero specialization. Frozen numerators of
  parameter degree E give lower coefficients of degree at most S+D*E,
  without dependence on the previous parameter-algebra rank. The shared
  denominator construction preserves these parameter degrees.
  A native multivariate clearing reader now uses fixed-width Kronecker
  substitution and streams the original source, numerator, and integer
  denominator readers. Its support bound follows from the original source
  and numerator degrees. Extra per-coordinate clearing powers are constant
  integer padding, so no modular division is needed. Target queries discard
  redundant high exponent bits, and modulus one is supported.
  Scalar equations can now be padded to one uniform monic degree on every
  branch, including invalid degree records. Their iterated integer bases
  consist of bounded coordinate monomials. Each height numerator has an
  exact representative of degree at most (births+1)*(N-1); its native
  coefficient reader asks the regular-representation matrix for column
  zero. Canonical coefficient representatives also give explicit monic
  scalar equations with old-coordinate degree at most births*(N-1),
  independent of coefficient heights and old algebra ranks. The padded
  generator matrix is constructed from the original coefficient matrices.
  One global odd-power schedule preserves every older scalar power as new
  coordinates are prepended. Canonical heights embedded in later prefixes
  retain their original physical degree bounds. For actual substituted
  Fermat critical rows, derived leading forms exclude all physical and
  multiplier coordinates at infinity whenever an unused coordinate supplies
  the objective. Appending these blocks preserves exclusion at infinity for
  the whole system, including singular roots. Every padded scalar root also
  extends the prefix algebra evaluation, including extra padding roots and
  nonreduced prefixes.
  Iterated scalar prefixes now construct their complete square systems,
  positive row degrees, and nonzero integer coordinate annihilators. Joining
  a prefix to its actual canonical-height critical block in a finite layout
  gives a finite root set, with no regularity hypothesis on those roots.
  Prefix coordinates determine a unique algebra evaluation. Undoing the
  physical powers gives the original critical equations at the actual
  retained heights. Every selected real scalar root extends the same
  parent coordinates, and its canonical numerator and integer denominator
  recover the exact height at every interpreting evaluation. Native
  canonical coefficient readers now accept independent exponent widths,
  reject exponents outside the basis box before narrowing, and undo the
  fixed coordinate powers while charging the original matrix reader.
  Padded scalar-generator matrices now have native entry readers built
  from the original coefficient matrices. Binary identity tests handle
  shift columns; padding and invalid degrees give zero blocks. The
  canonical new-head basis puts its new digit in the least significant
  position, so binary division supplies the old rank and new digit without
  a permutation table. Lifted old elements have diagonal scalar blocks.
  Native matrix-polynomial entries now stream binary matrix powers and a
  modular sum, charging both original entry and coefficient readers.
  Characteristic-coefficient scans internally construct the inverse
  polynomial and its evaluated matrix, including singular branches.
  Fixed-width basis changes preserve the characteristic denominator.
  Exact numerator-matrix identities combine the new generator and lifted
  inverse matrices; native digit guards supply the lifted entries.
  Native generator, selected-inverse, and denominator queries now share the
  original source record and caller modulus. Every internal coefficient
  scan forwards its own requested modulus to the original reader. Valid
  basis ranks retain their exact meanings; binary clipping supplies total
  defaults for other ranks. Original entry-height bounds derive the
  determinant and characteristic budgets, and the source-level numerator
  identity uses the same constructed generator and inverse matrices.
  The native numerator reader now multiplies those matrices internally,
  forwarding every factor query to the original scalar source. Its column
  zero supplies the actual canonical height coefficients, including wider
  exponent queries and the fixed power substitution. No separate numerator
  matrix reader is assumed.
  Retained algebra elements now lift through chains of actual scalar
  extensions. Their native matrix readers compare the whole new digit block
  and divide by its combined binary radix, charging the original old reader.
  Old generators and representative evaluations keep their exact coordinate
  slots. A scalar birth can also retain arbitrary ancestral physical and
  multiplier coordinates: only scalar slots enter its new equation, and
  exclusion at infinity and exact algebra interpretation are preserved.
  Constructed history samplers now alternate actual scalar and critical
  extensions while retaining the whole parent tuple. Every root interprets
  the scalar algebra and satisfies the original critical equations at its
  actual heights. Their full root sets are finite, including singular roots.
  One global degree bound has a native binary computation; each critical
  block followed by a scalar birth adds exactly 2n+4 coordinates. Every
  selected real scalar root extends the same full parent, and every child
  interpretation recovers its exact height, including nonunit leading
  coefficients. Uniform native history queries still need construction.
  Original coefficient-matrix heights now derive budgets for the constructed
  generator, singular inverse, canonical numerator, and integer denominator.
  The native coefficient reader uses these same source bounds. All budgets
  have binary computations; one extension's numerator-height budget grows
  at most linearly in the original height, with an explicit polynomial factor
  in the old rank and scalar degree.
  Actual critical history roots now construct their next relative scalar
  polynomial. One common integer denominator reconstructs the frozen
  coordinate block exactly; the resulting annihilator has fixed specialized
  degree determined only by free spatial arity and original source degree.
  Every critical coordinate, including at singular points, extends the same
  full history and is recovered by its canonical height. Native original
  source, retained-height, integer-denominator, and leading readers now
  construct the cleared critical rows and relative-polynomial coefficients.
  A block representation now expresses multiplication matrices of relative
  characteristic coefficients and matrix moments as integer power entries.
  The characteristic polynomial is taken over the original parameter algebra;
  its degree stays independent of the old algebra rank. Binary block sizes
  account for that rank in the integer computation.
  Native algebra-valued moment readers now construct the augmented integer
  blocks and power them from the original row, column, and matrix coefficient
  readers. Quotient ranks select outer vertices, remainder ranks select old
  basis coordinates, and all three reader costs are charged.
  Native relative characteristic-coefficient readers now construct Berkowitz
  factor blocks from the original matrix reader, including algebra-valued
  trailing moments. Integer block powering computes each coefficient's
  multiplication-matrix entry without changing the relative characteristic
  degree. Binary controls retain the original record and caller modulus;
  out-of-range coefficients return zero, and the original reader's full
  space cost is charged.
  Native relative reduction-action readers now power the original reduction
  matrix, select shifted normal columns, and zero the padding columns before
  computing characteristic coefficients. The actual pure-power construction
  supplies these actions; its normal mask and coordinate shift have derived
  FP programs over binary state ranks. The action and its characteristic
  coefficients require no additional matrix readers.
  Original lower-polynomial and common integer-leading readers now construct
  the actual relative coordinate annihilator's coefficient matrices. Native
  reduction entries select or negate one lower coefficient, using additive
  multiplication-matrix entry maps; no multiplicativity assumption is made.
  The action, relative characteristic polynomial, and scalar rescaling are
  computed internally, with both supplied reader costs charged. Negative
  scalars, composite moduli, and zero-padding columns are retained.
  Frozen substitution now has an explicit coefficient sum over the original
  spatial exponent grid. A native FP mask selects the matching free exponent;
  it never enumerates old parameter monomials. Native products of algebra
  powers now compute the required old basis entries from original factor
  matrix entries, with binary powers, product lengths, and old ranks.
  A cleared monomial term now constructs every factor program from original
  coefficient, common-denominator, and retained-height readers. The spatial
  exponent sum determines its padding power; free coordinates select the
  denominator and frozen coordinates select retained heights. Their complete
  space costs are charged, including when the denominator is not invertible
  modulo the caller's modulus. A native fixed-width coefficient sum now
  combines these term programs with the free-exponent mask and computes the
  actual multiplication-matrix entry of each frozen-substitution coefficient
  from those same three original readers. No expansion in old parameter
  monomials is required.
  Native derivative readers now extract actual old basis entries of original
  partial derivatives from the same coefficient reader. Additive extraction
  commutes with differentiation and cannot increase spatial degree. The
  frozen-substitution reader also computes these cleared derivatives while
  retaining the original clearing allowance and all three original reader
  costs.
  The frozen Fermat constant now has a native reader from the original
  retained-height matrices and integer leading coefficient. Full matrix
  powers are summed outside the free block; a fixed-width guard selects
  the constant spatial coefficient. Adding this constant computes the actual
  cleared lower polynomial from the same original readers, including signed
  heights and denominators over composite moduli. Saved-source query writers
  now separate the original family from new exponent and basis queries. Native
  free-coordinate gradient readers select the original index offset plus the
  local rank, differentiate before clearing, and retain the original allowance.
  A native coordinate-product reader decrements one spatial exponent and calls
  the original coefficient reader once; its correctness needs only additive
  extraction. The common critical-row leading coefficient a*D*q^D also has a
  constructed native modular reader. Actual coordinate-gradient products now
  feed a streamed sum omitting the objective coordinate. Native scalar
  multiplication and subtraction construct the Euler objective coefficients;
  a native row selector combines these with the remaining cleared gradients.
  All critical lower rows are computed from the original four readers.
  A two-call recursive controller now constructs the Euler objective from
  the frozen lower coefficient and the Euler sum. Its native certificate
  assumes no child evaluator, and its stored state retains one context and
  one modular reply, with exact two-child requests and a two-step clock.
  The recursive lower-row selector preserves the source and old basis
  indices. A streamed Euler sum scans the free coordinates, omits the
  objective term locally, and bounds its modular accumulator. Coordinate
  multiplication requests one decremented gradient coefficient when the
  selected exponent is positive, and returns zero otherwise.
  Retained-height power products now have resumable stages through the
  existing layered matrix reduction. Binary product lengths use one local
  power stack; adjacent layers request valid factor positions and old basis
  pairs. Separate factor-power stages preserve the original factor source.
  Both native certificates use metadata without a factor evaluator.
  Frozen substitution now has a resumable sum over the original spatial
  exponent grid and a local mask for compatible free exponents. Another
  sum omits free coordinates from the frozen Fermat powers. The constant
  coefficient scales that sum by the FP leading residue, and a two-call
  controller adds it to the actual cleared source coefficient. Each local
  certificate avoids assuming the recursively requested evaluator.
  Monomial factors now route coefficient and frozen-height entries to
  child tasks. Scalar, free-coordinate, and padding entries use the FP
  denominator residue locally. The actual monomial product uses the same
  resumable power-product stages.
  Derivative coefficients also suspend for one bumped original coefficient,
  then apply native exponent multiplication modulo the caller modulus.
  A binary degree guard returns zero outside the derivative support. The
  actual cleared-gradient source has native local certificates through
  these same stages, retaining both old basis indices.
  Saved-source queries now supply every critical lower coefficient in the
  reduction reader's row, spatial-rank, and old-basis protocol. These rows and
  the common integer leading coefficient feed the actual relative coordinate
  annihilator internally. Its native evaluator charges those same four
  original readers; its specialized degree is the spatial grid size,
  independent of the old rank. The unused fallback coordinate is proved
  irrelevant to the reduction matrix and relative polynomial.
  Bounds on the actual lower rows and common integer leading coefficient now
  give binary budgets for every coefficient matrix of this constructed
  annihilator. These budgets are linear in the two input heights, with a
  factor depending on the spatial grid, reduction bound, and binary size of
  the old rank. Bounds from the same four original inputs now derive those
  lower-row and leading budgets, including original derivatives and frozen
  Fermat constants. The original spatial grid controls coefficient sums.
  A height-independent binary factor now bounds the whole critical budget
  from a common positive bound on those four inputs. The canonical native
  constructor derives its reduction bound and spatial width from free arity
  and allowance, matching the sampler's relative degree.
  Actual retained-history data now constructs a native source whose relative
  polynomial equals the sampler's critical candidate. Its coefficient budget
  follows from integer source coefficients, retained numerator matrices, and
  scales, including common-denominator clearing. A constructed height bank
  prepends each canonical numerator and denominator and embeds all old
  numerators. A binary factor bounds one complete critical birth, including
  the next bank normalization; singular selected coefficients and invalid
  advertised degrees are covered by the height bounds.
  Critical histories now have a derived common bound on all retained
  numerator matrices and denominators. One metadata ceiling controls every
  critical reduction below the birth cap. Induction on the actual history
  gives a geometric height budget, whose binary length grows linearly with
  the number of births. The common budget has a native binary computation
  from the original spatial metadata, scalar width, and birth cap.
  Initial scalar input and exceptional births still need integration with
  this global bound. Resumable binary folds now supply local recursive
  controllers for streamed modular sums and products. Their certificates
  assume no child evaluator; exact bounded entry requests and accumulator
  bounds feed the ranked recursive-stack compiler. The combined history
  reader controller still requires assembly. Flat history task words now
  retain one root record while replacing birth, phase, and query fields.
  Their ranks decrease on an earlier birth or local phase. Bounded query
  fields give a polynomial word allowance independent of the number of
  retargeting steps.
  Numeric task fields now use a fixed count of binary blocks sized by a
  root-dependent cap. Native writers clip malformed values and recover
  valid fields exactly. A flattening writer extracts the original task
  from local matrix query wrappers; its stored result retains one root,
  fresh fields, and a derived unary word bound. Earlier births and lower
  phases preserve the decreasing rank through this writer.
  A native binary critical-query cap now includes the original and relative
  spatial grids, retained rank, characteristic/moment/action/product block
  dimensions, and scalar-rescaling exponents. It uses the coefficient-height
  budget as a numeric bound, keeping field widths polynomial in its binary
  length. The cap still needs instantiation in the combined history reader. The constructed critical polynomial's top coefficient
  is an explicit nonzero integer power. A second height representation uses
  the actual monic scalar root divided by that integer, preserving the same
  full physical parent. Its retained numerators are exactly the canonical
  prefix generators, and a history induction supplies the same common height
  budget. For these integer leading coefficients, native companion-matrix
  normalization reads one coefficient and one leading residue and uses modular
  scalar powering, including for composite moduli and nonunits.
  A forward modular pass now evaluates the scalar-root denominators from
  integer leading metadata and earlier denominator indices. Native FP
  certificates use unary birth and coordinate counts, binary exponents, and
  bounded residue tables. The cast of the integer recurrence is proved
  equal to the computed table for every positive modulus. Actual critical
  histories yield denominator-only scripts recovering their stored banks.
  Algebra-independent critical commands now construct the actual scalar
  prefixes and height banks with one fixed physical schedule. Their derived
  denominator instructions recover those banks exactly, including each
  older prefix. A truncated forward pass clips a binary birth request to
  the unary history count and reuses the same metadata fields. Native
  instruction access therefore gives FP residues of the interpreted banks.
  Every retained generator now has a deterministic creating command and
  older suffix. The constructed embedding supplies its actual matrix and
  preserves the same integer denominator. A prefix lookup selects the same
  creating family in the full script, supporting queries with one root.
  Actual creating-generator families now supply the resumable companion
  controller. Its leading residue comes from the interpreted bank’s native
  denominator pass; metadata and task writers suffice for the certificate,
  while the requested critical coefficient remains a recursive child.
  Reading these scripts is FP when their metadata has the supplied native
  controls; no algebraic matrix callback is used by the denominator pass.
  Finite closed-slab covers now assemble into a global component cover.
  Its paths are exactly finite overlap walks; adjacent edges are endpoint
  fiber intersections, and empty labels remain empty after saturation.
  The actual common-cleared height stage now fuses its native cofactor
  with the raw generator route, requesting the earlier creating companion
  directly. It preserves invalid/empty zero cases and introduces no extra
  same-birth recursive phase, including for composite moduli and nonunits.
  The retained-point terminal algorithm now searches complete terminal
  children for endpoint membership and equality, with exact path semantics
  in the finite slice. A native tagged leaf dispatches fresh child labels
  and retained references and handles invalid records.
  A shared matrix-entry writer now replaces row/column fields while keeping
  the same root, birth, modulus, and other bounded fields. The actual
  relative-characteristic power stage uses these fresh entry requests.
  Flat Euler Lower, Sum, and coordinate-gradient stages now select concrete
  children with normalized derivative ranks and guarded exponent decrements.
  Native local clock/state certificates also give common allowances over
  all short descendants, deriving the global recursive-stack resource bound.
  Actual flat critical coefficients now request one relative characteristic
  coefficient and rescale it locally using the derived FP common scalar.
  Point-pair trace requests retain both original endpoints by stage
  references. Their checked lower-rank query has exactly the original
  common-fiber path relation, including singular fibers; retained points
  are not assumed to be new critical samples.
  Flat retained-generator requests now descend to the exact creating
  companion using quotient indices; unequal retained digits and invalid
  selectors return zero without a child. Actual queried source common
  denominators also have native FP readers from the script metadata.
  Original creating-command leading residues now have a native reader with
  chronological lookup. The common leading scalar `a * Q^D * D` is FP from
  the original leading and denominator residues. Actual normalized Euler
  source access supplies the flat two-call objective stage, with decreasing
  phases and preserved bounded fields.
  Validated trace height requests now emit actual lower-rank child frames,
  with query sizes bounded in the original input and exact frozen-fiber
  connectivity semantics. These requests still need a complete dispatcher.
  The flat-history stack compiler now derives task closure, a unary rank
  bound, modular reply sizes, and a polynomial frame budget from local
  controller contracts, without assuming any recursive child evaluator.
  The companion stage now writes actual flat critical-coefficient requests,
  preserving the caller modulus and decreasing phase. Its controller is
  certified from original command metadata without a coefficient evaluator.
  A bounded binary slab tag now packs the actual local bit covers into one
  graph. Local edges and adjacent endpoint tests construct its PSPACE graph
  routines; unused tags remain empty even after component saturation.
  The original coefficient leaf now inserts its integer residue diagonally
  in the actual old basis, with its original FP or space cost charged.
  Critical query parameters now preserve the actual creating polynomial,
  carrier, and basis while changing the coefficient, matrix indices, target,
  and modulus. Original integer coefficients act diagonally in that basis.
  Original command metadata now derives all denominator-pass instructions,
  including the canonical exponent and clipped old selectors. Common-cleared
  height entries multiply one recursive generator entry by an FP cofactor;
  this works for negative scales and nonunits modulo composite integers.
  The critical stages share a flat task format with twenty-seven ranked
  phases and sixteen bounded fields. Its numeric cap includes the full
  born-prefix rank and the derived uniform height budget.
  Each retained generator now has an actual creating birth, whose index
  fixes the binary radix for its embedding in the current prefix. Its matrix
  entries route to that birth by quotient indices and matching low digits.
  A resumable companion-root controller computes shifts and padding locally
  and requests exactly one coefficient for every other entry. Its local
  controls are FP from the scalar-leading reader, without assuming a native
  coefficient evaluator. The mixed history reader still needs assembly.
  Retained-digit routing and relative Berkowitz factor and moment-block
  entry selection now have resumable controllers too. Local zero and unit
  cases request nothing; each other entry requests one selected child.
  Their native controls assume no child evaluator, and their outputs match
  the actual integer block matrices used for the relative polynomial.
  Modular matrix-power stages now derive native binary stopping allowances
  and unary state bounds from metadata, with valid-index child requests and
  preserved input contexts. Specializations evaluate actual relative
  characteristic coefficients and algebra-valued moments without child
  evaluator certificates. Coefficients above the spatial degree return zero.
  Shifted reduction-action entries and scalar rescaling now suspend through
  the same task interface. Nonnormal columns return zero immediately. A
  normal entry requests the constructed algebra-valued reduction power;
  rescaling requests one characteristic coefficient and finishes with FP
  scalar powering, including negative nonunits modulo composite moduli.
  Pure-power reduction entries also have native resumable controls. The
  actual parameter-algebra adapter retains both old basis ranks and the
  required spatial-index transpose. Normal diagonal entries read the local
  integer leading residue; each admissible nonnormal entry requests one
  lower coefficient, and invalid entries request nothing.
  These algebraic steps still require integration with the exceptional
  height equations and the recursive sampler.
  Polynomial shifts of
  row constants preserve exclusion at infinity. The full recursive component cover and
  endpoint attachment remain required.
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
  Resumable midpoint scans now have native child writers, Savitch successor
  semantics, decreasing depth, and non-growing validated query records.
  Their halting and state-length bounds charge only a binary counter and
  three Boolean values alongside the original task.
  The recursive connection tests remain open.
- Native recursion base cases: both connectivity tests in dimensions zero
  and one. On the real line, an ETR query detects a missing point between
  two points. Point queries include singleton validation and endpoint
  membership, retaining irrational endpoints and rejecting invalid descriptions.

For arbitrary Boolean sign pieces, a native product margin is positive exactly
on the strict stratum inside its closed weak envelope. Its bounded graph
retains the original tuple and has a unique margin coordinate. Adding the
old squared norm makes radial fibers affine. Each relatively closed positive
component has same-label local margin maxima on arbitrarily small radial
slices. Any continuous positive critical branch with squared radius equal to
the parameter converges to the prescribed original center, and its projected
component joins that center. Constructing and covering these branches for the
actual regularized producer, and bounding a uniform effective radius, remain
open. The radial graph now has a concrete native regularized source, a literal
integer spatial polynomial, and a degree cap independent of the radius. Marked
points recover the original tuple, margin, radial coordinate, and component
label; the critical branch argument must still preserve that marking. A universal
centered radial graph instead stores the center and squared distance as literal
coordinates, giving compact coordinate-frozen slices. For compact singular
polynomial zero sets, a constructed coercive critical-point limit stays in any
chosen clopen piece. Parametric eliminants produce nonzero trailing-coordinate
polynomials whose finite Cartesian root grid meets every such piece. Keeping
strict positive-margin labels isolated, constructing continuous branch coverage,
and proving effective uniform radius bounds remain required.

The complete 27-phase evaluator for critical-only scripts has a native
polynomial-space proof. One canonical residue model connects the actual leaf,
arithmetic, matrix, and creating-companion values. The concrete dispatchers
have native certificates, binary clocks, unary state bounds, and strictly
decreasing child ranks. Primitive original scalar coefficients may use charged
space. The stack compiler includes local output-processing costs, and no
per-stage matrix evaluator is assumed. A fresh phase26 record exposes the
actual creating-prefix generator entry through this evaluator.

Source snapshots preserve integer matrix entries under fresh query records,
and valid source dimensions fit the native field cap. The arithmetic includes
original and derivative grid sums, monomial factors and powers, frozen and
Euler rows, reduction powers, augmented moments, and relative characteristic
coefficients. Guards confine semantic replies to the actual current requests.
Both old-basis indices and the original transpose convention are retained.
The creating-source adapter returns zero at missing births. Its leading and
denominator leaves come from primitive critical-script metadata.

Tilted coercive sampling now stays in the selected positive clopen piece.
One radius-parameter family supplies finite grids and boundary-attaching branches;
actual Gram certificates prune extraneous Cartesian roots. A literal integer
circle equation transfers closed-source covers to the positive-margin sets,
so projected pieces are accessible without a supplied branch hypothesis.
Producing the finite recursive covers, effective bounds, and a native evaluator
for the tilted family remains open.

A tagged mixed history retains an initial integer bank through physical
critical births, with exact generator origins and common clearing. Relative
coordinate, validated squarefree, and Gram factors are constructed over the
selected old parent ring, with bounds at the original spatial degree. Scalar
normalization preserves selected roots even when the old multiplication
matrix is singular. One or two formal nilpotent digits expose the actual
parameter coefficients; both fit the original task cap. The Gram determinant
source uses an ordinary characteristic constant coefficient of its negated
matrix, with exact extraction of both formal digits.

Native virtual-source metadata, original integer coefficient leaves, and
source snapshots are proved. Scalar requests charge the common denominator,
leading value, and retained heights. Reduction entries request their leading
scalar recursively, preserving both old-basis indices. A native stack compiler
accepts the mixed birth/routine/phase rank and includes local processing costs.
Native current-reply controllers cover derivative, retained-height,
frozen and Euler operations, reduction entries and powers, action entries,
augmented entries and moments, relative factors and powers, and scaled critical
coefficients. Their guards, clocks, state bounds, and mixed-rank requests are
proved. Actual action and moment children discharge the matrix reply contracts.
The scalar multiplier remains a charged recursive request, including at composite
moduli. Canonical residue witnesses cover all lower phases zero through sixteen.
Fresh context queries retain the original root while selecting an earlier scalar
birth and the actual source kind. The original-row scale and critical leading
scale have separate native controllers. Two native dispatchers now cover all
virtual critical arithmetic phases zero through twenty-five, including the
grid, product, and factor operations. One matching predicate and exact scalar
callbacks discharge the lower dispatcher's current reply contracts. Context
two through four now have scoped dispatchers and current scalar contracts;
physical-context answers impose no virtual reply obligations. Native
Gram and Macaulay controllers are tied to actual mapped system coefficients.
Native homogeneous queries restore the actual full Fermat rows, retaining the
original scale separately from the derivative scale at composite moduli. Their
flat writers preserve the source context and both old-bank indices. Actual
restored-row and homogeneous-row branches return zero on invalid row,
monomial, and basis labels. Their child contracts name the existing lower-row,
scalar, and critical-coordinate models. A native reciprocal-chart branch now
returns the actual double-nilpotent mapped-system coefficient from its selected
homogeneous reply, including the negative identity chart and invalid-label zeros.
Native Macaulay entries now request only their selected current reciprocal
coefficient; invalid second-basis labels are rejected before padding. A native
negative Gram product and streamed sum return the literal matrix entry, with
loop counts bounded by the original retained-grid cap. One native row dispatcher
now closes all six value-matrix stages against their literal current model;
its external boundaries name only the lower critical and scalar stages. A native
Gram characteristic source now supplies the determinant routine's integer block
entries and augmented moment entry/power stages. These requests preserve
natural invalid labels and use only current value-row or block replies. Native
relative factors and powers now compute the literal characteristic coefficient
matrix, guarding invalid output basis labels explicitly. One native Gram
determinant dispatcher closes all its internal current replies; its external
arithmetic boundary is the existing value-row model. The complete mixed evaluator now joins these source decoders, scalar callbacks,
raw coordinate/PSC branches, and normalized producer operations. The raw value-factor
branch now reads the actual Gram characteristic coefficient; its coefficient
branch extracts the first nilpotent digit, retains natural invalid-label zeros,
and supplies the existing normalization raw-cut value after truncation.

Native integer-zero and trailing-degree scans keep binary counters and request
small-modulus residues or coefficient-zero flags recursively. Their local
certificates assume no child evaluator. Output postprocessing preserves the
request relation, and an adaptive two-call controller lets the first reply
select the second query. These controllers supply the scans needed for
leading normalization without materializing a large integer leading value.
The actual raw cut's leading matrix now supplies an integer characteristic
source of coefficient rank one. Native entry and characteristic controllers
use its literal matrix values; integer-zero and trailing-index controllers
use current characteristic replies and an explicit integer height bound.
Zero flags carry modulus two, and trailing indices carry a modulus larger
than the matrix dimension, so every answer remains a canonical residue.
Native powers, augmented entries and moments, and relative factors now use
current replies for this actual leading matrix. An adaptive inverse-coefficient
controller first requests the exact trailing index, then the selected
characteristic coefficient at the restored caller modulus. Both requests have
native certificates and strictly decreasing mixed ranks. Streamed sums now
compute the literal inverse matrix and its raw-coefficient product. The final
branch returns the trailing scalar on the diagonal at the selected degree,
the inverse/raw product below it, and zero for invalid indices or higher degrees.
One native dispatcher covers all fifteen normalization phases with a canonical
residue model. Its hypotheses are exact current child replies, an integer
entry-height bound, and the small-modulus loop bound. Distinct native phase
nodes now derive every internal reply contract from this one dispatcher model,
including zero outside the factor matrix. The final branch is the literal
normalized coefficient matrix. Normalized producer-leading and retained-generator
companion phases also have a native dispatcher with current-reply closure. Its
two charged companion requests read the actual coefficient and producer leading;
both decrease the mixed task rank. The raw-factor dispatcher and complete mixed reader now share one current
residue model.

A full mixed command history includes normalized cuts alongside integer and
physical critical births. Padded earlier prefixes preserve exact generator
origins and denominators. A native cofactor fold requests earlier producer
leading values. A native retained-height controller now reconstructs the exact
old-bank multiplication entry from those leading values and the literal fresh
creating companion. Its query restores the creating context and coordinate;
unequal younger radix digits return zero. Affine height matrices are finite
integer combinations of these cleared references. Their spatial cofactors are
the common bank denominator to the ambient power times the product of original
scales omitting the selected coordinate; swept virtual heights use the same
constant block and an explicit slope block. A separate physical source backend supports ambient dimension
zero and offset zero without a frozen-height coordinate or formal digit.
Its original and derivative controllers now use an immutable original scalar
reader. Native physical height and monomial controllers use exact current
lower-stage replies and scalar callbacks, including signed composite-modulus
regressions. One context-restricted physical dispatcher now covers phases zero
through twenty-five, with exact current-reply closure and canonical values.
Its scalar callbacks remain charged. Native physical scalar controllers compute
common leading and original scale from their current children. The physical
denominator is reconstructed from earlier producer leading values and original
rule scales; a physical producer-leading phase requests common leading and
raises it to the exact derived exponent. A native physical companion dispatcher
now requests the actual critical coefficient and producer leading, with both
replies closed against current models. Its polynomial is the creating physical
command polynomial. Cut and physical readers also interpret the identical full
mixed-history state and denominator bank. Integer producers now have native
leading, coefficient, and companion branches using only original scalar cells
and degree metadata. All three producer kinds, including padded integer-X
births, are identified with one literal creating-command companion and leading
scalar. One guarded native dispatcher now joins all three producer kinds,
with canonical replies and zero for invalid births, routines, and contexts.
Its current model closes the chronological producer replies used by the literal
retained-height controller. The physical and virtual critical routines now
also have one guarded native dispatcher with canonical replies. A joint
critical/producer dispatcher closes the physical critical-coefficient callback
internally; its remaining boundaries are the scalar and normalized-coefficient
models. Natural-index height identities connect actual callbacks to the finite
affine formulas, including zero beyond the spatial coordinate range. Complete
mixed dispatch is proved; the remaining original input bindings are described
below.

A native scalar dispatcher now computes all six scalar phases from original
syntax cells and current producer replies. Fixed-width table passes reconstruct
the literal affine heights. The combined scalar, critical, and producer machine
closes their mutual callbacks against one current model; normalized coefficients
remain its external arithmetic boundary. Coordinate and value raw-coefficient
controllers restore the actual cut coordinate and choice before evaluation.
The PSC backend now computes actual matrix entries, powers, factors, and constant
characteristic coefficients with preserved cut indices. Context-restricted
normalization correctness uses proved request invariance to avoid imposing
virtual-source meanings on physical contexts. Full raw dispatch now includes
coordinate, squarefree, and Gram sources in contexts two through four,
preserving the saved coordinate and cut choice.

Mixed-history heights use one original-source growth factor. Actual virtual
coordinate, squarefree, and Gram sources have binary height bounds derived from
the original source and old bank. The Gram bounds include the actual reciprocal
system, Macaulay entries, determinant, and both formal nilpotent digits.
Resumable cofactor folds request older producer leading residues; these scalar
leaves remain charged computations.

The complete seven-routine mixed arithmetic controller now has a native
polynomial-space evaluator. All recursive scalar, critical, entry, determinant,
raw-cut, normalization, and producer callbacks are closed against its current
model. Original integer degrees and coefficients may themselves use charged
space. Literal command headers supply metadata, and original syntax bounds
supply heights for the actual complete history, including normalized cuts.
The initial exceptional integer bank has an actual source adapter with exact
polynomial transport. Binding every remaining original scalar and spatial
primitive to the concrete input writer remains required.

A division-free dilation gives the tilted sampling polynomial a constant
nonzero leading coefficient. Physical variables are homogenized while frozen
parameters remain unchanged; the gradient and coordinate coefficient identities
are proved with polynomial syntax-size bounds. The uniform native writer now feeds the original spatial coefficient reader,
with an input-syntax coefficient-height ceiling. A denominator-cleared
coordinate equation recovers the original coordinate by an index shift and
integer powers, preserving degree bounds without modular division. Selection
after specializing the old algebra gives a finite nonzero limit-coordinate
family. A bounded auxiliary level coordinate turns unconstrained critical
points into roots of the existing hypersurface critical kernel. The native
cut interface, effective level bound, and sampler assembly remain open.


Concrete exceptional affine syntax now derives its coefficient cells from
charged original level and selector words. The actual initial-bank slope has
a separate space evaluator and a source-only height bound. A complete
arithmetic constructor uses original header, scalar-body, and polynomial
writers together with charged integer sources. Binding the remaining concrete
selectors and command snapshots, and handling large level coefficients without
serializing their full integers, remain required.


The initial parent bank now supplies its own real coordinate bound from the
original polynomial masses. This gives an explicit binary exponent for the
level coefficient and a native modular reader for its potentially huge
integer value. The actual appended-level spatial coefficient reader and its
height ceiling use the old term word and this exponent. The arithmetic
constructor accepts this source without serializing the level integer.
Forward and inverse coordinate selectors and the sweep slope mask are derived
from original level data. A separate seventh header field distinguishes raw
cut tags while preserving the existing source contexts.

Selected limit-coordinate factors have exact matrix coefficient transport,
finite valid choices, real limit roots, and original-source height bounds.
Their native evaluator streams older producer leadings and a shifted critical
query, preserving the original root and modulus even for nonunit denominators.
The fourth cut constructor uses raw tag 5 and producer context 2. Its prepared
branch restores the immutable coordinate and choice; all denominator and
critical replies close against the full native controller. The shared history
height profile includes the extra denominator powers. Initial real parent
coordinates have correlated integer-prefix realizations and causal level
bounds. A correlated limit birth constructs the next source's frozen data
while retaining the old bank. Source-framed instructions and their
Family adapter preserve each creating source. Literal header adapters derive
cut metadata and producer routing. A causal binary schedule bounds the next
level and its LOW coefficients from retained-bank bounds, with native residue
readers. Actual framed run and padded-prefix bank bounds follow from script
syntax and one default-instruction bound. A concrete original-bank advice
factory constructs scalar controls and exact headers for one coarse critical
birth followed by a coordinate or limit cut. Original direction and level
values remain charged in space. Complete recursive command writers and effective graph bounds remain required.

Changing-source framed histories now have one native polynomial-space
controller for all seven arithmetic routines. Every scalar, critical, entry,
determinant, raw-cut, normalization and producer callback uses its current
model. Actual retained generators recover their earlier creating sources and
signed leading coefficients. Original term words and native frozen-coordinate,
tilt and level selectors supply the spatial coefficient costs; original integer
words supply exact degree and coefficient costs in space. The actual initial
exceptional bank also supplies these costs directly, followed by changing-source
noninteger instructions and default X padding. Unit-selector body
records supply the scalar costs. The combined syntax factory derives its height
and modulus budgets from original script, default and fallback bounds. Binding
these records to the complete canonical recursive command writer remains
required.

Physical critical points now extend the actual framed history, including at
singular points, while preserving the old real specialization, physical tuple
and bank. For an arbitrary polynomial zero set, an auxiliary-variable tilt
constructs bounded critical limits in every clopen component piece without a
compactness or regularity premise. A literal auxiliary-term transport preserves the frozen original coordinates.
At the same real bank specialization, its bounded critical trajectories meet
the actual finite selected relative-factor coordinate grid. The tilt direction
remains the free auxiliary axis. Physical critical attachment and the formal
parameter used in limit cuts retain distinct scopes.

The component sampler now starts with an actual empty bank and performs
exactly n tagged limit cuts. It reaches a point in every nonempty clopen piece
of the original Term zero set, with every original coordinate recovered from
the final bank at index n−1−i. All earlier physical rows and the interpreting
hom remain correlated through the trace. Original word sizes and the actual
interpreter derive the next bank height; its uniform recurrence has native
binary access. Each selected coordinate has at most 2^B values, and the actual
grid has at most 2^(B(n+1)) points. These are semantic coverage and size results;
native descriptor validation and the recursive connectivity graph remain open.

Canonical unit records now construct their literal changing-source plan,
body writer, snapshots and total command/fallback header tables. Original
producer birth labels are converted to current retained indices. The actual
integer prelude supplies its own coefficient and degree costs, and original
tilted term descriptors supply LOW identities. A separate auxiliary-cut record
writer preserves the original input and advice. The causal level source is
regular in its free level direction; its bounded level sheet is homeomorphic
to its exact projected region, with a unique continuous level value. This
sheet statement makes no identification with the original zero-set components.

The empty-bank auxiliary frontend now derives complete native square sampling
from original term syntax and dimension. All creating companions, literal
joint rows, mass and degree bounds, coordinate annihilators and root counts
have native space proofs. Full-root pullback preserves every actual source
while accommodating arbitrary caller moduli. A padded default-X birth handles
dimension zero without another serialized record.

Bounded original choices now replay the exact actual packed script and bank.
Advice has exactly 2*n*B bits, and both advice and packed roots have uniform
polynomial length bounds in the original input. Native denominator, common-Q,
cofactor and common-cleared coordinate readers use the same joint prefix root;
no independent coordinate-root lifting is inferred. Effective recursive adjacency remains required.

Fixed-width native candidate labels now decode one actual joint-root bank point.
Every nonempty clopen original zero piece contains such a point. Filtering by
the original equation constructs an actual component path cover, including
singular and unbounded zero sets, with at most 2^labelWidth components. The
canonical Boolean sign decomposition uses these covers with injective fixed-width
sign/component tags bounded by one polynomial in the original input length.
Native original-equation filtering and graph reachability are proved. Exact
raw bit decoding supplies an actual bounded Boolean frontier cover with native
PSPACE vertex validity. Reserved singleton endpoint words now have native
validation and writers, removing endpoint piece locators from the point-query
transfer. Relative-frontier edge costs remain required.

Actual retained-coordinate ordering preserves signs through positive Q-squared
clearing, including negative denominators and composite moduli. Correlated cut
frames retain the same old hom, tuple and bank; frozen-first permutations keep
the spatial degree and leading coefficient. Native bounded-regular LOW and
leading readers, including permuted sources, keep huge powers implicit. The
original-only radius bounds every decoded candidate, and the marked-lift
component theorem applies to the bounded zero set. Unbounded component
preservation and effective recursive adjacency remain open.

Current-denominator sweep height evaluation now reuses the charged bank
product. Original-only scalar controls and growth bounds give native models
for all seven routines and arbitrary-modulus companion readout. Untruncated
factor probes preserve the complete selected cut, with finite semantic tests
for lower choices, the leading coefficient and all higher coefficients.
Actual regular-frame sampling and sections give closed-slab covers from
recursive endpoint covers. Scalar-only critical shadows share the native
scalar prefix and bank, and free-slot normalization recovers ordinary
coordinate cuts without requiring physical critical lifts. The point-language
transfer now needs only a native bound for its actual frontier-edge routine;
it already rejects malformed, empty and nonunique endpoints. Native recursive
attachment/graph assembly and unbounded component preservation remain open.

Causal script plans now instantiate prior-run Q only in their mathematical
rules, preserving exact original headers, bodies and source lookup. Their
raw original table writers and mixed-scale controls are now constructed from
the causal record format, including optional original midpoint rows.
Full relative-factor coefficients now have native arbitrary-modulus readers
from the actual current-Q machine. At one successor joint tuple, finite
coefficient guards and an exact zero-padding guard recover the actual cut
root; a padded row alone is insufficient. Last-coordinate and fully frozen
terminal covers now support a descending regular-frame construction that
builds every recursive endpoint cover. Quantitative native labels and
attachment queries remain required. A valid Boolean tag's decoded joint
point projects into its own piece, retaining every original coordinate and
scoped term/formula value. Both connectivity transfers now use the same
actual raw frontier-edge routine; its native space bound and global
unbounded component preservation remain open.

Raw causal records now provide native indexed current-Q controls and original
resource bounds. Bank-coordinate characteristic polynomials retain the same
joint point, with proved original-only degree and coefficient-mass bounds;
their native coefficient bridge is now constructed. The integer prelude
remains unfinished.
Lower-choice probes query all earlier choices without altering the old run.
Recursive covers now have explicit size and native numeric width bounds.
Actual sections and persistent physical branches have injective fixed bit
words; native rank computation, branch attachment and complete record replay
remain open. The actual bounded regular source is also exactly a polynomial
in the external physical radius `T = 2^R`, with parameter degree independent
of `R` and polynomial binary width. This does not prove radius stabilization.

Native finite cut guards now test full coefficients, all lower choices and
padding at one actual successor vertex. Original command tags exclude
integer and physical commands from selected-cut validation. Relating every
guard to one creating-cut interpretation and later terminal tails remains
unfinished. Branch endpoints have a curve-free local characterization;
real parameter Tarski queries have semantic eventual-sign results, while
their native general coefficient circuit and endpoint cost remain open.
The external radius family has a proved original-only integer height bound.
Signed power constants have native degree-one integer sources with binary
exponents. Actual regular-source coordinates have an explicit dyadic bound;
its exponent is affine in the radius code. Clipping bad roots to those outer
cuts preserves avoidance of the complete bad set and exact cut origins.
Native sorting and whole-record assembly remain required.

Old-bank coordinate annihilators now have native coefficient and metadata
access, derived from original inputs and preserving the same candidate joint
point. Scalar power substitution also has native access without expanding
polynomial syntax. The canonical marked lift has exact original-coordinate
and real-slack identities; native correlated replay remains unfinished.
Unrestricted coordinate probes support all Y and E coefficients without
recorded-choice clipping. Selected principal queries lift to integer
polynomials on the same weighted tuple. Their general native coefficient
circuit, physical rank and endpoint-query costs remain open. Native cut scans
now imply actual validity and exact specialized degree at one common old
interpretation. The creating-row/root bridge now follows from the actual candidate. Later-tail
transport remains required before validating an entire recursive trace.

Actual successor rows now derive one common old interpretation, specialized
cut validity, exact degree and the full untruncated factor root. Decoded-bank
identification and later terminal-tail transport remain open. Actual cached
coordinate coefficients now feed integer multivariate heads. Coordinate-root
ordinals are constant on continuous physical branches, using all real scalar
roots; this does not assert that every ordinal tuple is a physical point.
Native implicit univariate tests preserve the same complete candidate and
actual retained-bank value. Current-Q leading and product readers support
integer Source leaves without expanded integer syntax. A native derivative
scan proves equality between coordinates from different framed scripts using
one shared nonzero annihilator. Correlated prelude replay, physical endpoint
assembly, full native graph construction and effective global stabilization
remain unfinished.

Independent exceptional frames retain original-parent and exceptional-scalar
labels, including endpoint-only and empty fibers. A frozen-first coordinate
permutation now connects arbitrary active subsets to the same selected mixed
parent. Exact fiber homeomorphisms preserve the original degree and bank.
Finite critical sections meet every connected component of each full frame
slice. An additional coarse critical-height cut gives regularity between cuts,
at the original degree and initial cap. Path saturation then gives full
closed-slab component covers from recursive endpoint covers. Compactness and
finite exceptional values now produce an ordered finite sweep and a cover of
the entire selected coarse slice, assuming covers only at its finitely many
endpoint fibers. The mixed sampler, uniform endpoint recursion, native cut
ordering, label packing, and graph assembly remain open.

Closed Boolean combinations of weak inequalities now reduce to one integer
polynomial equation while preserving point connectivity and whole-set
preconnectedness, including for unbounded sets. Shared circular witnesses give
a continuous section across disjunction boundaries. A strict conjunct also has
a connected circular witness lift, with native formula and endpoint writers.
Native gate metadata and arithmetic writers now derive the closed reduction
from the actual input formula. A polynomial-size shared gate construction and
canonical endpoint extension preserve both whole-set and point connectivity,
with the original singleton validation retained. A bounded circular replacement
also gives a proper closed projection with compact connected fibers. Its native
source and endpoint writers use dimension n + 5m and degree at most four times
the maximum of the original atom degree and two. Finite unions of strict
inequalities also have a native equation reduction: simplex weights and
circular witnesses give a continuous section and connected fibers. A bounded
native traversal now derives that finite term list from actual input formulas
whose Boolean constructors are disjunctions of strict atoms. The resulting
equation writer preserves whole-set connectivity of the canonical input,
including disconnected unbounded sets.
Formulas built from strict inequalities using conjunction and disjunction now
have a native closed witness graph homeomorphic to their original solution set.
Nonnegative margin gates use positive parts, products, and sums; a reciprocal
of the positive root margin selects precisely the original open set. Native
whole-set and point-query equation writers retain the original singleton
validation. Every old singleton has a unique canonical endpoint extension,
including points outside the source, which remain excluded by membership.
These constructions have one initial unary dimension and degree budget.
Every individual path fits a bounded closed ball, but this does not provide
an effective uniform radius. General Boolean mixtures across open and closed
boundaries and component-preserving compactification remain required. Arbitrary
formulas now have an exact finite sign partition using their original atomic
terms. Fixed-width labels, a native accepted-label circuit, and native strict
stratum and weak-envelope writers establish this decomposition for arbitrary
NOT, AND, and OR formulas. Boundary tuples lift to closures of selected pieces
in each properly projected bounded envelope. Relative incidence is expressed
by equality of every retained original coordinate. Connected component
refinement and native adjacency of these pieces remain separate obligations.
Original atomic rows also have native syntax readers, degree/mass/coefficient
bounds, zero extension, and padding/reindexing adapters that preserve their
literal evaluation on retained coordinates.

Arbitrary Boolean inputs now have finite component covers without a supplied
finiteness or path-cover premise. Polynomial zero sets have finitely many
components and are locally connected, including singular and unbounded sets.
Refining connected chains and taking a complete-space limit constructs actual
paths. The resulting finite semantic graph characterizes both connectivity
tests. Native bounded labels, component membership, and adjacency costs remain
required to turn this graph into the full PSPACE decision procedure.

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
lake env lean scripts/CheckAlgebraicArcs.lean
lake env lean scripts/CheckAffineShiftArcs.lean
lake env lean scripts/CheckIntegerGridValues.lean
lake env lean scripts/CheckIntegerGridArcs.lean
lake env lean scripts/CheckFiniteFiberSlabs.lean
lake env lean scripts/CheckBinaryValueReaders.lean
lake env lean scripts/CheckGridValueReaders.lean
lake env lean scripts/CheckEndpointMidpoints.lean
lake env lean scripts/CheckAffineShiftReaders.lean
lake env lean scripts/CheckActualHeightReaders.lean
```

The core import check enforces the separation from the optional tube route.
The axiom and space audits include all three library targets. The axiom audit checks
declarations in the `LeanCanny` namespace, local Nat
codec extensions, and their transitive dependencies, allowing only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms. The foundation
checks enforce the native Complexitylib time and space interfaces and reject
legacy machine dependencies. `CheckAbstract` also follows public definitions
and statement dependencies to reject hidden implementation references.
