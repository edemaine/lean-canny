# Connectivity development history

Archived checkpoint notes from README and RESEARCH, preserved on 2026-11-06.
This is a development ledger, not the current proof outline. Statements that
work remains open describe intermediate checkpoints or alternative routes.
Both original connectivity PSPACE membership theorems are now proved.

See [README](README.md#connectivity) for the public statements and
[RESEARCH](RESEARCH.md#connectivity-proof-outline) for the completed proof
outline and the correctness pitfalls encountered during development.
The [construction ledger](CONNECTIVITY-PROTOTYPE.txt) gives further detail.

## Former README checkpoints

The following historical ledger records intermediate checkpoints and alternative
routes; its earlier gap notes describe those checkpoints.

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
  lifted original points. A shared sampled source writer computes its
  coefficients
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
  sample set now has the same bound, proved using algebraic finiteness of
  regular
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
  real and complex critical sample, with nonzero denominators, native
  coefficient
  readers, and explicit degree and mass bounds. Even denominator powers now
  clear the original critical equations, with native readers and explicit
  bounds.
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
  count. Two native determinant-coefficient signs now recover supplied
  parameter-
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
  families now read actual signed records and compute constant,
  ancestral-height,
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
  into a complete coefficient reader for these coordinate annihilators,
  retaining
  the original source and signed record costs. Actual rows retain the original
  mass budget, and native degree and coefficient-size budgets now bound these
  annihilators. Every field-valued root is retained without a Jacobian
  condition.
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
  ordered ancestral bounds. Complete original roots project to prefixes and
  append frozen-stage roots. Their labels sample
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
  Gram construction also has coefficient-mass bounds. Their trailing
  coefficients
  and squarefree coordinate factors construct a nonzero integer exceptional
  polynomial with degree and root-count bounds. The affine-height arcs now use
  this explicit polynomial. Their original endpoint fibers are finite even at
  exceptional parameters. Singleton endpoint roots and the constructed arcs
  give finite graphs of entire closed affine-height slabs, preserving paths
  and connectedness. Incidence reduces to vertex and arc endpoint equality,
  including isolated endpoint roots. Native value readers now start with the
  original bivariate coordinate polynomials and multivariate test. They compute
  homogenization and the reciprocal Gram determinant with binary degree
  allowances, retaining parameter coefficients and charging all original
  readers.
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
  and binary row allowances, with both source readers charged. Infinity
  exclusion
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
  certificates agree. Their outer and parameter degrees have native binary
  bounds.
  Both Gram stages now also have derived coefficient-height budgets. A native
  lowest-nonzero-coefficient scan computes each actual trailing factor from the
  original source, with no trailing-index or coefficient-height oracle.
  A native complete slab exceptional polynomial now combines those trailing
  factors with every nonzero principal subresultant of each coordinate and its
  derivative. Zero factors are detected in space and replaced by one, so the
  construction requires no FP GCD-order oracle. Its streamed coefficient reader,
  binary degree bound, and coefficient-mass budget come from the original
  source;
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
  length. The cap still needs instantiation in the combined history reader. The
  constructed critical polynomial's top coefficient
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
  row constants preserve exclusion at infinity. The full recursive component
  cover and
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
  Source connectivity is equivalent to pairwise path connectivity of these
  samples. Their exact
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
  Sparse sign monomials now span all rational-valued functions on the projection
  roots,
  using at most the polynomial label width in distinct features, each to power
  at most two. Their product Tarski moments have native polynomial-space
  readers.
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
  both searches in native polynomial space. Native triple and
  derivative-weighted
  moments supply integer Gram pencils and pointwise probes. Bounded native
  search
  chooses short separating integer labels, computing the actual root count
  internally. Native cuts enumerate these labels in hash order. Two
  determinant-coefficient signs recover one derivative sign at the denoted root;
  short ordinals label every realizable signature without storing it in full.
  Streamed Thom comparisons compute real-order ranks, and bounded native search
  converts geometric ordinals to hash ordinals. Derivative-sign queries
  therefore
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
  valid base roots, and its real roots are exactly the union of all factor
  roots.
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
label; the critical branch argument must still preserve that marking. A
universal
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
One radius-parameter family supplies finite grids and boundary-attaching
branches;
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
The scalar multiplier remains a charged recursive request, including at
composite
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
homogeneous reply, including the negative identity chart and invalid-label
zeros.
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
arithmetic boundary is the existing value-row model. The complete mixed
evaluator now joins these source decoders, scalar callbacks,
raw coordinate/PSC branches, and normalized producer operations. The raw
value-factor
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
the inverse/raw product below it, and zero for invalid indices or higher
degrees.
One native dispatcher covers all fifteen normalization phases with a canonical
residue model. Its hypotheses are exact current child replies, an integer
entry-height bound, and the small-modulus loop bound. Distinct native phase
nodes now derive every internal reply contract from this one dispatcher model,
including zero outside the factor matrix. The final branch is the literal
normalized coefficient matrix. Normalized producer-leading and
retained-generator
companion phases also have a native dispatcher with current-reply closure. Its
two charged companion requests read the actual coefficient and producer leading;
both decrease the mixed task rank. The raw-factor dispatcher and complete mixed
reader now share one current
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
constant block and an explicit slope block. A separate physical source backend
supports ambient dimension
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
The PSC backend now computes actual matrix entries, powers, factors, and
constant
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
are proved with polynomial syntax-size bounds. The uniform native writer now
feeds the original spatial coefficient reader,
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
values remain charged in space. Complete recursive command writers and effective
graph bounds remain required.

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
compactness or regularity premise. A literal auxiliary-term transport preserves
the frozen original coordinates.
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
grid has at most 2^(B(n+1)) points. These are semantic coverage and size
results;
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
no independent coordinate-root lifting is inferred. Effective recursive
adjacency remains required.

Fixed-width native candidate labels now decode one actual joint-root bank point.
Every nonempty clopen original zero piece contains such a point. Filtering by
the original equation constructs an actual component path cover, including
singular and unbounded zero sets, with at most 2^labelWidth components. The
canonical Boolean sign decomposition uses these covers with injective
fixed-width
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
polynomials on the same weighted tuple. Their native principal coefficient
streams now have degree and mass controls;
physical rank and endpoint-query costs remain open. Native cut scans
now imply actual validity and exact specialized degree at one common old
interpretation. The creating-row/root bridge follows from the actual candidate.
Later-tail
transport is now proved for selected cuts; a universal trace scan remains open.

Actual successor rows now derive one common old interpretation, specialized
cut validity, exact degree and the full untruncated factor root. Decoded-bank
identification, same-terminal prefix interpretations and native terminal cut
validation are now proved. Actual cached
coordinate coefficients now feed integer multivariate heads. Coordinate-root
ordinals are constant on continuous physical branches, using all real scalar
roots; this does not assert that every ordinal tuple is a physical point.
Native implicit univariate tests preserve the same complete candidate and
actual retained-bank value. Current-Q leading and product readers support
integer Source leaves without expanded integer syntax. A native derivative
scan proves equality between coordinates from different framed scripts using
one shared nonzero annihilator. Physical endpoint
assembly, full native graph construction and effective global stabilization
remain unfinished.

Native original-only coefficient, degree and mass programs now construct the
two slack annihilators over the same old algebra. Their expanded characteristic
polynomials vanish at the prescribed real marked slacks under the same joint
interpretation. Concrete correlated prelude replay is now proved.
Selected-cut acceptance is now exactly actual validity, degree and the full
factor root at the decoded newest bank value. Every earlier prefix has one
interpretation of the same terminal suffix; generic native suffix tests are
available. A universal native scan now validates every creating cut.
Anchored scalar root ordinals characterize actual branch endpoints. Root-window
counts remove scalar-root existential quantifiers from Near, retaining its
ordered epsilon/delta conditions and the native coefficient-sign obligation.
A uniform coefficient-mass bound now gives an explicit large-parameter sign
cutoff for actual integer polynomial families. Applying it to the full
recursive graph still requires the corresponding polynomial presentation and
bounds. Full native graph construction and effective global stabilization
remain unfinished.

The native marked integer prelude now contains the original coordinates,
marked slacks and four power parameters in one prescribed correlated
realization. Its full outer-context saved key preserves the actual decoded old
candidate and admits one interpreting homomorphism. Both canonical slack roots
now satisfy the literal native sources; all
coordinate and slack roots are derived from the same old candidate, supplying
one correlated realization of the complete native prelude.
Native selected terminal-cut tests now characterize validity, degree and the
full factor root at the same decoded retained bank value. A universal native
scan
now validates every creating cut. Original-syntax bank queries also
supply their own planning while coordinate selection stays in the test datum.
Fixed-width Tarski principal streams now have native coefficient, degree and
mass controls, with eventual real signs from iterated infinitesimal trailing
coefficients. Same-terminal endpoint substitutions and coefficient-sign tests
remain unfinished, as do full native graph construction and effective global
stabilization.

The marked replay now has original-only native controls and arbitrary-modulus
bank access. Every filtered old candidate supplies one complete native vertex
with all prescribed bank values. Certified saved-prefix rows and denominator
data agree with this literal replay. A datum-based Thom comparison is in
PSPACE and preserves both sampled contexts and words; every filtered old
candidate has a replay of the required width accepted by that comparison.
The same vertex now also passes marked-point filtering.
A native scan validates every chronological cut on one terminal tuple, including
actual validity, stored degree and the full factor root at its retained bank
value. Causal records now append after the marked prelude with absolute birth
references, native tables, original implicit integer leaves and derived height
bounds. All seven native model routines have original-only controls; uniform
caller-modulus causal readout now follows from original-only projected-root
controls, preserving the original record table.
Actual coordinate heads now suffix-embed into one terminal tuple while retaining
eta. Substitution by the same bank endpoint plus or minus delta has native
cleared coefficient and mass programs. Shifted principal-coefficient tests,
ordered Near, physical trace reconstruction, full native graph assembly and
effective global stabilization remain unfinished.

The actual original candidate filter is now in PSPACE. A bounded search
finds one polynomial-width complete marked replay satisfying all original
untruncated leaf roots, regular-source and mark equations, and the Thom
comparison to the original candidate. The canonical replay constructs that
same witness; soundness recovers the original zero equation.
Marked causal records have original-only arbitrary-modulus bank access and
native validation of every actual creating cut on one terminal tuple. A
separate n+10 prelude adds signed cutoff roots with native controls.
An explicit full physical-column enumeration and native scalar-column reader
now give full-row interpretation and bank readback on the same physical
tuple. Native physical-row coefficients and masses, scalar/physical-coordinate
correlation and the trace grammar are still needed.
Tarski parameter coefficient tests now preserve both parameter blocks and
the complete candidate. Native coefficient reboxing rejects oversized
exponents, and cleared two-coordinate midpoint queries preserve arbitrary
signed denominators. These readers feed the native ordered Near tests;
native graph assembly and effective global stabilization remain unfinished.

The full physical sampler and original marked/outer deciders now derive
every row reader and native control from original syntax. Accepted creating
cuts certify their retained quotients as roots under the same older hom.

For prefix-frozen frames, a native exhaustive search now detects exactly the
actual real critical heights inside an interval between retained parent
values. Rejection is exactly disjointness. The proof includes singular roots,
checks all old quotients and the new physical correlation, and keeps parent
and child at one prepared source, horizon and width.
Native Near tests characterize equality with the selected branch endpoint
on the same full tuple.

All three ordinary bad-cut families preserve their real zero sets after
clearing-denominator changes. They now agree across independently realized
histories with equal numerical frozen equations, even with different banks,
horizons and widths. Actual constant coordinate and row scales are derived;
the value case uses weighted Gram minors.

Retained marks and bounds can serve directly as endpoints. Any retained/fresh
pair and one referenced midpoint anchor use exactly one to three decoded
records, sharing a full tuple and hom, with native byte and column bounds.
The literal midpoint block selects a closed physical branch whose endpoint
has an actual child critical record. That attachment uses one extra birth.
Overlapping transported pieces connect their branch endpoints inside the
recursively covered endpoint fiber.

A new native ordered bad-factor interval recognizer checks actual endpoint
order and derives its factor interpretation from guards on the same query
and word. Acceptance is exactly ordered endpoint root absence, including
constant factors, repeated roots and boundary roots. Its PSPACE cost uses
only original represented syntax and radius controls. The legacy language
using normalized-context guards has not been identified with this replacement.

Checked chronological labels now compile prefix, scale2/refsum midpoint
and endpoint-child frames into actual current-Q records. Critical companion
records capture all free coordinates of one physical point, with native
guards comparing every physical column at its own creating power. Native
Thom tests compare retained quotients across independent full sampler words;
atomic endpoint signatures include every frozen and free coordinate.
Midpoint companions now compile exactly, with a mean-aware signature and
actual readback of every coordinate. No retained midpoint alias is assumed.

One matched branch family now supplies the literal clopen slab interior,
ordinal codes, Near tests and endpoints together. A recursive record-chain
grammar has a quadratic count, original code/byte bounds and an actual framed
physical-column ceiling. Padding before the final probe gives an exact fixed
raw count and the existing marked factory's cap. Semantic padding requires
an already realized typed seed.

Complete sampling preserves the same ordinal under literal input composition.
The actual full-physical factory has identical semantic data after auxiliary
key-context changes, so a word can be allocated before embedding it in its
own context. An explicit sampler-width ceiling uses row count and logarithmic
degree. The actual native full sampler and every positive fixed-cap prefix
now have original-only unary word bounds and polynomial majorants. Scalar
width is unchanged by raw record-tail replacement, closing the code-budget
circularity. These bounds use marked mode and literal empty root metadata.

A native one-level compiler now checks its exact original record-table slice,
producer bounds, ordinary cut tags and chosen child endpoint. It constructs
the typed bounded ledger; widening to the original byte bound preserves every
record byte. One correlated optional-pair/anchor/captures program realizes
both geometric endpoints with reference `q + 1 + chosenPairRef`.

The whole-chain compiler and native validator now reconstruct typed bounded
records and prove exact equality with the accepted padded raw table. Reserved
coefficient-only interval probes support nonzero constant and rootless factors.
Actual strict padding margins and a zero-padding extension give one full
sampler word preserving every old quotient. An earlier-only scan retains the
actual-root guard on every meaningful cut. The actual last typed cut now
binds its serialized word to the literal instruction/current denominator,
canonical parent key and complete sampler word at the same root and cap.
Native coefficient guards now characterize validity and exact degree under
the same full-word interpretation. Canonical padding preserves an honest
parent realization using an already known original critical seed.
Whole-chain realization and the complete edge tests remain open.

Equal-height boundary programs now realize the midpoint, endpoint and both
capture blocks at the same point, including singular boundary components.
Equal specialized numerical frozen equations give equal coordinate-root
multisets and ranks across independent banks and parameters. A literal
scale-two mean row centers the sweep at zero without a retained alias.
The actual native cut writer/decoder now preserves these specialized roots.
Five native epsilon-window statistics identify the coordinate rank of the
captured midpoint, using the same full word and original-only costs. Keeping
epsilon proves the exact pseudo-remainder seed degree, including degree drops
at epsilon zero. Anchored coordinate ranks and Near tests imply an actual
local path. The last record before each checked level is exactly that frame's
own first-free-coordinate critical capture. Actual compact slices now have
critical extrema and a closed sweep cover
from their finite bad and critical values, including a singleton case.
Choosing the radius from the original input fixes the literal regular source
across histories. Actual sweep endpoints and every retained/fresh pair have
native chronological encodings with honest realizations. Semantic guard
composition and the two-way bounded graph construction remain open. Fixed
integer bivariate families have
stable root-sign-pattern counts past a common mass cutoff; the recursive
polynomial presentation and original-only uniform mass bound needed for
global stabilization remain open.

The dependency map and remaining mathematical obligations are recorded in
[`ROADMAP-PROOF-AUDIT.txt`](ROADMAP-PROOF-AUDIT.txt). Unconditional PSPACE
membership for the original point and whole-set connectivity languages is
still open.

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
endpoint fibers. The mixed sampler, actual endpoint recursion and local
native frame compilers are formalized. Whole-chain native validation, sample
word packing and effective graph incidence remain open.

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

The native atomic roadmap graph now has concrete PSPACE algorithms for
connectedness and point-to-point reachability. Every accepted vertex has a
total original-polynomial byte bound, and fixed-width coding preserves paths.
Every native edge, and hence every valid raw graph path, now gives a path in
one original regular zero set. Any accepted vertex also yields a fresh,
fully accepted canonical depth-zero seed with the same candidate; the critical
point and complete sampled word are constructed internally. This does not
assert graph reachability from the old vertex to that seed. An original Good
candidate within the required radius now initializes a fresh fully accepted
seed; its actual graph point lies in the marked lift's source component.
Native no-critical witnesses follow from critical freedom of the original
frozen slice. Native order and no-bad guards have exact original-word meanings,
and ordinary/mean probes have fresh own-root words retaining all old fields.
Geometric coordinate certificates now construct both native Near and Rank
tests with one bounded rank word; the actual all-coordinates scan is derived.
Equal retained endpoints now admit fully accepted extensions at any eligible
child-critical point, with fresh own-context words and every old raw column
retained. Every accepted vertex reaches a terminal-depth vertex at the same
point through native identity edges.
Genuine matched branches now construct actual native proper edges at their
prescribed child points, with all acceptance, Near ranks and shared midpoint
conditions derived internally. A finite matched sweep retains those same
branches and constructs its endpoint and slab covers. Arbitrary used cut
points get same-fiber weak critical representatives; artificial empty cuts
require no endpoint code. The entire frozen-slice path is simulated natively.
The terminal fiber and induction on remaining coordinates prove completeness
at every legal depth. For two accepted depth-zero histories with the same
candidate, actual native reachability is equivalent to a path between their
points in the original fixed-radius regular zero set. No recursive hypothesis
remains in this equivalence. This does not assert connectivity of the whole
native graph or a reverse theorem for arbitrary different-depth histories.
The native bounded marker search is now a PSPACE decision procedure.
For an accepted depth-zero seed with native Replay, it is equivalent to a
path from that seed to its own marked prelude in the fixed-radius zero set.
The attachment proof constructs a reachable terminal marker by induction,
retaining prelude fields and using actual retained target heights. It assumes
no marker exists in advance. Replay-aware first seeds can be constructed at
a prescribed global critical point, and arbitrary accepted depth-zero seeds
can be reinitialized at the same entire point with native Replay.
The bounded two-anchor search now decides whether the two ORIGINAL candidate
points lie in the same bounded original-polynomial component. It constructs
both Replay words at one shared actual critical point and compares their
entire physical points, allowing the candidate labels to differ.
The semantic bounded-component language itself is in native PSPACE, including
the original-equation candidate filters. Choosing the derived original-only
candidate radius removes every external radius and validity assumption from
this bounded-language theorem. This radius contains all candidates; preserving
their UNBOUNDED component relation is still a separate obligation.
The actual fixed and padded scalar-extension constructors now commute with
arbitrary coefficient specialization, including their relative coordinates
and relative multiplication matrices and characteristic polynomials.
Normalization and
fixed inverse shifts have proved parameter-coefficient mass and degree bounds
before evaluation. A common mass cutoff derives the inverse constructor's
coefficient-survival and degree/trailing-index guards internally. The actual
canonical mixed-record interpreter now has a constructed polynomial
presentation and one original-input effective cutoff for all its prefixes.
Specialization preserves the quotient basis, bank, all physical rows and
scalar slots. Common bounds and transport for the entire guarded graph
remain open.
Literal sign-refinement and frontier-piece membership now has an exact
closed-circular lift in the SAME decoded candidate component at the specified
original point. The radial polynomial and eliminant have an exact integer
formal-center model, with post-specialization trailing-index guards and
original-only bounds for the INPUT model. Actual piece closure is equivalent
to common membership or a same-label finite-real descriptor retaining a
grid anchor and cut-free interval. The curve is constructed internally.
The original formal input, actual tilted homogeneous system and normalized
eliminant now have native coefficient readers in polynomial space. The final
evaluator retains all formal center/radius/epsilon/T coefficients and takes
only original input packets. A monic characteristic quotient constructs the
normalized value even when the extraneous determinant vanishes at zero.
The actual original source now supplies input-row and normalized eliminant
height bounds, including arbitrary nested coefficients. Concrete center
coefficient polynomials have closed native readers, degree/mass bounds and
finite same-center guards for actual specialized trailing/target degrees.
Bounds retain center variables formally. Actual native finite tests now
pull these center polynomials back through the same chronological bank
references and current common denominator. They select the specialized
perturbation index and target degree with original-only bounds. Joint bounded
descriptor words and native frontier incidence remain to be discharged.
Generic coefficient-base constructions now specialize to the actual native
basis, rows, banks, and all four mixed cut recipes, including their computed
moving slope. Matrix coefficient bounds give a local normalization cutoff.
For an actual finite polynomial family, ordered root branches preserve
query signs beyond an explicitly constructed cut mass, including shared
factors and repeated roots. The marked integer prelude now has a literal
radius-polynomial family,
with exact native degree/leading preservation. Interpolation converts
proved native dyadic growth to parameter mass bounds; actual cut births
specialize to the native next quotient beyond a proved local cutoff.
The constructed formal marked prelude now specializes at every radius,
with its command order bound to the literal full-record-plan suffix.
Actual native banks, raw cuts and critical polynomials have proved affine
radius height bounds. Independent Cartesian queries have constructed
annihilators and input-derived sign cutoffs, including nonmonic heads.
Native matrix growth now derives formal entry bounds and a common BinaryFn
budget for unary-many normalization cutoffs. Constructed finite Cartesian
root labels cover every independent root tuple and preserve bounded query
signs after one common input-based cutoff. Native reachability is equivalent
to walks in the actual finite physical-point graph, independent of endpoint
word choices. Matching its entire edge family across radii remains open.
Actual head/window/query bounds now cover the installed certified graph
sampler, with its actual decoded saved parents and native degree requests.
This supplies evaluated heights; selector and edge transport remain separate.
The actual canonical mixed-record family now specializes above an
original-input effective cutoff, uniformly over every prefix. The remaining
common bounds and physical-edge transport for its entire guarded graph
are still open.
One original-input cutoff now covers every bounded padded record table,
candidate label, seed/probe choice and canonical prefix. A common original
exponent also bounds their formal next-cut matrix coefficient masses. Actual
proper-row keys and degree selectors have radius-independent structural
catalogs. Field equality retains the same left characteristic source for both
probes and has original affine height bounds charging each source radius
and its own sampled row separately. No word ordinal transport is assumed.
Actual indexed sampler rows and scalar columns now specialize from the
constructed family in their literal native order, with original parameter
coefficient degree/mass bounds. Retained-bank characteristic polynomials
specialize to the actual saved keys and installed field source, including all
derivatives. Their target degrees and parameter coefficient bounds are
original-only. The entire sparse graph-query family and physical-edge
transport remain open.
The whole actual raw-cut scalar-prefix representative now specializes at
every target coefficient, with finite target/scalar degrees and original
parameter coefficient degree/mass budgets. Actual consecutive-prefix
NoCritical source and sparse query heights are bounded as well. Computed
common-denominator and total-cofactor products specialize at every canonical
prefix and explicit key. Physical cut/principal query bindings and the
remaining graph roles are still separate.
Constructed field queries now specialize to the literal native physical
test, with original coefficient budgets. The binding permits arbitrary actual
radius functions when their two queried roots have equal radius values; it
does not identify resource seeds with a constant-radius reader. Alternative
typed raw-cut kinds at the same saved rule share the original affine height
bound. The radial same-center squarefree/PSC integer families and their
closed coefficient frontends are also constructed.
Constructed canonical term and mandatory leaf queries now have original
parameter coefficient budgets. The actual single-bank denominator and proper
rank/near queries have original affine radius bounds, preserving their
literal native degrees, eta shifts and physical columns.
Actual same-bank principal and trailing-index guards now select witnesses
after center specialization while retaining radius as a polynomial. The
literal branch cut has a constructed integer coefficient reader with
nonwrapping exponent boxes and original budgets.
Untruncated alternative-factor and actual critical-correlation queries now
have constructed parameter families and original coefficient boxes. Joint
radius/center coefficient degree is bounded for the literal affine value
certificate, with its actual Macaulay box and declared degrees.
The actual saved-rule coordinate head now has a constructed parameter
family. Original metadata catalogs and exact eta/zero-window principal
operators preserve literal native padding and shifts. A tuple-level native
critical-scan equivalence constructs fresh own words internally.
Constructed parameter heads now map to the native complete sampler
annihilators for EVERY raw column, with original declared row degrees.
NoCritical interval and consecutive-prefix comparison queries specialize
to their own native physical columns, with original coefficient budgets
and one finite target bound for both probes and all derivative orders.
All complete raw sampler heads now have original Binary uniform degree,
positivity and parameter coefficient budgets over EVERY prefix/AUX. Actual
term queries also have original spatial-degree boxes. Proper parent and
terminal heads and windows have literal parameter maps; final principal
query composition and complete graph predicate transport remain separate.
One finite coherent family now covers EVERY actual full-row root across
the large-parameter interval, with fresh literal native words at dyadic
radii. The literal radial value-certificate reader, coefficient source and
same-center native selection/trailing guards are also closed. Joint
descriptor feasibility/component association and full graph guard/edge
transport remain separate.
The whole installed critical-zero scan now preserves acceptance and rejection
on fresh own sampler words beyond an original Binary cutoff. Literal near
and rank principal queries have exact own-column maps and complete original
finite-variable, spatial and parameter coefficient boxes. Whole native
Atomic/Local/NoCritical/Edge tuple incidence and joint descriptor feasibility
remain to be proved.
Literal saved historical cut rules, kinds and declared degrees now match
the canonical instruction. Full clipped lower-choice coefficient probes
specialize on their OWN physical parent columns and have original finite
variable, spatial and parameter coefficient boxes. Whole historical trace
guard acceptance and its shared full-tuple incidence remain separate.
The inner native critical-child search now equals one explicit formula
over a shared parent/child raw-tuple pair, with actual bank agreement,
correlation and both endpoint signs. Joint descriptor roots now yield
same-component core candidates and fresh own Replay words, with actual
center/value guard binding. Full grid/cut-stratum sampling and native
cross-source component checking remain open, as does whole graph transport.
The complete native marked test and both historical scans now transport
together to one fresh own word. The whole bounded NoBad search transports
on the same base curve with one original cutoff. Native Near/Rank statistics
and guards transport on their actual own-word curves. Checked Atomic grammar
survives fresh-word replacement; companion correlations follow from the
complete critical scan. Concrete joint coefficient and principal features
preserve actual squarefree-selection guards. Companion coordinates, complete
Near/Rank witnesses, Local/Edge transport, uniform all-role stabilization,
descriptor stratum sampling and native cross-source component association
remained open at that checkpoint. The completed native joint-witness route
now proves both original language-membership theorems listed above.

### Final integration checkpoints

The polynomial-zero connectivity extension now proves an effective ball
cutoff from the original dimension, degree and coefficient mass. Beyond it,
any two endpoints in the ball are joined in the bounded zero set exactly
when they are joined in the entire zero set. Singular and unbounded zero
sets are included; the cutoff has native binary controls. See
`EffectivePolynomialBallConnections.joined_iff_after_cutoff` and
`component_iff_after_cutoff`. The bounded external-sample association checker,
two-label integration and both original connectivity PSPACE endpoints remain
unfinished.

The actual OLD/EXTERNAL provider atomic checker now has a native PSPACE
theorem, with derived record-bank controls and same-point replay. Canonical
marked endpoint roots realize its actual saved prelude, and accepted words
have a polynomial size bound for each provider. Point/frame/signature and
replay-to-prelude readbacks are proved. Genuine OLD and EXTERNAL endpoints
now construct fresh accepted depth-zero seeds in the same marked component.
A fresh accepted recursive child now preserves the entire prescribed point,
all earlier fields and the literal provider while increasing depth by one.
Every accepted parent with depth room has an equal-point child connected by
an actual native identity edge. Native NoCritical and NoBad are equivalent
to their original frozen-slice geometric conditions. Genuine matched slab
interiors now construct accepted proper children on independent own words,
with the prescribed entire endpoint points and preserved earlier fields.
The actual native proper-edge constructor and graph soundness are proved.
Full frozen-depth induction now makes native reachability equivalent to
geometric connectivity between accepted depth-zero representatives of one
provider. A genuine path to a seed's own marked prelude constructs a reachable
terminal marked anchor. Native OLD/EXTERNAL association, both marked-anchor
searches and a shared two-label witness have PSPACE checkers, with original
joint-header vertex budgets. The original stratum labels are now equivalent
to the native shared-sample witness. The actual sampler preserves the anchor
grid, using an enlarged catalogue that retains every old coefficient index.
A genuine radial descriptor lifts to that stratum with both labels and its
entire radial tuple retained. Principal and value interval truth is preserved
on actual stratum components. Native grid checking now verifies all selection
receipts internally on the same sampler word. The original Boolean frontier
edge is exactly projected sample equality or oriented guarded joint feasibility.
Exposing endpoint formulas through tautologies preserves the space and reduces
point reachability to existing auxiliary samples. Native interval checking,
the same-word guarded witness, and both original Boolean graph decisions are
complete. The final theorems have no remaining computational premise.

## Former RESEARCH checkpoints

Savitch is relevant to reachability in an implicitly represented exponential
graph, as in roadmap and motion-planning consequences. Vertices, recursion
stacks, and adjacency evaluation need workspace proofs. A free adjacency oracle
would omit an essential cost.

The ETR procedure instead uses deterministic algebraic enumeration and sign
testing; its completed proof does not require Savitch. Generic Savitch support
in another library does not automatically transfer an algorithm or class
membership between machine models. Formalizing the report's roadmap and
connectivity results requires those additional constructions and bounds.

The `LeanCannyConnectivity` target now provides native fixed-width graph
reachability and whole-graph connectivity with polynomial-space edge routines.
`SpaceReachability` derives the space-only interface from the pinned native
Savitch theorem, including the edge workspace. `ImplicitGraphPSPACE` guards
invalid records and scans all valid vertex pairs with binary counters. Width
zero and empty graphs are included.

`Connectivity/ClosedPathCover` proves the topological transfer for finite
relatively closed, path-connected pieces. `BitPathCover` connects this theorem
to the actual graph routines. `FormulaPathCover` uses ETR to decide whether
pieces are nonempty and intersect; its effectivity hypotheses are FP query
writers and a unary FP width. The geometric cover is still supplied, not
constructed. Its existence alone would not prove those quantitative bounds.
Endpoint identifiers may themselves be computed in polynomial space. A
binary-counter scan of piece/endpoint ETR intersection queries locates pieces
containing singleton-described endpoints, including irrational points.
Polynomial-time explicit formula writers are a sufficient condition for this
adapter, not a bound proved for Canny's roadmap pieces. `BitPathCover` also
supports other polynomial-space adjacency implementations, including implicit
algebraic representations.

`Connectivity/Problem` and `Connectivity/Encoding` specify the two geometric
languages. Endpoint formulas must denote unique points; arbitrary real
constants and a rational-point sampling assumption are absent. No membership
theorem for either connectivity language is claimed: effective cover
construction and the total encoded connectivity decision procedure remain
to be supplied.

`Connectivity/InputFP` proves polynomial-time recognition of the complete
canonical encodings. `Connectivity/EndpointValidation` proves
`validEndpoints_mem_PSPACE` unconditionally on all bitstrings. It rejects
malformed inputs and inconsistent, nonunique, or out-of-dimension endpoint
descriptions. Two copies of an endpoint formula use even and odd variables;
a polynomial-space coordinate scan asks ETR whether two solutions can differ.
`ETR/InterleaveFP` certifies the copying transformation without modifying
integer payloads, and `ETR/FormulaArityFP` supplies the exact syntax bound.
This validation result does not test membership in the described space or
path reachability.

The report's Theorem 3.5 invokes the roadmap algorithm of the cited 1987
paper; it does not prove the geometric roadmap construction within the report.
The present target includes arbitrary Boolean formulas and singular,
noncompact sets. Existing tube and critical-sampling lemmas do not establish
component-preserving roadmaps for these inputs. Canny's later
[general semialgebraic roadmap paper](https://doi.org/10.1093/comjnl/36.5.504)
provides a separate generalization beyond the earlier compact, regular case.
That geometric construction and its quantitative representation bounds remain
substantial missing formalization work.

`Connectivity/FrontierCover` extends the graph transfer to finite decompositions
with pieces that are not closed. An edge records a point of one piece in the
relative closure of the other. Finite graph clusters are clopen; consequently
every path induces a graph walk. If boundary points can access the corresponding
piece by a path, walks conversely give paths. Both closures and paths can be
taken in the subtype of the original space, so a missing boundary point cannot
silently join two components.

`Geometry/AlgebraicBranchLimit` proves endpoint continuation for bounded
continuous algebraic branches. The cluster values of a continuous real branch
form an interval. Factoring out the lowest parameter power leaves a nonzero
univariate polynomial that annihilates every cluster value. Compactness supplies
a cluster value; the finite root set and interval property force convergence.
Translation and reflection give both endpoints, and coordinatewise convergence
extends vector-valued branches continuously to the closed parameter interval.
The statement permits singular endpoint fibers and identically zero direct
specializations before removing the parameter factor.

`Connectivity/AccessibleArc` derives boundary accessibility for these algebraic
arcs from their continuous extensions. These lemmas do not assume nonvanishing
derivatives at their endpoints. The coordinate equations must still be supplied.

`Geometry/RootBranchLocal` constructs a continuous branch on a closed parameter
interval around each regular root of a system. Every sufficiently nearby root
lies on this branch. It derives the interval and its continuity from the
implicit function theorem; no root family is assumed.

`Geometry/RootProjection` constructs local projection charts from those
branches. A proper root projection has compact regular fibers; the charts make
them discrete and hence finite. A closed-map covering theorem then gives a
covering over every interval of regular values. `Geometry/ProperProjection`
also derives properness from closedness and a fixed compact coordinate bound;
the parameter itself need not be bounded.

`Geometry/CoveringBranches` proves completeness and uniqueness of global
branches by unique continuous lifting over a simply connected base.
`Geometry/RootBranches` applies this to the root projection over an open real
interval. `Connectivity/RegularRootArcs` derives compact coordinate bounds from
properness, applies the algebraic endpoint-continuation theorem, and proves
that all extended endpoints satisfy the original equations. No regularity at
the endpoints is required.

`Geometry/RootBranchCount` bounds a fiber by the product of degrees of its
nonzero coordinate equations. For a nonzero bivariate polynomial, only finitely
many parameter values give the zero coordinate polynomial. Thus every open
interval contains a simultaneous good specialization for finitely many such
equations, and the branch count is bounded by their coordinate degrees.
This is a cardinality bound, not an effective root encoding or coefficient
bound.

`Connectivity/SlabCover` glues complete interior arcs to accessible covers of
the endpoint fibers and proves the resulting finite frontier graph preserves
both paths and preconnectedness of the entire slab. `RegularRootArcs` constructs
this cover from a proper regular root system and its endpoint-fiber covers.
`Connectivity/ArcIncidence` proves that arc-to-slice incidence is endpoint
membership, distinct interior branches have no incidence, distinct slices have
no incidence, and same-slice incidence reduces to the fiber's own relation.
These results hold for nonclosed slice pieces and use relative closures.

`Connectivity/BitFrontierCover` transfers such accessible covers to the native
polynomial-space implicit-graph algorithms. Both frontier adjacency and endpoint
location may use polynomial space, and that workspace is included in the bound.
No general closure-membership oracle or effective roadmap is assumed to exist.

The unproved part is the uniform construction for arbitrary Boolean polynomial
descriptions: suitable critical root systems and slices, a component-preserving
recursion through singular and noncompact cases, and polynomial bounds on the
vertex descriptions and graph routines. The regular-slab results do not supply
these obligations, so the two full connectivity PSPACE theorems remain open.

`Geometry/PolynomialRootFamily` derives smoothness of an explicit square
polynomial family in the parameter and unknowns. Its analytic derivative in
the unknowns is invertible exactly when the evaluated formal Jacobian
determinant is nonzero. `ProperProjection` now also derives properness for a
closed family lying on the level graph of a proper function, without a fixed
global compact bound on the unknowns.

`Algebra/RegularFiberSpecialization` constructs an exceptional parameter factor
when all generic roots are regular in every field extension. The singularity
ideal becomes the unit ideal over the fraction field; clearing denominators
puts a nonzero parameter scalar in the original ideal. Its nonvanishing rules
out singular specialized roots. `ProjectionRegularSpecialization` applies this
to the actual reciprocal/level/partial equations and their square Jacobian.
`ParameterLineSpecialization` chooses integer direction coordinates so the
joint exceptional polynomial remains nonzero as a univariate level polynomial.
The integer coordinates and univariate degree are bounded by the joint
exceptional polynomial's total degree; that degree has no input-size bound yet.

`Geometry/ProjectionCriticalBranches` constructs spatial projection-critical
equations with the level retained as a polynomial parameter. Removing the
reciprocal coordinate is necessary here: it may diverge at exceptional levels
even when the spatial curve is bounded. A critical-value annihilator excludes
singular hypersurface levels, so the reciprocal can be introduced temporarily
at every retained spatial root to transfer the nonsingularity certificate.
For any proper polynomial level function, a constructed integer direction and
finite exceptional level set make its spatial root projection a finite-sheeted
covering. No regularity hypothesis on the original polynomial is assumed.
The theorem does not yet prove that these critical curves, together with
recursive slices, preserve all components of the original semialgebraic set.

`Geometry/RegularFiber` restricts implicit-function charts to actual level
sets. These charts take values in the derivative's kernel, which may vary
with the point. Consequently regular fibers are locally path connected;
compact regular fibers have finitely many connected components, each also
a path component. Compactness and connectedness are not assumptions of the
local chart or local path-connectivity results.

`Geometry/ComponentCriticalSampling` maximizes a fixed projection separately
on each compact regular fiber component. Components are relatively open, so
each such maximum is a local maximum on the whole fiber. Normalized Lagrange
multipliers put it in the actual spatial critical system. Every point has a
path to its sample inside the same fiber. The map from critical roots onto
fiber components is surjective, so any finite bound on the root set bounds
the number of components. Combining properness, the constructed integer
direction, and a critical-value annihilator gives finite sample sets covering
all components at every level outside a finite exceptional set.
The full recursive roadmap for general Boolean inputs and its polynomial-space
representation bounds remain unproved.

`Connectivity/OpenPathCover` proves that paths induce finite overlap-graph
walks even for an infinite open cover. `Geometry/FiberPathPersistence` applies
this to open slice neighborhoods: overlap parameters form open sets under an
open fiber map, so each finite walk persists near its original parameter.
Continuous sections retain their endpoint neighborhoods, making their fiber
connection an open condition.

`Geometry/FiberPathSeparation` proves the complementary persistence statement
for proper maps with locally path-connected fibers. A fiber component and its
complement are disjoint compact sets. Disjoint ambient neighborhoods separate
them, and closedness of the projection keeps nearby fibers within their union.
Fiber connection of continuous sections is therefore also closed, and hence
constant on a preconnected parameter space.

`Geometry/LocalProductFibers` constructs the slice cover and proves openness and
fiber local path connectivity from local product charts.
`LocalProductBaseChange`
pulls these charts back to any parameter subset. `RegularComponentTransport`
constructs the charts by the implicit function theorem for a proper smooth map
on a regular-value region; regularity outside that region is not assumed.
`PolynomialComponentTransport` derives all analytic hypotheses from polynomial
evaluation and a critical-value annihilator, giving an actual finite exceptional
set for this transport theorem.

`Connectivity/FiberSectionCover` saturates each continuous section by its entire
fiber component. Generalized persistence and separation allow both endpoints
and their common fiber parameter to vary over any parameter space. Thus each
saturated piece is clopen in the total slab. It is path connected, as is its
restriction to any path-connected parameter region. Complete component samples
give a cover of every original point. Overlap reduces to connection of the two
samples in a single fixed fiber, giving both point and whole-space graph tests.

`Algebra/LevelProjectionSpecialization` now retains the coordinate-annihilator
certificate used to prove finite fibers. `ProjectionRegularSpecialization`
chooses one integer direction preserving this certificate and the regularity
certificate simultaneously. `Geometry/ProjectionCriticalBranches` transfers
the resulting nonzero bivariate coordinate equations to actual spatial roots.
`Connectivity/RegularRootArcs` retains the sample-root anchors when extending
the complete branches. `PolynomialSlabCover` combines these results into an
actual finite clopen path cover of the original proper polynomial slab, with
continuous indexing branches on the closed interval and both connectivity
tests reduced to the critical-root graph in one sample fiber. The coordinate
annihilators and exceptional polynomials still lack input-size bounds.

`Geometry/ConnectedSlabLimit` proves that a decreasing family of compact
preconnected sets has preconnected intersection. The limit of a slab component
at an endpoint equals the intersection of its closed short tails. Properness
makes these compact; path connectivity of the tails makes the entire endpoint
limit connected and nonempty. Reflection handles the upper endpoint. This
argument allows multiple limit points and imposes no endpoint regularity.
`Connectivity/FiberSectionLimit` applies it to the actual saturated pieces.
`EndpointAttachment` uses a recursively supplied finite accessible endpoint
cover to join any two points of this connected limit in the endpoint fiber.
A continuous indexing-branch extension then attaches every boundary point to
the slab component through that slice. The recursive slice cover itself is
still an obligation, not an assumed uniform semialgebraic construction.

`Connectivity/ClopenPathCover` saturates a finite accessible or closed path
cover by its frontier-graph components. The resulting pieces are clopen and
path connected, with the same labels and the same empty records. For native
bit-indexed covers, `BitFrontierCover.component_membership_computable` decides
membership using guarded native PSPACE reachability and a locator for an
original piece containing the queried point. Closed path covers reuse their
overlap routine as frontier incidence, so this operation composes recursively.

`Connectivity/ComponentSlabCover` constructs a closed path cover of the entire
original closed slab from its saturated interior pieces and recursively supplied
clopen endpoint covers. Its auxiliary middle pieces are closures of interior
pieces together with chosen endpoint components. Connected endpoint limits
prove that these equal the union of the open interior piece and those two
endpoint pieces. This removes closure queries from overlap and record validity.
The continuous critical branch joins all three parts, proving path connectivity.
The final cover keeps only one selected pair of endpoint components per interior
label, so its index is a sum of the three label families, not a product at each
dimension. Selectors remain query functions and still need effective endpoint
representations. `PolynomialSlabCover.exists_closed_cover` supplies all interior
hypotheses from the original proper polynomial, preserves both connectivity
tests, and allows singular endpoint fibers. Recursive endpoint covers themselves
are still inputs to this theorem.

`Geometry/HypersurfaceSweep` constructs genuine local products for a sweep
on a fixed hypersurface. The combined smooth map `(q,g)` is restricted to
`{c} × S`, then explicit source and base homeomorphisms identify it with the
sweep on `q=c`. Its derivative kernels supply the chart models. Properness of
`q` makes each fixed hypersurface compact, hence any continuous sweep on it
proper. The constructed atlas proves moving-endpoint component persistence
and section transport within its regular sweep region.

`Algebra/CoordinateCriticalValues` constructs a nonzero polynomial vanishing
on the regular critical values of a coordinate projection on a fixed level.
When all non-base partials vanish, the chain rule and the nonzero base partial
force every coefficient-field derivation to kill the swept coordinate.
Minimal-prime annihilators combine into one polynomial. This works over
extension fields and gives rational coefficients for rational input equations.
`Geometry/PolynomialHypersurfaceSweep` applies it to a regular polynomial
level: a non-base partial gives an explicit right inverse of the combined
derivative. A critical-value factor first constructs regular hypersurface
levels; their coordinate sweeps then have constructed finite exceptional sets,
proper projections, and regular product atlases. Certificate sizes remain open.

`Algebra/FixedLevelProjectionJacobian` removes the independent-level hypothesis
from generic critical-root nonsingularity. Derivations in the independent
direction coordinates supply all tangent directions. A left-kernel argument
and the nonzero base partial supply the remaining normal direction.
`FixedLevelRegularSpecialization` clears the generic singularity ideal and
chooses one integer direction retaining finite simple extended critical roots
and nonzero coordinate annihilators over every extension field. Its coefficient
field may already contain a sweep parameter. The direction bound still depends
on an exceptional polynomial with no input-size estimate.

`Geometry/CoordinateSlice` replaces the swept coordinate by a polynomial
parameter over the original coefficient ring. Evaluation agrees exactly with
the original polynomial on the coordinate slice. An explicit homeomorphism
identifies each hypersurface sweep fiber with this equation in the remaining
coordinates, including irrational values and empty fibers. The coordinate
count drops by one. Closed embedding of coordinate insertion transfers
properness, and its derivative transfers combined-map regularity to the slice
equation. Fiber paths correspond exactly under this homeomorphism.

`Algebra/ProjectionCriticalFamily` defines the critical equations over an
arbitrary parameter coefficient ring and proves that coefficient maps commute
with the equations and their formal Jacobians. `UniformCriticalSpecialization`
chooses one integer direction over its fraction field, clears the coordinate
annihilators and the generic nonsingularity certificate to the original ring,
and constructs a single nonzero factor retaining all these certificates under
every accepted field specialization. These certificates have no input-size
bound yet.

`Geometry/ParameterizedCriticalBranches` transfers the certificates to the
spatial system at regular slice roots. The reciprocal variable is used only
inside the proof; its potential divergence at endpoints does not affect the
spatial family. Every component of each compact regular specialized slice
has a sample in precisely this system. `Connectivity/CoordinateCriticalArcs`
uses compactness of the original fixed hypersurface to prove properness and
construct complete anchored critical arcs with continuous endpoint limits.

`Connectivity/CoordinateSlabCover` saturates these branches into a finite
clopen path cover of the entire original regular coordinate slab. Its overlap
graph is defined by connection of the critical samples in the actual
lower-dimensional polynomial slice. Connected endpoint limits and continuous
critical branches give the closed-slab composition data. Recursive clopen
endpoint covers complete the whole closed coordinate slab, preserving point
and whole-space connectivity. Endpoint covers transfer along an explicit
slice homeomorphism with unchanged labels. This still assumes recursive
endpoint covers; it does not supply the general effective recursion.

`Connectivity/ZeroDimension` supplies uniform native algorithms for the
empty-tuple base case, retaining well-formedness and singleton endpoint
validation. `OneDimension` reduces whole-space connectivity of an arbitrary
Boolean real-line description to the absence of an existential gap witness.
Its polynomial-time query writer uses three disjoint copies of the input.
`OneDimensionPoint` proves that real-line paths exist precisely when all
intermediate points are present, then constructs the separating-point query
for formula-described endpoints. Its native polynomial-space algorithm
combines singleton validation, both endpoint membership tests, and absence
of a separator. These base cases include empty, singular, and unbounded sets;
they do not settle the varying-dimensional languages.

`Algebra/CharacteristicLowestBounds` and `MacaulayLowestBounds` give explicit
degree, mass, and scalar coefficient-bit bounds for the lowest coefficient of
the padded characteristic numerator. This coefficient is nonzero over a
domain. `Geometry/MacaulayRegularPersistence` now proves that it vanishes at
regular projective-chart roots, using the proved quotient factorization.
Thus coefficient bounds for polynomial division are unnecessary here.

`Algebra/AffineCoordinateSystem` homogenizes an arbitrary square affine system
and adds `u X₀-Xᵢ`. `Geometry/AffineCoordinateEliminant` proves that adding this
coordinate equation preserves Jacobian invertibility and constructs an actual
nonzero coordinate polynomial at every regular real root. Its degree is at
most the fixed-width Macaulay matrix count, and its integer coefficient-bit
budget is explicit. Bivariate characteristic bounds retain a sweep parameter.
`UniformAffineCoordinates` constructs bounded coordinate polynomials and the
product of their leading coefficients as a nonzero specialization factor;
both parameter degree and factor mass are bounded. `ProjectionCriticalBounds`
and `BoundedCriticalCoordinates` apply these estimates to the actual spatial
critical equations, with explicit dependence on the supplied integer direction.
The chosen direction and the separate factor excluding singular roots still
lack input-size bounds; the native recursive query construction is also open.
`RegularCoordinateRootCount` uses these constructed equations to bound every
retained regular fiber by `N^n`, where `N` is the fixed-width matrix count.
This equals `2^(n*(n+1)*W)`, giving an explicit cardinality allowance for binary
branch labels. Locating and querying those labels still need native routines.

`Geometry/AffineCoordinateFinite` extends the same constructed coordinate
eliminant to finite affine zero sets over algebraically closed fields, including
singular roots and projective zeros at infinity. Real roots inherit this result
from any algebraically closed extension. `UniformAffineCoordinates` and
`RegularCoordinateRootCount` retain their original degree, mass, and binary
label allowances for these singular finite fibers.

`Geometry/CoerciveConstrainedSampling` minimizes on a closed coordinate slab
isolating a projected zero. Its bounded minimizers have a convergent subsequence
whose limit retains that coordinate; they are eventually interior critical
points. `PolynomialLimitAnnihilator` now accepts eventual annihilation.
`FiniteCoordinateAnnihilator` consequently constructs one bounded nonzero
integer polynomial for every finite coordinate image of a polynomial zero set,
even with positive-dimensional spatial fibers. Its mass-exponent allowance has
the polynomial binary-length estimate already proved in `CoerciveRadiusBits`.

`Geometry/CoordinateSweepBounds` applies this result to the sum of squares
defining the coordinate critical locus of a regular integer hypersurface. It
constructs an integer exceptional factor with explicit degree and mass bounds
from dimension, source degree, and source mass exponent. Outside its roots the
combined hypersurface/sweep derivative is surjective. This bounds the sweep
critical values; the generic direction and the separate critical-root
regularity factor remain to be bounded.

`Geometry/SystemCoordinateBounds` gives the same projected-value theorem for
arbitrary finite integer polynomial systems using their sum of squares.
`SingularParameterBounds` includes the formal spatial Jacobian, bounds its
degree and mass from the equations, and constructs a bounded exceptional factor
when there are only finitely many singular parameter values. Singular bad
fibers may have positive dimension. A qualitative real regularity factor
suffices; none of its arithmetic bounds are used. Transferring this result to
the parameter-ring critical systems requires an effective integer polynomial
representation of their parameter variables.

`Algebra/IntegerParameterFlatten` now supplies that integer polynomial
representation, with the parameter in coordinate zero. Evaluation and spatial
partial derivatives commute with this representation, as does the formal
spatial Jacobian. Its degree is bounded by the sum of spatial and parameter
degrees, and its mass exponent is bounded using source coefficient mass and
the number of spatial monomials. `Geometry/ParameterizedSingularityBounds`
transfers the bounded exceptional factor back to the original equations over
`ℤ[T]`. `BoundedCriticalCoordinates.exists_bounded_regularity` applies it to
the actual spatial critical equations. Only a qualitative regularity factor
is supplied; its degree and mass are not premises. The chosen integer direction
and native coefficient/query access still require effective bounds and
constructions.

`Geometry/UniformCriticalRegularityBounds` connects this factor to the actual
uniform integer direction from `UniformCriticalSpecialization`. Regularity of
the original slices outside any qualitative nonzero factor suffices. The
reciprocal-variable Jacobian transfers regularity to the spatial system, and
the new construction bounds its exceptional factor independently of both
qualitative witnesses. Its mass budget still uses the existential direction
allowance; bounding that allowance from the input remains open.

`Algebra/IntegerParameterCoefficient` proves the exact scalar coefficient
identity for integer parameter substitution. `IntegerParameterCoefficientSpace`
implements it by splitting a fixed-width binary exponent word into the
parameter block and spatial tail, making one native source coefficient call.
The adapter retains its literal behavior on short words and at width zero.

`Encoding/FixedWidthQueryBinary` certifies exponent guards with binary degree
allowances. `FixedWidthDerivativeBinarySpace` extends the existing exact
derivative reader to those allowances, avoiding a unary conversion of recursive
degree values. `FixedWidthCriticalSpace` evaluates the base polynomial row or
the difference of two derivative coefficients scaled by a binary direction
entry. `ParameterizedCriticalCoefficientSpace` connects this native program to
the actual critical equations over `ℤ[T]`, with the parameter variable kept
separate from the spatial partials. These are native coefficient routines from
a supplied source reader; the recursive records and geometric graph queries
still need to be constructed.

`Algebra/ProjectiveDirectionGrid` supplies a quantitative direction-selection
step for homogeneous systems. One root-free specialization selects a nonzero
maximal Macaulay minor, whose parameter degree is bounded by the column count
times the source parameter degree. A grid with this allowance contains an
integer specialization retaining root-freeness over every coefficient-field
extension. The allowance has an explicit binary-length bound. Applying this
step to the original affine critical family still requires constructing the
root-free projective system, including exclusion of roots at infinity; the
input-size bound for that family’s chosen direction is not yet proved.

`Algebra/FermatCriticalInfinity` proves root-freeness of the pure-power critical
infinity equations, first at the coordinate direction and then under any
injective generic coefficient map. `HomogenizationAdditive` supplies the
additive identities for the explicit homogenization.
`FermatCriticalHomogenization`
identifies the actual affine-chart and infinity equations for an arbitrary
lower-degree polynomial plus a pure-power leading sum.

`HomogeneousBadSystem` appends the homogenized spatial Jacobian.
`NestedTotalDegree` bounds parameter-coefficient degrees through products,
determinants, differentiation, homogenization, and variable permutations.
`FermatCriticalBadSystem` gives the resulting singular-critical system explicit
spatial and direction-degree bounds. `FermatCriticalGeneric` proves it has no
generic projective root: affine roots are nonsingular and infinity roots are
excluded by the original critical equations.

`FermatBoundedCriticalDirection` consequently constructs a bounded natural
critical direction for a pure-power-leading hypersurface regular over field
extensions. No exceptional-direction factor or degree allowance for such a
factor is supplied. Its direction bit width is at most
`(n+2)*(2*n+N.size+4)+n+1`, for `n+1` spatial coordinates and source degree `N`.
`Encoding/FermatCriticalDirection` constructs an actual record of `n` such
blocks and certifies native field access and polynomial record length, using a
binary source degree. The extension-field regularity premise is explicit;
real regularity alone does not supply it. The original input reduction still
needs to construct this source shape, select a regular level over complex
extensions, and supply the recursive geometric queries.

`ETR/ComplexDifferentialSymbolic` proves polynomial equality for the shared
derivative transformation by evaluation over `ℂ`. Applying it twice computes
the value, two first partials, and their mixed second partial.
`ComplexTermHessian` identifies these outputs with the original compiled term.
`ComplexCircuitCapturedTransform` and `ComplexCircuitShift` supply native
parameter-dependent gate substitution and uniform wire relocation.
`ComplexHessianCircuit`, `ComplexHessianEncoding`, and `ComplexHessianFamily`
initialize fresh copies and prove simultaneous completion at one shared input
point, including their native polynomial-time generation costs.
`ComplexKernelRow` and `ComplexKernelRowEncoding` compute the required linear
combinations of Hessian rows, kernel-vector sums, and first-derivative critical
equations. `FermatSweepKernelCertificate.affine_bad_iff` expands the existing
affine chart predicate into these equations.

`ETR/ComplexCriticalKernelCircuit` assembles the Hessian copies, kernel rows,
normalization, and zero constraints into one query. Its computational part is
one acyclic program; `ComplexCriticalKernelCorrect` proves an exact normalized
root equivalence by constructing one global completion. The encoder includes
every source, direction, index, and loop cost. `ComplexCriticalKernelPSPACE`
provides native feasibility and emptiness certificates for compiled source
terms, with the in-range chart condition kept separate from the total cost
proof. `ComplexCriticalKernelFinite` transfers values, gradients, Hessians,
and normalized roots through one coefficient-map and variable-renaming identity.
`ETR/ComplexCircuitReindex` supplies native captured wire maps with independent
input and auxiliary-wire behavior. `ComplexFrozenSource` redirects variable
zero to a computed integer sample and shifts positive variables down one
coordinate, preserving the original compiled body. Its native encoder charges
the actual validated source and sample literal. `ComplexFrozenSlice` proves
the exact coefficient-specialized coordinate-slice identity.
`Encoding/FermatFrozenSource` reads the actual certificate sample in binary and
constructs the frozen program and all fresh-wire metadata.

`ComplexSamplePowers` redirects a shared binary power-sum circuit to that
computed sample and the spatial coordinates. `ComplexSampledSource` joins it
to the low source and dyadic regularization, with one acyclic program and an
exact symbolic polynomial. Its native encoder and critical-kernel tests retain
both binary exponent words, including the scale that is never serialized as
an integer literal. `Encoding/FermatSampledIdentity` proves its coefficient-map
identity with the existing finite-coordinate Fermat certificate, including the
constructed regular integer source. `FermatAffineQuery` gives native bad-root
and emptiness tests agreeing with the original affine chart predicate.
`FermatValidity` scans these and the infinity tests over every normalized chart
and proves exact agreement with the original `Valid` predicate.
`Computation/SpaceFunctionQuantifiers` supplies the native bounded scan with
arbitrary space-bounded children and caps its binary counter before unary
conversion. `FermatDirectionChoice` searches the fixed-width records and proves
that the constructed regular integer source supplies a valid candidate. Its
selected record has native polynomial-space computation and the original
geometric validity guarantee; neither a validity procedure nor a direction is
assumed. The selected record can be retained with the input for subsequent
polynomial-time field access.
`FermatTermPreparation` derives an even degree and a coefficient-mass allowance
from normalized term size. The native selector then needs only the source
reader and unary dimension. The actual arity bound implies validity and
generic-slice regularity of its selected direction. These source-preparation
theorems do not establish component preservation for the original formula.

`Geometry/CompactSublevelComponents` proves that components commute with
decreasing compact intersections at a retained point. For a continuous
nonnegative energy on a compact set, membership in the zero-set component is
equivalent to membership in every positive sublevel component. Distinct zero
components therefore separate at some positive tolerance, with no regularity
assumption at the zeros. This limit theorem does not supply a finite effective
tolerance or identify connected components with path components.

`Geometry/CircleSublevelLift` constructs the level equation
`g(x) + u² + v² = e` over the sublevel `g(x) ≤ e`. A continuous square-root
section makes the projection a quotient map. Its fibers are connected
circles, including the radius-zero singleton, so the projection preserves
exact components and preconnectedness, also for the empty sublevel. This
avoids the two-point fibers of a single squared slack coordinate.
`CircleSublevelLevels` constructs its derivative, smoothness and properness,
and proves that its critical values equal those of the original energy.
`PurePowerSublevelLift` constructs odd coordinate-power homeomorphisms and
transfers component preservation to two slack terms of degree twice an odd
number. `PurePowerSublevelLevels` proves the corresponding derivative,
critical-value and properness results. The encoded-term degree is now
`2 * (2 * normalizedSize + 1)`, matching this source shape.

`RegularSublevelComponents` transports the lifted regular fibers over a
positive interval with no critical values. Compact sublevel limits then
identify the component relation on the original zeros with that of any
sublevel in the interval, without regularity at the zeros.
`GeneralCriticalValueBounds` applies bounded finite-image elimination to the
actual augmented critical-value system. It constructs bounded integer
annihilators even for singular or positive-dimensional critical-point loci.
`Encoding/GeneralRegularLevel` computes the resulting dyadic exponent in
native polynomial time from unary dimension and binary degree/mass controls.
`EffectiveSublevelComponents` gives the explicit dyadic component-preservation
theorem for nonnegative integer polynomial energies with compact sublevels.
It concerns connections between zeros, and supplies no path recovery for the
original zero set or complete Boolean-input reduction.

`BoundedPositivePerturbation` preserves that zero-component relation for every
set between the zero set and its safe sublevel. A bounded nonnegative penalty
gets an explicit dyadic coefficient, retaining the relation at every level in
the upper half of the safe interval. A coordinate radius gives a pure-power
penalty bound with derived exponent.
`BoundedZeroSource` constructs the integer energy
`q(x)² + (sum(wᵢ²) - 2^(2R))²` in two extra variables. Its sublevels are
compact,
and its degree, coefficient mass and zero-coordinate radius have explicit
bounds. `BoundedZeroComponents` constructs its circle quotient onto the
original zeros in that closed ball, preserving exact components and
preconnectedness. `BoundedZeroPerturbation` then constructs the positive
pure-power perturbation preserving connections between lifted original zeros.
`BoundedRegularSource` shifts by the safe interval's lower endpoint before
applying the existing integer regularization. The tiny regular level stays
inside the component-preserving interval. `BoundedRegularComponents` proves
exact polynomial and level semantics, properness, and the component relation
between original bounded zeros and their constructed lifts to this regular
pure-power hypersurface. Regularity holds over rational field extensions.
`Encoding/BoundedZeroControls` and `BoundedRegularControls` compute the exact
scalar controls in native polynomial time from unary dimension and binary
degree, mass and radius allowances.
`ETR/ComplexBinaryScale`, `ComplexZeroEnergy`, `ComplexScaleShift`, and
`ComplexBoundedLow` compute the enormous radius, scale and shift on shared
wires. `ComplexBoundedSource` joins these to the frozen original term,
sampled radial and pure-power sums, and outer regularization in an acyclic
program. Its output is proved equal to the intended integer polynomial.
`ComplexBoundedEncoding` proves native polynomial-time source encoding and
unary wire/operation bounds in the original source and binary exponent words.
`ComplexBoundedPSPACE` gives native critical-kernel tests for this circuit.
`Encoding/BoundedSampledIdentity` identifies its complex coefficient image
with the coordinate slice of the actual geometric regular source, including
dimension zero. `BoundedSourceWriter` derives degree and mass allowances from
the original encoded term, computes all exponent words and reads the actual
sample field. Its native writer requires only original source, dimension,
radius and record reader cost certificates. `BoundedAffineQuery` and
`BoundedValidity` connect the resulting affine/infinity tests to this source's
existing finite `Valid` predicate. `BoundedDirectionChoice` selects a valid
record by bounded native polynomial-space search, with geometric existence
proved from the derived controls. Record selection and actual source
serialization compose in native polynomial space.
The regular-source theorem compares lifted original points; it does not claim
that every regular-source component meets their image or recover paths in
the original singular set.

`CircleSublevelPaths` proves path connectedness of every circle fiber,
including radius zero, and exact path-component preimages under projection.
`LiftPaths` transfers this to the pure-power and bounded sphere zero sources
through their actual coordinate homeomorphisms. Arbitrary points in the
same lifted fiber can be joined, and paths between chosen section points
correspond exactly to paths in the original sublevel or bounded zero set.
These results do not transfer paths from a positive perturbed sublevel to
its singular zero set.

`BoundedMarkedComponents` describes the relevant regular-source subset by
the single polynomial obtained by renaming the old sphere zero energy.
Every marked point is joined to the constructed lift of its original
projection. Marked source component membership is equivalent to original
bounded zero component membership; original preconnectedness means that all
marked points lie in one source component, including the empty case.
`Computation/MarkedGraphPSPACE` proves a native polynomial-space test with
separate flags for marked endpoints and valid traversable vertices. Paths
can use unmarked valid intermediates. `Connectivity/BitMarkedCover` transfers
this test through a finite accessible cover and charges edge, validity and
marking routines independently. `BoundedMarkedCover` specializes this to the
constructed regular source. This removes the need to prove every source
component meets the original zero image. It does not construct the actual
recursive cover or its native adjacency and marking query writers.

`ETR/ComplexCircuitFreeze` redirects the swept coordinate of an arbitrary
shared source program to an existing parameter wire, shifts the remaining
input coordinates, and translates auxiliary outputs. Well-formedness and
exact polynomial substitution are proved without expanding source terms.
`ComplexCircuitFreezeEncoding` proves native polynomial-time gate generation,
unary output addresses and unchanged operation count. Its cost theorem uses
the original source encoder, with no literal encoding of the parameter value.
`ComplexCircuitFreezeSlice` identifies evaluation with the actual coordinate
slice over any commutative ring, including irrational real parameter values.
The formulas selecting critical parameters and the full recursive query
writers are still required.

`ETR/ComplexBoundedTail` isolates the sphere, perturbation and regularization
calculation after the original polynomial and swept coordinate have been
computed on existing wires. It accepts a variable swept coordinate and
exposes the old zero-energy wire for marking. `ComplexBoundedTailEncoding`
proves native polynomial-time encoding and unary address/length bounds.
`ComplexBoundedFullSource` compiles the original term with a parameter input
and appends this tail. Its source and marking outputs have exact polynomial
interpretations; `ComplexBoundedFullEncoding` supplies native cost proofs.
`Encoding/BoundedFullIdentity` identifies these with the actual geometric
regular source and mark polynomial before choosing a sample, over any
commutative evaluation ring. `BoundedFullWriter` derives all controls from
original syntax, unary dimension and binary radius; it needs no record or
sample reader. `BoundedFullGeometry` identifies the exact finite variable
permutation, preserves the pure-power leading form, and transfers properness
and regularity over rational field extensions. The full recursive cover and
critical-parameter query writers remain required.

`Encoding/BoundedCriticalSampleIndexedMoments` and the indexed determinant
probes let a test polynomial depend on a separate binary query index while
keeping the actual sample filter, selected basis, hash and descriptor at the
original source. `BoundedCriticalSampleIndexedSign` proves native polynomial
sign access at these fixed descriptors and hash-order ordinals. Its guarded
descriptor languages are in native PSPACE.
`BoundedCriticalSampleCoordinateTests` supplies the rational-coordinate
numerator and denominator tests from the existing native modular readers and
binary degree/mass controls. Their quotient at an actual sample parameter is
the original sample coordinate, and its denominator is nonzero.
`BoundedCriticalSampleCoordinateSign` combines both signs, normalizing binary
coordinate indices while retaining the original point descriptor. Its guarded
descriptor and ordinal languages decide actual coordinate signs in native
PSPACE without a supplied coordinate-sign oracle, and reject out-of-range
coordinates and ordinals.
`BoundedCriticalSampleTermCoordinates` extends the rational sample tuple by
zero over one beyond its dimension. Native coefficient branches and uniform
degree/mass bounds apply to every coordinate index.
`BoundedCriticalSampleTermTest`
clears denominators in any supplied encoded arithmetic term, with derived
binary bounds and native modular readers. At an actual sample parameter its
sign is the original term's sign on that sample, extended by zero.
`BoundedCriticalSampleFormula` uses these signs in the native Boolean circuit
of an original formula reader. Its guarded descriptor and ordinal languages
decide exactly formula truth on the actual samples and provide native marking
flags. Invalid descriptors and out-of-range ordinals are rejected even when
the formula is true. These are sample predicates; the recursive cover and its
adjacency routines are still required.
`BoundedCriticalSampleSliceSource` supplies a second algebraic-slice backend
whose base is an actual sample descriptor. Each query separates that point
word from its auxiliary record. The original sample source, filtered basis
and selected hash remain unchanged when records are attached. Native
bivariate coefficient readers give coefficient signs and actual-degree scans
through `BoundedCriticalSampleSliceDegree`.
`BoundedCriticalSampleSlicePrincipal` computes both actual degrees before
testing a signed principal coefficient. `BoundedCriticalSampleSliceTarski`
reuses the existing native bivariate pseudo-remainder seed construction,
specializes it at the same sample parameter, and computes the exact Tarski
query. No symbolic-degree stability hypothesis is used.
`BoundedCriticalSampleSliceRootCount` derives native distinct-root and
prescribed-sign counts from three moments, together with native PSPACE sign
realizability. The zero polynomial has an empty polynomial root list. This
provides the fiber arithmetic for actual sample bases; the full recursive
coordinate families and cover still need construction.
`BoundedCriticalSampleLineCoordinates` now constructs concrete rational
bivariate coordinate families from the original sample readers. One binary
index frees a coordinate; all others remain at the same sample parameter.
Raw coordinate and modulus words are normalized before existing native
readers are called. `BoundedCriticalSampleLineCorrect` proves nonvanishing
denominators and identifies the environment with a finite coordinate update
of the actual sample.
`BoundedCriticalSampleLineTerm` substitutes a supplied encoded arithmetic
term in these families, with native coefficient readers and derived bounds.
Specialized signs agree with the term on the actual coordinate line.
`BoundedCriticalSampleLineZero` combines the native zero-polynomial flag and
distinct-root count to decide zero existence in native PSPACE, also for a
term vanishing on the entire line. The language validates the descriptor and
the free coordinate.
`IndexedMultivariateRational` now clears indexed rational substitutions in
several variables and proves that fixed-width encoding commutes with clearing.
`BoundedCriticalSampleBlockSource` frees an arbitrary contiguous block of
coordinates while retaining the same actual sample parameter and frozen
complement. Denominators stay nonzero throughout the block. Empty blocks
recover the original tuple; freezing the first free coordinate at its sample
value gives the next smaller block.
`BoundedCriticalSampleBlockEncoding` derives a uniform exponent width that
prevents collisions between the independent free variables.
`BoundedCriticalSampleBlockReaders` constructs native modular coordinate
readers, including uniform binary exponent bounds on malformed large indices.
The block offset is binary and its size is unary.
`BoundedCriticalSampleBlockTerm` constructs multivariate term polynomials
with native collected-coefficient access and binary controls for degree,
coefficient mass, and the monomial grid count. At every actual sample parameter
their signs and zeros agree exactly with the term on the corresponding free
block, with no coordinate-sign or coefficient oracle. The sign semantics also
commute with freezing the first free coordinate. These families keep the
original sample base fixed; recursive construction of new sample bases and
the complete cover remain required.
`BoundedCriticalSampleFiberRoot` gives distinct roots of an actual-sample
fiber short ordered binary labels, with native PSPACE validity. Invalid
descriptors and zero heads have no valid child labels.
`BoundedCriticalSampleFiberThom` proves that derivative signatures separate
these roots and that sparse sign monomials span all rational-valued root
functions. Individual derivative moments and sign counts are native, with
binary orders and no symbolic-degree stability assumption.
`BoundedCriticalSampleFiberRecordSpan` reuses the existing short sparse-record
encoding at the actual sample's source and original record. Its row matrix
and Gram matrix have rank equal to the distinct child-root count.
`BoundedCriticalSampleFiberRecordMoments` constructs native sparse product
moments while preserving both the sample descriptor and original record.
It proves the exact sum over the child roots on every raw query, including
concatenated records and invalid descriptors.
`BoundedCriticalSampleFiberRecordGram` derives native integer Gram entries
from these moments, with a degree bound on their magnitude.
`BoundedCriticalSampleFiberPrefixRank` masks unused Gram rows and computes
prefix ranks with native characteristic-coefficient scans. The candidate
dimension and all coefficient budgets have native binary controls.
`BoundedCriticalSampleFiberRankChoice` selects the unique rank-increasing
row for each requested rank by native bounded search. Out-of-range ranks
have no witness and return the total reader's default index zero.
`BoundedCriticalSampleFiberRankBasis` proves that these increasing selected
rows form a basis on the actual child roots and separate distinct roots.
Its native reader returns one short selected record, recomputing the row
search without storing a basis table.
`BoundedCriticalSampleFiberBasisGram` gives native selected Gram entries;
`BoundedCriticalSampleFiberBasisMoments` gives native selected triple moments.
`BoundedCriticalSampleFiberFeatureMoments` adds native derivative-sign-weighted
moments with binary orders clamped to the supplied degree. All keep the same
actual sample descriptor and original query record, including on invalid raw
queries.
`BoundedCriticalSampleFiberRootHash` constructs bounded separating labels
from selected record signs. `BoundedCriticalSampleFiberBasisPencil` identifies
distinct values with distinct roots of the weighted Gram determinant.
`BoundedCriticalSampleFiberWeightedMoments` supplies native weighted entries;
the `PencilEntries`, `PencilCoefficient`, `PencilBounds`, and `PencilSource`
modules derive native determinant access and uniform bounds on all raw count
and modulus words. Their correctness packet uses the actual child-root count.
`BoundedCriticalSampleFiberPencilRootCount` tests separation natively, and
`BoundedCriticalSampleFiberHashChoice` computes that count and selects bounded
separating parameters without a supplied hash or rank oracle.
The `PencilCuts`, `HashRoots`, `HashCuts`, and `HashEnumeration` modules
identify
the exact integer hash values and enumerate every distinct child root exactly
once in hash order, retaining its original actual-sample base word.
`BoundedCriticalSampleFiberSignatureProbe` proves recovery from two determinant
coefficients, with a nonzero denominator at every valid root. The
`ProbeEntries`,
`ProbeBounds`, `ProbeCoefficient`, and `ProbeSource` modules compute those
coefficients natively from the constructed moments.
`BoundedCriticalSampleFiberSignatureRead` streams any binary-indexed derivative
sign at a hash-order child ordinal. Orders beyond the degree return zero.
Its native PSPACE sign languages also validate the child ordinal, rejecting
invalid actual-sample descriptors and out-of-range ordinals even for sign zero.
These signatures are complete and distinguish all the child roots.
`BoundedCriticalSampleFiberRootOrder`, `RootRank`, and `OrderedRoot` convert
the hash labels to real-order ordinals with native streamed comparisons and
bounded searches. The resulting roots equal the original mathematical ordered
roots, including multiplicities counted only once.
`BoundedCriticalSampleFiberTestMoments` multiplies an arbitrary bivariate
test with the sparse-record product before specialization at the actual
sample. Its native weighted moments use the same parent descriptor and
original query record. `TestProbe`, `TestProbeSource`, and `TestSign` recover
general test signs at ordered child roots, with native PSPACE sign languages
rejecting invalid bases and ordinals even for sign zero.
`BoundedCriticalSampleFiberRootReindex` proves that attaching metadata
preserves the ordered child coordinate. `TestDerivatives` uses this to read
arbitrary binary-indexed test derivatives at that same root.
`BoundedCriticalSampleFiberLocalSign` computes one-sided signs by scanning
for the first nonzero derivative and proves their neighborhood semantics.
`RootCells` and `CellQueries` identify these signs throughout cells between
consecutive roots when the specialized test is zero or divides the head.
`BoundedCriticalSampleFiberLineTest` composes the general test reader with
the actual constructed coordinate-line families. It reads encoded term
signs at ordered zeros of an encoded head term, with no extra coefficient
oracle. Correctness uses the actual sample tuple updated at the free
coordinate; guarded sign languages also validate that coordinate.
`BoundedCriticalSampleSliceIndexed` attaches factor indices without changing
the actual sample. Its native specialized nonzero test drives
`BoundedCriticalSampleSliceRootProductSource`, replacing identically zero
factors by one before the product. `RootProduct` constructs a nonzero
polynomial at every valid sample, with roots exactly the union of the
specialized factors' roots and native product coefficients and root counts.
`RootProductQueries`, `RootProductPointSign`, and `RootProductCellLanguage`
compute indexed point and one-sided signs while preserving the original
descriptor and query record. Every nonzero factor divides the constructed
product, so interval-sign correctness needs no supplied divisibility oracle.
`CriticalSampleSliceCellCover` constructs the finite accessible cover of
every sign-defined subset of the actual fiber, including point cells, gaps,
both exterior rays, and the rootless case. `CellLabels` and `CellAdjacency`
provide native label validation and exact frontier incidence with polynomial
label width. `CellSignGeometry`, `CellSigns`, and `CellSignLanguage` recover
each factor's sign on the entire cell, including zero factors.
`CriticalSampleSliceBooleanAtoms` and `BooleanCells` evaluate the original
Boolean sign circuit at the source-and-record context while retaining the
actual sample descriptor. `BooleanPSPACE` constructs the restricted cell
graph and proves native PSPACE connectivity of its actual real solution set.
`BooleanReachability` proves that guarded cell-label reachability is exactly
path connection in that solution set. Invalid base descriptors and endpoint
widths are rejected.
`FormulaCriticalSampleRationalSlice` identifies the Boolean-selected cells
with the original formula in rational coordinates at the actual sample's
parameter. Native guards exclude every denominator pole, including when
clearing denominators makes an atom vanish identically. Its whole-set
connectivity and cell-label path languages are in native PSPACE.
`FormulaCriticalSampleLine` constructs both coordinate families from the
original readers. Their denominators are nonzero on the entire line, so the
solution set is exactly the formula evaluated on the updated actual sample
tuple. Its native connectivity and path deciders also validate the free
coordinate. `Geometry.CoordinateLine` proves that updating one coordinate
embeds the real line, preserving preconnectedness and paths in any restricted
set. `FormulaCriticalSampleLineGeometry` transfers the native query packets
to the formula's intersection with this line in the actual tuple space.
`OrderedRealCellLocation` identifies cell codes from the number of roots
strictly below an endpoint and a root-equality test, including exterior rays
and rootless fibers. `CriticalSampleSlicePointLocation` computes both counts
natively from an implicit comparison polynomial and the existing root product.
`BoundedCriticalSampleTermCut` constructs such a comparison polynomial for
any encoded arithmetic endpoint term evaluated at the actual sample. A fresh
variable beyond the term's arity gives exactly the signs of `t - endpoint`,
with native readers derived from the original sample and term readers.
`CriticalSampleSlicePointReachability` constructs both endpoint labels and
proves native point path decisions in the Boolean solution set, rejecting
endpoints outside that set even when both endpoint values coincide.
`FormulaCriticalSampleLinePoint` composes these routines with the original
formula line. Its native PSPACE endpoint language needs only the original
sample readers, an FP formula reader, an FP reader for each endpoint term,
and the binary free-coordinate control. Its correctness packet is exact
path connection in the formula's intersection with that coordinate line in
the actual sample's tuple space. No endpoint labels are supplied.
`BoundedCriticalSampleBlockCoefficient` gives total native coefficient queries
by arbitrary binary exponent words, repacking exactly the declared variable
blocks. `ParameterSpatialSpecialization` proves that specialization of variable
zero commutes with every spatial derivative and critical equation.
`BoundedCriticalSampleBlockCriticalSource` constructs the actual block critical
rows for a fixed-width candidate direction. Their degree and coefficient-mass
allowances are derived from the original term, block controls, and direction
width; no stability of the specialized degree is assumed.
`BoundedCriticalSampleBlockCritical` supplies their native modular coefficient
reader from the original sample and term readers. Pivot and row indices stay
binary and are clamped only for bounded internal queries. Invalid pivots and
rows return zero, including empty spatial blocks. Modulus and row words are
normalized before child calls. `BlockCriticalGeometry` identifies specialization
with the actual lower-dimensional critical equations and identifies the
specialized source's zero set with the original term on the updated actual
sample block. Selecting directions yielding finite regular child samples,
constructing their descriptors, and assembling the recursive cover remain open.
`BoundedCriticalParameterSeparable` exposes the separability already guaranteed
by the balanced primitive-parameter constructor. Its derivative is nonzero at
every root, including extraneous roots and actual selected parent parameters.
`RetainedParameterPolynomial` supplies the embedded parameter row's coefficient
mask, mass bound, and exact partial derivatives. `RetainedParameterSystem`
proves that adjoining this row multiplies the spatial Jacobian determinant by
the parent derivative, with the corresponding analytic regularity equivalence.
`BoundedCriticalSampleJointSource` combines the retained parent equation and
constructed spatial critical rows into one square integer system. Its common
degree, mass, exponent-width, and root-label allowances have native controls.
`CoefficientWidthBinarySpace` extends the existing guarded exponent conversion
to binary degree bounds; no exact-degree FP oracle is introduced.
`BoundedCriticalSampleParameterRow`, `JointCritical`, and `JointCoefficient`
construct native modular access to every row in the common layout. Oversized
critical exponents are rejected before narrowing; spatial monomials are masked
from the parent row. Parent-row queries remain defined for empty blocks.
`JointGeometry` identifies the actual parent fibers and reduces joint regularity
to spatial regularity. `RegularAffineSubsetCount` applies the existing
individual
coordinate eliminants to the regular subset, without requiring every root to be
regular or the full root set to be finite. The regular joint candidates
therefore
form a finite family with the derived label bound, even when other parent fibers
have singular or positive-dimensional root sets. Every regular critical point
over an actual parent sample belongs to this family. Completeness for intended
children still needs good directions. These candidates also include extraneous
parent roots; native parent filtering, good-direction selection, and child
descriptor construction remain open.
Recursive sample-base construction and the complete
higher-dimensional cover remain open.

`BoundedCriticalSampleBlockEvaluation` extends exact block-coordinate evaluation
to arbitrary source records, including records carrying query metadata.
`BoundedCriticalSampleChildTerm` constructs native coefficient readers and
binary degree and mass bounds for original terms pulled back to child
parameters.
`BoundedCriticalSampleChildTermSign` then validates both descriptors and their
actual-parent relation before deciding the original term's sign on the tuple
with the child inserted in its free block. Both denominator clearings preserve
signs. The defining source vanishes on every selected child; coordinates outside
the block retain their original values, including the zero extension.
`ScaledCriticalSystem` proves that nonzero constant scaling preserves the
whole spatial critical zero set, scales its Jacobian determinant by the
appropriate power, and preserves both critical and hypersurface regularity.
`BoundedCriticalSampleBlockScaling` identifies the actual cleared slice with
a positive constant times the original frozen-coordinate term polynomial.
`CriticalSampleOriginalSlice` transports the native child-pair reduction to
that original term's zero set. These identities do not assume that the
critical roots are finite or regular; in particular, singular roots outside
the constructed regular-child enumeration are retained by the equivalence.
A direction validator must exclude every singular critical root; counting
only roots of the regular-candidate parameterization cannot establish this.
The scaling bridge permits such a test on the original frozen-coordinate term.
`ComplexCircuitBlock` now compiles the original source with free coordinates
first and frozen parent inputs after them. The operation count is unchanged;
all addresses and the gate writer have native time bounds, including binary
offsets. `FreeCoordinateSpecialization` commutes with free partial derivatives.
`ComplexCriticalKernelPorts` gives exact constrained kernel queries with
independent logical witnesses. `ComplexCriticalKernelSpecialization` proves
that the union of normalized kernel charts at real inputs is exactly the
singular critical locus of the frozen slice, with no finiteness assumption.
`ComplexBlockKernel` constructs the native PSPACE validator for original-term
blocks and scans every chart. `ComplexBlockKernelGeometry` identifies its
specialized polynomial with the original frozen-coordinate term polynomial
used by child-sample geometry. `ComplexFrozenParentConstraint` now constructs
real parent-circuit guards in a later witness region, with links to the frozen
inputs and zero extension beyond the parent tuple.
`BoundedCriticalSampleBlockConstraint`
serializes the selected actual-parent circuit in native space and proves both
soundness and completeness: any satisfying assignment has an actual parent,
and any actual parent and arbitrary free tuple extend to witnesses.
`BoundedCriticalSampleBlockRegularity` composes this generated predicate with
the native kernel validator. Its acceptance is exactly regularity of every
critical root over every actual parent of the original term. Only referenced
term variables need frozen-input links; no coordinate table, parent labels,
or finite-critical-set premise is supplied.
`ProjectiveDirectionFamily` extracts nonzero maximal-minor certificates with
bounded parameter degree and avoids all certificates of a finite family on
one integer grid. `FermatCommonCriticalDirection` applies this to a family of
pure-power-leading hypersurfaces regular over coefficient-field extensions.
The grid allowance is the family size times the single-source allowance.
Its encoding counterpart constructs one record for all actual parents, using
the existing sample-count bound; the family contributes only its label width
to each direction field. Native record readers and length bounds are proved.
`FermatCriticalRegularity` specializes the algebraic certificate equations to
the exact finite critical rows and identifies their Jacobian with the analytic
derivative determinant. `BoundedCriticalSampleBlockData` transports actual
parent samples across query contexts while retaining their coordinate values.
`BoundedCriticalSampleDirectionChoice` now constructs a native bounded record
search using the actual-parent validator. The common-direction bound proves
success from the pure-power shape and extension-regularity premises, without
a supplied successful record. Its selected record has native direction readers.
`BoundedCriticalSampleDirectionPacket` prepends the normalized pivot field and
generates the explicit packet in native space; all child-source readers remain
polynomial time on that packet. `CriticalSampleSelectedDirection` transfers
acceptance to regularity of the original-slice child critical system.
Applying the source premises to the recursive sources and constructing the
recursive cover remain open.
`ComplexSharedKernel` now validates the shared circuit itself, with native
program and gate bounds. `BoundedFullBlockKernel` instantiates it with the
actual constructed regular-source program and proves the finite frozen-block
identity; no expression expansion of its binary powers is used.
`CoordinateBlockSpecialization` proves that every contained block preserves
the pure-power leading degree. The frozen pure powers add only a constant
to the specialized lower part, whose degree cannot increase. These give the
pure-power shape and lower-degree premise for blocks of the constructed full
source. `BoundedFullBlockRegularity` generates the actual-parent constraints
and proves acceptance equivalent to regularity of every critical root over
every actual parent. The original condition is replaced by those constraints.
`BoundedFullBlockData` transports the actual parent family and snapshots
the source readers across candidate-record metadata.
`BoundedFullBlockDirectionChoice`
uses the native shared-source validator in a bounded record search. Its width
comes from the constructed degree and actual parent count allowance. The block
shape and lower-degree bounds are derived, so only coefficient-field slice
regularity remains a geometric premise for contained blocks. The unfrozen
initial source derives this regularity from the construction and needs no
supplied shape, degree, leading coefficient, or regularity certificate.
Native record readers and selected kernel-query serializers preserve the same
source, parent family, and direction. The shared-source child descriptor
pipeline below supplies the native interface.
`BoundedCriticalSampleBlockCodes` now supplies Kronecker coordinate codes with
an independent native width. `BoundedFullSampleBlock` instantiates the existing
implicit fixed-width rational-substitution engine with `BoundedFullCoefficient`
for the exact constructed source. Source ranks remain binary, and fixed even
denominator powers use source-derived controls.
`BoundedFullSampleBlockPolynomial`
recovers collected multivariate coefficients and derives degree, support,
coefficient-mass, and native binary budget bounds.
`BoundedFullSampleBlockScaling`
identifies specialization at every actual parent with a positive constant
times the original finite coordinate block. This block agrees with the
shared-source kernel validator. Zero sets, hypersurface regularity, and the
entire spatial critical system and its regularity are preserved, including
singular roots. The unfrozen whole-source specialization has scale one.
`FixedWidthCriticalDirectionSpace` and `FixedWidthQuerySpace` charge native
direction selection in polynomial space. `BoundedFullSampleBlockCoefficient`
repackages arbitrary binary exponent words, and the critical source/reader
modules stream spatial critical equations with derived degree and mass bounds.
`BoundedFullSampleJointSource` retains the separable parent equation and gives
common degree, mass, exponent-width, and root-label allowances. Its native
coefficient readers guard width conversion and preserve the exact source
context, including empty blocks and modulus one. At actual parents,
`BoundedFullSampleJointGeometry` identifies all joint roots and their
regularity with the original block critical system. Regular candidates have
the derived finite label bound even if other parent fibers are singular or
positive dimensional. `BoundedFullSampleJointCoordinate` constructs nonzero
coordinate annihilators with native degree and coefficient bounds. Width
conversion, homogenized rows, implicit Macaulay entries, subtractive
characteristic determinants, and trailing-coefficient scans retain the
shared-source coefficient and space-computed direction costs. The new child
source feeds native exact-degree preparation and the existing balanced
primitive tree. Its separable parameter and rational coordinates have native
coefficient readers and derived degree/mass bounds. Filtered parameter roots
are in bijection with the regular joint candidates. Every regular critical
point over an actual parent has exactly one child parameter recovering its
retained parent coordinate and complete spatial tuple.
`BoundedFullSampleSelectedDirection` now connects the actual native selector
to these child inputs. A leading unused pivot field preserves every selected
free-direction entry; source and parent contexts are unchanged. Its space
certificate charges the direction search. Accepted records make the original
block critical system regular, so every actual-parent critical point has a
unique child parameter. Contained blocks derive selection success from slice
regularity, while the initial whole source supplies it unconditionally.
`BoundedFullSampleChildReaders` supplies native rational coordinate access.
The equation filters clear the exact joint rows with even powers; the
Jacobian source, entry, determinant, and regularity-filter modules give
native coefficients, bounds, and exact analytic regularity semantics.
Equation counts minus singular counts compute exactly the regular parameter
and joint-candidate counts, with native PSPACE existence decisions and no
all-roots-regular premise. Signed queries subtract singular contributions
over the same regular root set. Parent derivative-sign probes preserve the
retained parent coordinate, and their full sign signatures identify the
specified actual parent root. Selected-sign pattern counts and signed moments
are native.
Native reindexed queries and child-parameter derivative signs supply sparse
records spanning all functions on the regular roots. Prefix-rank scans select
a basis; native Gram pencils and bounded hash search select an injective
integer hash. Determinant cuts enumerate its values. Canonical signed words
have native PSPACE validity and a derived unary length allowance, name unique
regular joint candidates, and cover exactly that candidate family.
`BoundedFullSampleChildDescriptorGeometry` connects these words to the
original full-source blocks: every regular critical point over an actual
parent has exactly one valid bounded descriptor. The selected-direction
adapter supplies regularity, and the initial whole source supplies successful
selection without a separate witness.
Native polynomial-test and binary-indexed sign probes now read signs at these
descriptors, with validity guards rejecting malformed words and ordinals.
`BoundedFullSampleChildParentSelection` validates both descriptors and compares
all parent derivative signs with a binary-counted scan. It selects exactly
the retained coordinate of the specified actual parent. The resulting
`BoundedFullSampleChildActualSamples` family is finite and in bijection with
the original block's regular spatial critical points over that parent.
Accepted words name unique samples and have the native length allowance;
the native enumeration contains every sample in the fiber. Accepted selected
directions cover every critical point without a pointwise regularity witness,
including on the initial whole source.
`CoordinateBlockCompactness` proves compactness of contained coordinate-block
preimages by projection from the ambient compact preimage. No bounds on frozen
values or regularity assumption are required. `BoundedFullSampleBlockGeometry`
therefore derives properness and compactness of every real level of the
constructed full-source blocks, including singular levels and empty blocks.
Containment is essential: an out-of-range free variable can leave a constant
zero polynomial with a noncompact level.
`ProjectionCriticalSourceRegularity` derives hypersurface regularity from
regularity of every spatial critical root. A singular source point would be a
critical root with a zero base row in its derivative. The native selected
critical-system certificate thus supplies this sampling premise as well.
`FullSampleChildCoverage` constructs a path from every slice point to a sample
with an accepted bounded actual-parent descriptor. Its component map is
surjective, giving finite components bounded by the actual selected fiber and
then by the native regular-candidate count. Whole-slice preconnectedness is
equivalent to paths between all actual samples, including the empty slice.
`FullSampleChildPairs` implements these pair scans with native enumeration and
parent selection. Its PSPACE bound includes both scans and a supplied PSPACE
pair-language decider. Correctness transfers a pair-language path predicate to
whole-slice connectivity. Selected-direction wrappers remove separate critical
regularity premises; the initial whole source also supplies selection success
and containment. This is a conditional transfer: the recursive path procedure
and component-preserving cover remain to be constructed.
The original `BoundedFullSampleBlock.Inputs` still takes
`BoundedFullWriter.Readers`. `RationalCoordinateFamily` now provides a native
parent-coordinate interface independent of that source syntax. Its binary
degree and mass controls and coefficient evaluators are closed under
reindexing, fixed-exponent composition, guarded choice, and zero extension.
`RationalParentUpdate` retains the complete ambient point through a child
parameter: successor coordinates replace the sampled block, while all other
coordinates compose through the retained parent coordinate. Its native space
certificate includes both families and the composition routines.
`FullSampleParentCoordinates` instantiates the interface for original and
shared-source child samples. At every actual child parameter it proves all
denominators nonzero and recovers exactly the original ambient assignment,
including the coordinates outside the child block and zero extension.
`RationalParentBlockCodes` and `RationalParentFullBlock` stream full-source
blocks over these generalized parents. Multivariate coefficient, degree,
support, and mass bounds are derived, and the native coefficient evaluator
includes every parent computation. `RationalParentFullBlockScaling` proves
positive constant scaling, exact zero sets, hypersurface and critical-system
regularity equivalences, and properness of contained free blocks.
`FullSampleNextBlock` constructs this next-stage input at actual derived
children. Its specialization is the exact original source with the child's
ambient coordinates frozen outside the next free block, up to a derived
positive constant; all contained real levels are compact. No separately
supplied coordinate reader, denominator witness, or scaling certificate is
needed.
`SeparablePolynomialFamily` now packages native parent equations and binary
bounds independently of the original writer. Rational separability gives
simple roots in every characteristic-zero field. `SampleParentParameters`
instantiates this interface for both original and derived parents.
The `RationalParentFullBlockCritical` and `RationalParentJoint` modules give
native critical and complete joint coefficients, guarded width conversion,
homogenized rows, Macaulay entries, determinant coefficients, and trailing
coefficient scans. The retained parent row works even for empty spatial
blocks and keeps the complete source context. Exact root and analytic
regularity equivalences hold at every defined parent parameter root.
Regular candidates have finite native label bounds without requiring other
parent fibers to be regular or zero dimensional. Each coordinate has a
nonzero integer annihilator with native coefficients and derived bounds.
`RationalParentChildSource` performs native exact-degree preparation and feeds
these equations to the balanced primitive tree. `RationalParentChildCoordinates`
supplies native separable parameters and rational coordinate readers, with
binary degree and mass controls. `RationalParentChildParameters` identifies
regular parameters bijectively with regular joint candidates. Every regular
original-block critical point at a defined parent root has a unique parameter
recovering the retained parent and the complete spatial tuple.
`RationalParentChildParents` turns these coordinates back into an ambient
parent family and another native joint input. Parent denominator nonvanishing
passes through the retained parameter; regular children retain a root of the
previous parent equation. `FullSampleNextStage` instantiates the generalized
pipeline at actual earlier child samples and proves unique next-stage
parameters, exact nested ambient assignments, and denominator nonvanishing.
Native equation and Jacobian filters now count exactly the regular candidates
over generalized rational parents. Sparse records, Gram bases, injective
hashes, and ordered enumeration construct canonical bounded descriptors.
Native polynomial and indexed sign readers operate at these descriptors.
`SeparablePolynomialThom` supplies native iterated-derivative coefficients for
arbitrary separable parent equations. `NamedRationalParents` records the actual
subset of parent roots, injective bounded names, and native validity and
derivative readers. `NamedParentChildSelection` validates both names and uses
a binary derivative-sign scan to identify precisely the retained actual
parent. `NamedParentChildNext` constructs another such source, with exact
ambient coordinates and nonzero denominators. Every regular original-block
critical point over an actual parent has a unique accepted child parameter.
Newest-first pair encoding adds the new descriptor length to the old ancestry
length. `NamedRationalSeed` supplies the concrete zero root and empty name.
The full primitive parameter polynomial can still have extraneous roots;
the ancestry validator excludes them from the actual parent family. These
are fixed-stage native closure certificates. In particular, composing them
does not establish uniform degree, mass, space, or name bounds for an
input-dependent number of stages. Direction selection and these uniform
recursive bounds remain open.
`TriangularPolynomialSystem` and `TriangularPolynomialTower` provide an
algebraic alternative to repeatedly eliminating the old parameters. Appending
a stage retains all earlier variables and takes the maximum row degree and
coefficient-mass bounds. At arbitrary depth k and stage width n, there are
exactly k*n variables; k ≤ n gives at most n² variables. The combined Jacobian
factors into the old determinant and the new spatial determinant, including
empty blocks. `TriangularPolynomialRegularity` proves that freezing ancestral
coordinates commutes with differentiation, and identifies analytic regularity
with the stage-by-stage criterion. These results apply at arbitrary depth.
`PolynomialSystemReindex` preserves the Jacobian under explicit simultaneous
equation and variable reindexing. `TriangularPolynomialIndexing` gives a
computable stage-order equivalence with Fin(k*n), preserving root, regularity,
degree, and mass statements. `FlatCriticalStage` uses the original polynomial
for critical rows in the free set and linear copy constraints outside it.
`FlatCriticalTower` copies from the preceding complete ambient tuple, starting
from zero, and proves exact stage-by-stage root semantics and uniform bounds.
`FlatFullSourceTower` instantiates this construction with the original native
full-source readers and input-dependent depth. Degree and mass budgets have
native controls. `FlatFullSourcePlan` validates every block's containment,
nonemptiness, and pivot membership in native polynomial time; roots of valid
nonempty plans satisfy the original source equation at the newest stage.
`FlatFullSourceCoordinate` applies one elimination to the
whole tower: every regular root annihilates concrete nonzero coordinate
polynomials with natively computed degree and coefficient-bit allowances.
`BlockRenameCoefficient` and `FixedWidthBlockRenameSpace` give exact native
coefficient access to a source embedded in a selected variable block. Outside
exponents are rejected; redundant bits and raw moduli are retained correctly.
The full-source block and critical-coefficient adapters use the original
source reader, with two derivative calls for each critical difference.
`FixedWidthLinearCoefficientSpace` provides native coordinate and copy-row
coefficients. `TriangularPolynomialRows` and `FlatCriticalIndexedRows` identify
every indexed row at arbitrary depth, retaining ancestral indices.
`FlatFullSourceContext` transports all source and stage metadata together.
`FlatFullSourceRowCoefficient` assembles the complete reader, charging the
space-computed direction record before dispatching to critical or copy rows.
`FlatFullSourceRowCoefficientCorrect` proves exact collected-coefficient
semantics for the existing indexed system. `FlatFullSourceCoefficient` derives
the exponent width from the original degree allowance. Invalid rows, including
every row at depth zero, return zero; modulus one is supported.
`PositivePolynomialSystem` appends a zero dummy coordinate, preserves every
original index, gives unique root extension, and preserves the Jacobian
determinant. `FlatFullSourcePositive` instantiates it with native positive
dimension and the same degree and mass budgets. Analytic regularity is
preserved, including at depth zero.
`FlatFullSourcePositiveCoefficient` embeds the old rows and supplies the dummy
row with exact native coefficients. Nonzero dummy exponents are rejected in
old rows; raw moduli, invalid row indices, and the valid empty-seed row are
handled explicitly. `FlatFullSourcePositiveRows` supplies native homogenized
coordinate rows, retaining the source and coefficient parameter.
`FlatFullSourcePositiveCoordinate` derives a positive width containing every
row degree, as well as native matrix-size and coefficient-bit budgets. Its
nonzero coordinate polynomials annihilate every regular padded root and every
regular original root at the corresponding old coordinate.
`FlatFullSourcePositiveMacaulay` reads the implicit integer polynomial matrix.
`FlatFullSourcePositiveCoordinateCoefficient` feeds these entries to the native
subtractive-characteristic reader and lowest-coefficient scan. It computes
the actual nonzero coordinate eliminant, uniformly in the input-dependent
tower depth. The entire source and direction costs remain charged.
`FlatFullSourcePositiveContext` preserves these exact equations when the
complete original source context is transformed. `FlatFullSourceSampleSource`
constructs a finite coordinate source, computes exact degrees natively, and
retains every prepared coordinate equation at regular flat roots.
`FlatFullSourceSampleCoordinates` supplies a separable common parameter and
native rational coordinate readers. Parameter degree, coordinate degree, and
coefficient-mass allowances have binary native controls uniformly in the
input-dependent depth. Every coordinate-root tuple has a unique parameter
with nonvanishing coordinate denominators. Parameter roots can still encode
extraneous tuples. `FlatFullSourceSampleParameters` selects the flat equations
and analytic regularity, proves a bijection with regular original tower roots,
and gives a native polynomial label-width bound without assuming every root
is regular. `FlatFullSourceSampleReaders` retains the complete source context
through rational substitution. `FlatFullSourceSampleFilters` constructs native
univariate equation tests with exact zeros and real signs on parameter roots.
The `FlatFullSourceSampleJacobian` modules differentiate all ancestral and
dummy coordinates and read the actual determinant.
`FlatFullSourceSampleRegularFilter` gives a native polynomial whose
nonvanishing is exactly analytic regularity on parameter roots. All test
degree and mass allowances are native.
`FlatFullSourceSampleEquationCount`, `SingularCount`, and `RegularCount`
instantiate native sign-pattern counting and subtract the singular roots.
The result is exactly the number of regular original flat roots, with a native
existence decider. `Queries` and `ReindexedQueries` supply signed moments on
this actual filtered set while preserving the complete source context.
`Thom`, `Records`, and `RecordSpan` give short derivative-sign records spanning
the root-function space, with Gram rank equal to the regular-root count.
The prefix-rank and basis modules select records natively. The root-hash,
weighted-moment, and pencil modules construct a separating integer hash,
checking the determinant root count rather than assuming a selected basis or
a hash witness. `HashChoice`, `HashRoots`, `HashCuts`, `HashEnumeration`, and
`Descriptors` give canonical bounded words, native validity, and ordered
enumeration. Every descriptor names one accepted parameter and one regular
flat root. `TestSign` and `IndexedSign` read general native polynomial tests at
these labels, rejecting invalid labels even for sign zero. `DerivativeSigns`
streams arbitrary indexed derivatives of the common parameter. All these
modules use the `FlatFullSourceSample` prefix and the uniform flat source.
`FlatFullSourceSampleVertices` converts hash-order ordinals into fixed-width
vertex words with a native polynomial width and a PSPACE validity language.
It proves a bijection with regular roots of the original unpadded tower,
including all ancestral coordinates. Polynomial sign readers normalize the
ordinal word while retaining the source. Component-preserving graph edges
and coverage of general recursive fibers remain to be constructed.
Slice regularity is still required separately: even a tangent slice of the
regular circle has a singular root. General recursive endpoint slices and
their component-preserving treatment remain open. The original copy rows
freeze raw coordinates, so their native backend alone does not implement
slicing along a newly chosen critical direction.

`AffineHeightPolynomial` now constructs arbitrary linear heights and midpoint
levels from two ancestral ambient blocks. A doubled current height equated
to that sum lies strictly between distinct endpoint heights; it does not
constrain each ambient coordinate to its midpoint. `FlatAffineCriticalStage`
uses n ambient coordinates and n+1 multipliers. Its rows are the original
source equation, its gradient expressed in the new and active old normals,
active affine-height levels, and zero unused multipliers. All row degrees
are bounded by max(source degree,1), with explicit coefficient-mass bounds.
`FlatAffineCriticalRegularity` proves that a regular stage root has nonzero
new-height multiplier: otherwise the source row is dependent on the active
height rows. The new height consequently annihilates every slice tangent.
`FlatAffineCriticalGeometry` identifies its formal Jacobian with the analytic
frozen-stage derivative.

`FlatAffineCriticalExtremum` proves the converse for constrained local maxima.
A surjective slice derivative supplies normalized Lagrange multipliers;
independence of the new normal from the old normals makes the source
coefficient nonzero, yielding an actual stage root with nonzero new-height
multiplier. `ComponentFiberMaximum` supplies a local maximum in each component
of a compact regular fiber, joined to every point of that component.
`FlatAffineComponentSampling` applies it to the actual affine slice. This
requires regularity of the slice constraint map; it does not assert that
all critical stage roots are nonsingular.

`FlatAffineCriticalTower` assembles these rows with fixed stage width 2*n+1.
Levels refer directly to earlier ambient blocks, including sums of two
heights for midpoint levels, sharing all ancestry. Indexed row degree and
mass bounds remain uniform at every depth, and depth at most n uses at most
n*(2*n+1) variables. `FlatAffineCriticalIndexedRows` now identifies the exact
source, gradient, multiplier, and affine-level rows at their stage-order
indices, including references to ancestral ambient blocks.

`FlatAffineFullSourceTower` now gives this separate tower native input
controls. Directions and level records are charged space-bounded readers;
signed coefficients are differences of fixed-width blocks. Levels decode as
constants, earlier heights, or midpoints, with references clamped to existing
stages and a constant fallback for empty ancestry. Variable counts have unary
controls; degree and coefficient-mass exponents have binary controls uniformly
in the input-dependent depth. `FlatAffineFullSourceContext` preserves the
entire system when its original source context changes, including the nested
stage and level queries.

`FlatAffineIntegerSpace` computes signed scalar residues, including modulus
one and redundant words. `FixedWidthConstantSpace` supplies constant-row
coefficients, including empty and zero-width exponent layouts.
`FixedWidthHeightSpace` streams actual collected coefficients of weighted
linear forms, allowing coincident variable selections and charged
space-bounded variable selectors. `FlatAffineHeightCoefficient` instantiates
it with actual signed record entries. `FlatAffineFullSourceBlockCoefficient`
and `FlatAffineFullSourceDerivative` supply native embedded original-source
coefficients and partial derivatives with binary degree bounds.

`FlatAffineFullSourcePositive` appends one coordinate fixed at zero, retaining
all original indices, roots, and analytic regularity, including depth zero.
`FlatAffineFullSourceEmbedded` reads original-source coefficients and partial
derivatives in this larger layout. `FlatAffineRowLayout` and `RowAccess`
supply total clamped coordinates and native metadata. The ancestral selector
charges the actual space-bounded level-record computation. `RowPolynomials`
constructs the source, gradient, active-height, unused-multiplier, and dummy
components; `RowIdentity` proves that their dispatch equals every actual row
of the completed indexed system. The linear, source, and level reader modules
then feed `FlatAffineFullSourcePositiveCoefficient`: every selected row now
has a native coefficient evaluator with arbitrary unary caller exponent
width, a separately derived safe source-derivative width, and modulus-one
semantics. No ancestral coefficient oracle is supplied.

`FlatAffineFullSourcePositiveRows` supplies native integer and homogenized
rows, preserving the entire source context under query transforms.
`FlatAffineFullSourcePositiveCoordinate` constructs a nonzero annihilator
for each coordinate of the completed tower. Every regular original root
extends to a root of these equations, including all ancestral coordinates.
Degree and coefficient-bit bounds have native controls uniformly in depth.
`FlatAffineFullSourcePositiveMacaulay` reads the actual homogenized matrix;
`PositiveCoordinateCoefficient` computes the determinant and its lowest
nonzero coefficient natively. `PositiveContext` preserves these exact
coordinate equations when the original source context changes.

`SquareSampleInput` supplies a reusable positive square-system interface.
Its canonical row query carries the source, selected row, exponent-width word,
rank, and modulus predecessor. Width is the word length; context changes
preserve the other fields, including noncanonical words. `SquareSampleAccess`
derives arbitrary FP-context row and annihilator readers from these two native
programs. `FlatAffineSampleInput` constructs both programs from the actual
affine tower, requiring only its original source and direction/level access.
No additional coefficient-access premise is introduced by this adapter.

`SquareSampleSource` prepares exact degrees for the coordinate annihilators.
`SquareSampleCoordinates` constructs separable primitive parameters and
rational coordinates; every regular system root is recovered with all
coordinate denominators nonzero. `SquareSampleParameters` proves a bijection
between accepted parameters and the regular system roots. A binary parameter
degree bound gives a unary label width. The equation and Jacobian filters,
regular-root count, streamed signatures, sparse records, rank-selected bases,
hash labels, enumeration, and indexed sign routines now use this interface.
They do not assume that every system root is regular or that the entire
root set is finite.

`SquareSampleVertices` has native fixed-width validity and a bijection with
regular system roots. `SquareSamplePolynomialTest` clears rational-coordinate
denominators by even powers, giving native signs of implicit multivariate
polynomials at those same roots. Its native coefficient access and binary
budgets are charged. In particular, tests of actual system rows derive their
coefficient reader from `SquareSampleInput.Access` and have sign zero at every
valid sample.

`FlatAffineSampleVertices` removes the unique zero dummy coordinate. Its
vertex labels cover exactly the regular roots of the entire original affine
tower; both their native count and existence decision require only the
original source and direction/level access.

`SpatialPolynomialReindex` proves that simultaneous spatial row/variable
reindexing preserves the frozen Jacobian, while retaining every ancestor.
`TriangularPolynomialStageRegularity` gives exact root and Jacobian criteria
for all stages of an indexed tower. They preserve every earlier prefix,
including empty blocks and depth zero. An explicit appended-point map has
exact old/new block identities and root/regularity extension criteria.
`FlatAffineTowerRegularity` identifies these criteria with the actual affine
Lagrange stage matrices. `FlatAffineTowerGeometry` proves the corresponding
analytic derivative equivalences, prefix preservation, and criticality at
every stage of a regular full root.

`FlatAffineSliceRegularity` solves the full nonsingular spatial Jacobian with
prescribed constraint outputs. Its ambient coordinates prove surjectivity
of the source/old-height derivative. Consequently the number of active old
heights is strictly less than the ambient dimension. This implication does
not need a root hypothesis. In particular, fully activating every old-height
slot cannot produce a regular child sample.

`FlatAffineSamplePrefix` changes only the depth, retaining the original
source and all charged records. It projects regular sample roots to every
earlier prefix, with unchanged coordinates; repeated projections compose.
The projected root has a short sample word. A native program computing that
word directly from the full sample label is not yet supplied.
`FlatAffineSampleExtension` combines a regular parent and an actual regular
frozen child stage into a regular complete tower root. Projecting recovers
the parent, and the appended coordinates are exactly the child. When every
frozen critical child is regular, this extension injects the child roots into
the complete next-tower regular roots. Their number is bounded by the native
next-tower count, without another elimination over the parent's coordinates.
Its compact slice theorem produces a valid child label in the component of every
slice
point, retaining the given parent. Compactness, slice regularity, independent
new height, and regularity of every frozen critical child remain explicit
hypotheses.

`GenericAffineCriticalJacobian` proves generic affine critical regularity
without first changing ambient coordinates. Derivations of algebraically
independent objective coefficients produce Jacobian columns supported on the
gradient rows, scaled by the source multiplier. Slice row independence
forces that multiplier to be nonzero. Pairing a left-kernel vector with these
columns kills its gradient entries; slice row independence and the unused
multiplier equations then kill every remaining entry.
`FlatAffineGradientJacobian` identifies this matrix with the actual polynomial
stage, including source coefficient maps and arbitrary ancestral level
polynomials whose frozen values lie in the coefficient field.

`FlatAffineRegularSpecialization` encodes slice regularity with polynomial
right-inverse variables. Every regular-slice root extends to this guarded
system, and every guarded root has a surjective slice constraint matrix.
The generic Jacobian theorem applies over every extension of the parameter
fraction field. Existing ideal-based denominator clearing produces a nonzero
objective exceptional polynomial. Integer-grid avoidance specializes it to a
natural-number objective, with an allowance depending on that polynomial.
`AffineDirectionAvoidance` constructs a nonzero linear factor vanishing on
the old height span whenever fewer than n heights are active. Avoiding both
factors gives an integer objective outside that span, with all critical roots
on the fixed regular slice nonsingular. No complex smoothness of the whole
unsaturated slice is assumed: the polynomial guards retain exactly regular
slice points.

This proves qualitative integer genericity for fixed affine slices. It does
not bound the exceptional polynomial's degree in the original source data,
or supply polynomial input-size bounds for the chosen direction. Uniform
recursive direction/level choices, singular slices, effective prefix-label
projection, and component-preserving graph edges remain open.

The full effective recursion for arbitrary Boolean, singular, and noncompact
inputs, its component preservation, and its polynomial bounds remain open.
Neither requested full connectivity PSPACE theorem has been established.
