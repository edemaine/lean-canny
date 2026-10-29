# Prior work, proof route, and complexity infrastructure

## Current result and scope

[`CoercivePSPACE`](LeanCanny/ETR/CoercivePSPACE.lean) proves
`LeanCanny.ETR.etr_mem_PSPACE` and
`LeanCanny.ETR.existsReal_subset_PSPACE`: the project's encoded ETR language
belongs to Complexitylib's PSPACE, and every language polynomial-time reducible
to it does too. The final theorem composes actual native readers and preparation
programs; it has no supplied coefficient, metadata, finite-fiber, or geometric
parameter-selection hypothesis.

The completed result is Canny's ETR PSPACE upper bound. The proof uses a coercive
one-parameter construction to obtain effective bounded samples, followed by
symbolic primitive coordinates and eventual sign decisions. The report's
roadmap, connectivity, and motion-planning algorithms are further work. The
compact tube route developed earlier remains an unused alternative with the
quantitative gaps listed below.

## Prior real-algebraic formalizations

Investigation date: 2026-10-19. These findings describe the repositories and
searches inspected then; they are not claims that no other formalization exists.

* [TauCeti](https://github.com/TauCetiProject/TauCeti) includes real-algebraic
  quantifier elimination, CAD existence, Tarski–Seidenberg, and Sturm–Tarski/sign
  determination. See its
  [quantifier elimination](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/Semialgebraic/QuantifierElimination.lean)
  and [recursive sign determination](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/SignDetermination/Recursive.lean).
  The inspected sign-determination construction used noncomputable choices;
  those correctness results did not supply Canny's workspace bound.
* [Hex](https://github.com/leanprover/hex) develops exact real-algebraic
  computation, including root isolation, algebraic numbers, resultants, and
  real-closed-field tactics. Such arithmetic does not by itself give a PSPACE
  bound for ETR.
* Isabelle AFP has
  [Ben-Or–Kozen–Reif](https://www.isa-afp.org/entries/BenOr_Kozen_Reif.html)
  and [hybrid real quantifier elimination](https://www.isa-afp.org/entries/Quantifier_Elimination_Hybrid.html),
  relevant algorithmic correctness precedents in another prover.
* Coq has Cohen and Mahboubi's real-closed-field quantifier elimination and
  [MathComp CAD](https://github.com/math-comp/cad).

The local Sturm–Tarski and signed-principal-subresultant proofs adapt a selected
slice from TauCeti revision `034e577c895d28c058d92af4036f7ce0b03081cf`.
[`STURM_SOURCES.md`](STURM_SOURCES.md) records source files, attribution, and
changes. The adaptation specializes analytic arguments to the reals and uses
Mathlib's intermediate value theorem. The native computational layer reduces
root/sign queries to streamed determinant signs, with degree and coefficient
budgets and all original-source reader costs included.

## Gap in Canny's symmetric coordinate recovery

Canny's report, printed pages 6–7, equations (13)–(16), recovers coordinates by
shifting projection coefficients in opposite directions and taking a GCD.
The assertion that suitable coefficient choices always make this GCD linear
fails for a simple finite system. This is a gap in the proposed construction;
it does not refute the PSPACE upper bound or the existence statement of
Lemma 2.2.

[`SymmetricRecoveryDegeneracy`](LeanCanny/Algebra/SymmetricRecoveryDegeneracy.lean)
formalizes the example `x³ - x = 0, y = 0`. Its solutions are `(-1,0)`, `(0,0)`,
and `(1,0)`, and its homogenization has no nonzero solution at infinity. For
projection `L(x,y) = c₀x + c₁y`, the eliminant is
`q(X) = X(X-c₀)(X+c₀)`, with distinct roots whenever `c₀ ≠ 0`.
Changing `c₁` by either `+1` or `-1` leaves q unchanged. At the middle projected
root zero, the recovery GCD is therefore `gcd(q(X), q(-X))`. Since
`q(-X) = -q(X)`, this GCD has degree three, rather than one. The theorem
`symmetric_pair_not_linear` verifies the failure for every coefficient choice.

The obstruction is the midpoint relation: every linear projection preserves
`L(-1,0) + L(1,0) = 2L(0,0)`. The corresponding instance of condition (14)
is identically zero in the projection coefficients. Thus separating the three
projected roots, or choosing infinitesimal coefficients, does not remove these
spurious recovery roots as claimed on page 7.

[`AsymmetricProjection`](LeanCanny/Algebra/AsymmetricProjection.lean) and
[`AsymmetricCoordinateRecovery`](LeanCanny/Algebra/AsymmetricCoordinateRecovery.lean)
prove bounded asymmetric recovery for finite point sets. The completed ETR
proof uses the coercive sampling and certified primitive-coordinate construction
described below; it does not assume the failed symmetric-recovery claim.

## Encoded statement

[`ETR.Syntax`](LeanCanny/ETR/Syntax.lean) uses integer polynomial expressions
and Boolean combinations of equality and strict inequality, with real
semantics. [`ETR.Encoding`](LeanCanny/ETR/Encoding.lean) gives a canonical binary
codec; integer magnitudes are binary and variable indices unary. The language
rejects malformed strings. The grammar recognizer and all normalization and
compiler reductions have native polynomial-time certificates on every bitstring.

[`EquationCompilerFP`](LeanCanny/ETR/EquationCompilerFP.lean) compiles a formula
to one equisatisfiable integer polynomial equation, using witnesses, Boolean
selectors, and a final sum of squares. Malformed inputs map to an unsatisfiable
equation. Arity, degree, encoded length, and coefficient mass have explicit
input-size bounds. The completed route uses this uncompactified equation,
avoiding boundary zeros introduced by compactification.

[`ExistsReal`](LeanCanny/ETR/Complexity.lean) is defined as the downward closure
of this ETR language under Complexitylib polynomial-time many-one reductions.
ETR is complete for that class by definition. The class inclusion follows from
the ETR algorithm and proved PSPACE reduction closure. Relating the encoding
to other standard ETR presentations and proving the NP lower inclusion are
separate future results.

## Effective bounded critical samples

For a compiled polynomial q in n variables and D at least its total degree,
consider

`F_s = q² + s * Σ Xᵢ^(2D+2)`.

[`CoercivePolynomialSampling`](LeanCanny/Geometry/CoercivePolynomialSampling.lean)
constructs global minimizers for positive s and proves their gradient equations.
From an original root, it chooses a bounded subsequence of critical samples as
s tends to zero; its limit is a root. Conversely, bounded samples with squared
residual tending to zero have a root as a subsequential limit.

[`CoerciveCriticalFibers`](LeanCanny/Algebra/CoerciveCriticalFibers.lean) proves
finite gradient fibers for every nonzero s. Each gradient has leading term
`(2D+2)*s*Xᵢ^(2D+1)` and lower total-degree remainder. Division by these pure
powers leaves a finite spanning set with every exponent below `2D+1`.
Finiteness is derived from the actual equations, including constant gradient
targets; it is not a promise about a chosen fiber.

[`CoerciveCriticalHomogenization`](LeanCanny/Algebra/CoerciveCriticalHomogenization.lean)
constructs the homogeneous gradient rows and one coordinate row over ℤ[T][s].
For nonzero s there are no roots at infinity. Finiteness gives a real T
specialization with no complex projective root. A maximal Macaulay minor is
then nonzero and vanishes at every common projective root. Explicit row degree
and coefficient-mass budgets bound this minor. Removing its lowest s power
and passing to a limit gives an integer coordinate annihilant for a root.

[`CoerciveRootRadius`](LeanCanny/Geometry/CoerciveRootRadius.lean) combines these
annihilants with a Cauchy root bound to derive a root radius from n, D, and an
original mass exponent. [`CoerciveRadiusBits`](LeanCanny/Algebra/CoerciveRadiusBits.lean)
proves polynomial binary-size bounds for the radius and penalty exponents.
[`CoerciveSourceSampling.correct`](LeanCanny/ETR/CoerciveSourceSampling.lean)
therefore equates ETR with eventual bounded critical samples for the actual
compiled input, with the radius chosen internally.

## Native annihilants and preparation

The source-size existence proof can select a minor noncomputably. The coefficient
algorithm instead uses a fixed determinant. The full Macaulay matrix A has a
nonzero Gram determinant `det(AᵀA)` at a real specialization with no complex
projective root. Every common projective root annihilates it. The block matrix
`[[I,A],[-Aᵀ,0]]` has the same determinant and needs only original coefficient
entries and constants.

[`CoerciveBoxGramEliminant`](LeanCanny/Algebra/CoerciveBoxGramEliminant.lean)
uses fixed-width padded monomial and shift ranks, permitting binary matrix
dimensions without materializing a dense matrix.
[`CoerciveAnnihilatorResidue`](LeanCanny/ETR/CoerciveAnnihilatorResidue.lean)
and [`CoerciveNativeOriginalResidue`](LeanCanny/ETR/CoerciveNativeOriginalResidue.lean)
compose the actual source, derivative, homogenization, shifted-entry, and
determinant readers. Degree and mass budgets have FP binary writers. A pin leaf
retains the perturbation as an original root coordinate.

[`CoerciveIntegerPreparation`](LeanCanny/ETR/CoerciveIntegerPreparation.lean)
clears the original bivariates at an implicit dyadic reference value and
computes the actual degree, GCD-order, and balanced degree/direction tables in
native polynomial space. The exponent has a short binary code; residues of the
large powers are computed without writing their full integers.

[`SymbolicFormalSquarefreeSpace`](LeanCanny/Algebra/SymbolicFormalSquarefreeSpace.lean)
defines a total coefficient program for arbitrary supplied metadata. The
coefficient-form and Cramer quotient determinant stages charge every child
reader. Exact prepared metadata identifies its result with the genuine symbolic
squarefree polynomial. Thus malformed frames do not require false claims that
their supplied degrees or GCD orders are correct.

Padding requires particular care: dyadic clearing of symbolic X gives a scalar
multiple of X, whereas the integer tree's fallback leaf is literal X. The native
preparation uses an enlarged finite source containing all cleared leaves used by
the desired symbolic subtree. [`CoerciveTableCorrectness`](LeanCanny/ETR/CoerciveTableCorrectness.lean)
extracts that subtree and proves exact polynomial, degree, and direction
identities at every used node, including the original root.

## Uniform symbolic evaluation and coordinates

[`SymbolicFixedTableCoefficientSpace`](LeanCanny/Algebra/SymbolicFixedTableCoefficientSpace.lean)
instantiates the uniform recursive coefficient evaluator for the complete
fixed-table symbolic graph. It derives task-word, reply, metadata, rank, and
intermediate-degree bounds and retains alpha-degree guards when a request
moves to a smaller child radix. Squarefree leaves, resultant stages, matrix
operations, and zero branches all have native local programs.
[`CoerciveParameterCoefficient`](LeanCanny/ETR/CoerciveParameterCoefficient.lean)
composes that evaluator with actual preparation, yielding coefficients of the
actual source primitive parameter.

[`CoerciveCoordinatePairReaders`](LeanCanny/ETR/CoerciveCoordinatePairReaders.lean)
computes indexed numerator and denominator stages using the exact prepared
node orders and directions. Whole coordinate paths are evaluated by ordered
matrix products at input-dependent depth. Source-derived fixed clearing
allowances give rational coordinates with nonzero denominators at the relevant
parameter roots, and ordinary small positive specialization preserves both
encoding and decoding.

[`CoerciveQueryCoefficient`](LeanCanny/ETR/CoerciveQueryCoefficient.lean)
computes the actual gradient, residual, and penalty query coefficients.
[`CoerciveClearedQuerySpace`](LeanCanny/ETR/CoerciveClearedQuerySpace.lean)
composes these readers with the computed coordinates and even denominator
clearing. All original, stage, path, and substitution costs are retained;
there is no intermediate coordinate or query coefficient oracle.
[`CoerciveClearedQueryCoefficient`](LeanCanny/ETR/CoerciveClearedQueryCoefficient.lean)
provides the final coefficient interface used with the actual coordinate readers.

## Eventual signs and the final theorem

[`InfinitesimalRootPSPACE`](LeanCanny/Algebra/InfinitesimalRootPSPACE.lean)
decides eventual real-root/sign feasibility from native bivariate coefficient
readers and binary degree/mass controls. Its effective stability bound concerns
the complete symbolic parameter and sign queries, so no separately chosen
geometric alpha interval is required.

[`CoerciveInfinitesimalSemantics`](LeanCanny/ETR/CoerciveInfinitesimalSemantics.lean)
proves that four exact sign patterns characterize ETR. Their two inequality
positions allow negative or zero values; the gradient equations require zero.
The actual parameter and cleared-query readers discharge the reader interface
in [`CoerciveInfinitesimalReadout`](LeanCanny/ETR/CoerciveInfinitesimalReadout.lean).
[`CoercivePSPACE`](LeanCanny/ETR/CoercivePSPACE.lean) takes the finite union and
exports the unconditional ETR and ExistsReal PSPACE theorems.

## Complexity foundation and verification

The development uses Complexitylib's tidy multitape calculus throughout.
[`SpaceFunction`](LeanCanny/Computation/SpaceFunction.lean) is a proof-only
wrapper around `ComputableTidilyInPolySpace`;
[`SpaceDecider`](LeanCanny/Computation/SpaceDecider.lean) carries membership in
Complexitylib's machine-based PSPACE class. P, FP, and polynomial-time
many-one reductions also use this foundation directly.

Composition, pairing, branches, binary folds, modular scans, matrix powering,
Berkowitz determinants, and recursive stacks compose native space certificates.
A child may take arbitrary time in polynomial space; its execution clock is
not stored in its caller. Recursive correctness, decreasing ranks, and encoded
state-size bounds are still proved explicitly. Exponentially large matrices,
polynomials, and powers of two are accessed by short binary indices and modular
readers. They are not stored as expanded objects.

The earlier Complexitylib V1 adapters, custom-machine simulation, and suspended
scheduler were removed. No equivalence with Mathlib's `FinTM2` or another
library's PSPACE predicate is assumed. The historical machine comparison found
that `lean-trominoes` supplied TM2 workspace certificates and a generic Savitch
evaluator, while the older Complexitylib V1 used a distinct multitape model. A
space-preserving bridge between those predicates was not established here.
[`TidyBoundedFold`](LeanCanny/Computation/TidyBoundedFold.lean) supplies the
binary-counted fold evaluator used by the main development, accepting
polynomial-space children without a running-time bound.

The commands in [`README.md`](README.md) check the full build, allowed axioms,
grammar correctness, and native space/time foundations. The axiom audit allows
only `propext`, `Classical.choice`, and `Quot.sound`; conditional helper interfaces
do not replace the actual programs in the final theorem.

## Reusing upstream algorithm tools

The polynomial-time iteration adapters now use
`ComputableTidilyInPolyTime.iterate` directly. Output-size bounds compose with
native `PolyBounded` operations, avoiding a second fold construction and the
extraction and reconstruction of polynomial bounds.

The binary-counted space folds and recursive stack already use native
`ComputableTidilyInPolySpace.iterate`. Ordinary polynomial-time list folds do
not replace them: counts may be exponential and a child may require arbitrary
time in polynomial space. Their accumulator, rank, and task-word invariants
remain necessary.

`polytime` now normalizes project goals and local certificates to the native
predicate and delegates composition, named-certificate lookup, and search to
upstream `fun_prop` and `PolyTime`. `FPPred` certificates expose their Boolean
verdicts. Native `program_certificate` registrations cover the total raw packet
codec and named readers; typed `encPair` projections have a different wire format.
Small forwarding rules cover unary arithmetic and range operations; bounded
quantifiers and counting use upstream typed traversals. The former local Aesop rule set and custom routine-call
search are removed. [`CheckPolyTimeFoundation`](scripts/CheckPolyTimeFoundation.lean)
checks local and named calls, encoded unary outputs, bounded predicate scans,
malformed packets, and rejection of routines without certificates.

[`TidyBoundedProduct`](LeanCanny/Computation/TidyBoundedProduct.lean) shares the
binary range-product evaluator used by finite-annihilator and balanced degree
preparation. Callers supply factor readers and polynomial bounds on every
accumulator prefix. Generic controller lengths and execution identities live
in `ControllerDispatch`, rather than Berkowitz-specific storage proofs.

[`PolynomialBounds`](LeanCanny/Computation/PolynomialBounds.lean) extracts
explicit polynomial witnesses only at interfaces that need them. `PolyBound`
is a native `PolyBounded` specialization; its closure operations compose native
certificates. [`NativeSpaceClosure`](LeanCanny/Computation/NativeSpaceClosure.lean)
provides encoding-parametric PSPACE/tidy equivalence and reduction closure with
narrow imports. It is a candidate for a lightweight upstream space-closure module;
it avoids the hierarchy, probability, and Savitch dependencies of the broad
`Classes.Inclusions` module.

[`SymbolicPreparedTable`](LeanCanny/Algebra/SymbolicPreparedTable.lean) packages
exact node polynomials, degree metadata, and actual selected directions for
prepared tables. The coercive readers use its shared pair-recovery specification.
Exact-degree and fixed-envelope coordinates share one decoding induction while
retaining their respective polynomial representatives. Generic fixed-width,
homogenization, and residue-reader helpers similarly separate reusable packet
correctness from the coercive algebraic specialization.

Complexitylib's canonical repository is now
[`cslib-community/complexitylib`](https://github.com/cslib-community/complexitylib).
The project keeps its pre-rename revision and Lake identifier `complexitylib2`;
this link migration does not change the checked foundation or its pins.

## Unused tube route: remaining quantitative choices

The compact tube and generic projection development remains useful independently.
It proves qualitative ETR sampling equivalences, finite-fiber transfer,
coordinate annihilants, native finite-root sign tests, and exact PSPACE samplers
for compiled points with nonzero chart Jacobian. The completed coercive proof
does not invoke its unresolved outer parameter choices:

* A source-size bound for a positive epsilon retaining feasibility.
* An effective delta below the compact feasibility gap.
* A bounded rational direction retaining suitable finite projection samples.
* A bounded regular/retained alpha interval compatible with those choices.
* Native nested implicit substitutions for any exponentially long rational
  constants required by those choices.

`GenericProjectionJacobian` proves generic nonsingularity, and the actual generic
singular ideal is the whole ring. `TubeRegularJacobianReaders` computes its
integer determinant. `RowSpanEliminant` and `AffineMacaulayMatrix` give bounded
minor certificates from bounded affine row-span membership. The missing
arithmetic input for that approach is a source-bounded multiplier degree for
the singular ideal. Homogeneous Macaulay surjectivity alone does not supply it
when roots remain at infinity.

`CriticalValueIntegerAnnihilator` gives critical-value annihilants, and
`EffectiveRegularPolynomialLevels` turns a supplied mass bound `mass≤2^b` into
the regular interval `0<alpha≤2^(-(b+1))`. Those results do not bound b by the
tube input size. Qualitative rational density likewise gives no bit bound on
the neighborhood needed to retain a sample.

An explicit rational packet cannot store a dyadic denominator `2^s` in space
polynomial in the length of s when s is exponential. Implicit residues and all
nested specialization costs must be included. The coercive route resolves its
own one-parameter powers this way; it does not resolve the tube route's nested
choices.

## Savitch and further report results

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
This is a cardinality bound, not an effective root encoding or coefficient bound.

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
fiber local path connectivity from local product charts. `LocalProductBaseChange`
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
additive identities for the explicit homogenization. `FermatCriticalHomogenization`
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
`q(x)² + (sum(wᵢ²) - 2^(2R))²` in two extra variables. Its sublevels are compact,
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
degree/mass bounds apply to every coordinate index. `BoundedCriticalSampleTermTest`
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
The `PencilCuts`, `HashRoots`, `HashCuts`, and `HashEnumeration` modules identify
the exact integer hash values and enumerate every distinct child root exactly
once in hash order, retaining its original actual-sample base word.
`BoundedCriticalSampleFiberSignatureProbe` proves recovery from two determinant
coefficients, with a nonzero denominator at every valid root. The `ProbeEntries`,
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
to spatial regularity. `RegularAffineSubsetCount` applies the existing individual
coordinate eliminants to the regular subset, without requiring every root to be
regular or the full root set to be finite. The regular joint candidates therefore
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
binary degree and mass bounds for original terms pulled back to child parameters.
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
inputs and zero extension beyond the parent tuple. `BoundedCriticalSampleBlockConstraint`
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
the source readers across candidate-record metadata. `BoundedFullBlockDirectionChoice`
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
denominator powers use source-derived controls. `BoundedFullSampleBlockPolynomial`
recovers collected multivariate coefficients and derives degree, support,
coefficient-mass, and native binary budget bounds. `BoundedFullSampleBlockScaling`
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
n*(2*n+1) variables. This is a separate algebraic tower: its native coefficient
readers and integration with the existing regular-root sampling backend
remain to be constructed. Generic critical-stage regularity, selection of
recursive levels and directions, and component-preserving graph edges also
remain open.

The full effective recursion for arbitrary Boolean, singular, and noncompact
inputs, its component preservation, and its polynomial bounds remain open.
Neither requested full connectivity PSPACE theorem has been established.
