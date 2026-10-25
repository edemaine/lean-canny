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

The full effective recursion for arbitrary Boolean, singular, and noncompact
inputs, its component preservation, and its polynomial bounds remain open.
Neither requested full connectivity PSPACE theorem has been established.
