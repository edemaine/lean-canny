# lean-canny

A Lean formalization of the theorem that the
Existential Theory of the Reals (ETR) is in PSPACE,
or stated in terms of complexity-theory classes: ∃ℝ ⊆ PSPACE,
and native PSPACE bounds for semialgebraic point and whole-space connectivity.
This theorem is from John Canny's 1988 technical report
[*Some Algebraic and Geometric Computations in PSPACE*](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/6041.html)
(stored in this repo as [`canny-tr.pdf`](canny-tr.pdf)), published as a
[STOC ’88 paper](https://doi.org/10.1145/62212.62257) (pp. 460–467).

The main results in
[`ETR/CoercivePSPACE.lean`](LeanCanny/ETR/CoercivePSPACE.lean) are:

```lean
LeanCanny.ETR.etr_mem_PSPACE : LeanCanny.ETR.language ∈ LeanCanny.PSPACE
LeanCanny.ETR.existsReal_subset_PSPACE : LeanCanny.ExistsReal ⊆ LeanCanny.PSPACE
```

These are unconditional theorems for the project's encoded ETR language and
[CSLib Frontier](https://github.com/cslib-community/cslib-frontier)'s
machine-based PSPACE class. The coefficient algorithms,
metadata preparation, recursive evaluation, and final sign decisions are
constructed internally. The development uses Lean 4.36.0-rc2 with pinned
Mathlib, CSLib, and CSLib Frontier dependencies.

This establishes the report's ETR and connectivity PSPACE upper bounds for the
encoded problems below. Explicit roadmap output and motion-planning interfaces
are separate from these language-membership results.
The proof uses a coercive one-parameter sampling construction; it does not
formalize every intermediate construction in the report verbatim.

The formalization also identifies a [gap in Canny's coordinate-recovery
argument](RESEARCH.md#gap-in-cannys-symmetric-coordinate-recovery): three
collinear solutions can produce a cubic GCD where the construction requires a
linear one, regardless of the projection coefficients. The completed PSPACE
proof avoids this failed step.

For independently readable, checked statements of all three PSPACE bounds, see
[`Abstract.lean`](LeanCanny/Abstract.lean). A reader can inspect its definitions
and theorem statements to assess the claimed result; Lean verifies the proofs
through [`AbstractBridge.lean`](LeanCanny/AbstractBridge.lean) and the development.
All public definitions are local to the abstract or use background libraries.
A declaration-driven command generates the local flat token encoding using
CSLib Frontier encoders; its PSPACE transfer is checked
in [`AbstractEncodingBridge.lean`](LeanCanny/AbstractEncodingBridge.lean).

## ETR proof outline

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
CSLib Frontier's `ComputableInPolySpace`.
[`SpaceDecider`](LeanCanny/Computation/SpaceDecider.lean) carries membership in
its native PSPACE class. Polynomial-time reductions and all FP controls also
use CSLib Frontier directly. Space composition charges the original readers;
no free coefficient oracle or execution-time bound on a space-bounded child
is assumed.

## Alternative constructions

The default `LeanCanny` library and `import LeanCanny` contain the completed
ETR and connectivity proofs through the formal abstract. The optional
`LeanCannyAlternatives` library is available through
`import LeanCanny.Alternatives`; it also imports
the completed result. All source modules retain their existing paths.

The repository also develops Canny's compact tube and generic projection
constructions, projective elimination, finite-root sign feasibility, and
nonsingular tube sampling. These are independently proved ingredients and
alternative samplers. The tube route's effective epsilon/delta/direction and
retained-level choices are unresolved; the completed ETR theorem uses the
coercive route and does not depend on those choices.

Further work includes relating this encoding to other ETR presentations,
proving the NP lower inclusion, and constructing explicit roadmaps and
motion-planning interfaces. The alternative library remains checked by the full
verification commands below.
See [`RESEARCH.md`](RESEARCH.md) for prior work,
proof details, and the unused tube route's precise gaps.

## Counting-hierarchy extension

The optional `LeanCannyCountingHierarchy` target (`import LeanCanny.CountingHierarchy`)
formalizes the fixed counting-level upper bounds of OpenAI's October 4, 2026 preprint
[*Existential–universal real sentences in the counting hierarchy*](https://github.com/openai/math/blob/main/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/etr-counting-hierarchy.pdf).
It uses CSLib Frontier's fixed-oracle, majority-verifier counting levels.

`Controlled` supplies binary degree, coefficient-mass exponent and prime-cutoff
bounds, unary arity, and one uniform modular evaluator. Constants, variables,
addition, multiplication and binary-indexed powers have constructed evaluators
at the same function level. Controlled zero-variable families inherit Frontier's
`F_(max(a,5)+3)` sign bound.

Finite-field orthogonality gives simultaneous multivariate coefficient extraction
as one grid sum, including zero variables. A base-`p` address decodes the entire
point in polynomial time, so the uniform multivariate evaluator has a checked
`F_a → F_(a+1)` certificate with variable unary arity. It returns the canonical
coefficient residue when the total degree and coordinate indices are below `p-1`.
Addressed coefficients of controlled integer families inherit the original mass
bound and have signs in `F_(max(a+1,5)+3)`.

Binary-indexed factorial residues are available in `F_3`. The truncated-exponential
module constructs the polynomial expression used in characteristic reconstruction,
its modular evaluation and its indexed coefficient evaluator, with fixed CH bounds.
Divided negative trace slots are constructed by modular powering. Supplied
`F_(a+2)` trace residues yield an `F_(a+8)` indexed exponential coefficient evaluator,
including reversal of the coefficient index and zero above the dimension.
Jacobi's polynomial determinant identity gives Newton's recurrence over arbitrary
commutative rings. Over fields with nonzero denominators through the truncation
degree, the finite exponential satisfies that recurrence and has the same
coefficients as the reversed characteristic polynomial. The modular evaluator
therefore returns actual characteristic coefficients from modular power traces,
including zero above the dimension.

For pure-power systems, a finite residue functional descends to the actual relation
ideal. Degree induction and the residue pairing prove that the normal monomials
form a basis over any commutative coefficient ring. A normalized Bezout kernel
then proves the multiplication trace–residue identity, including multiple roots
and specialization to arbitrary characteristic.

Uniform `F_a` evaluators for the objective, lower relations and Jacobian now
construct power traces in `F_(a+5)` and indexed characteristic coefficients in
`F_(a+8)`. The proof uses the actual normal-basis multiplication matrix and
commutes with arbitrary coefficient-ring specialization. No trace or
characteristic-coefficient oracle is assumed.

The complete finite determinant criterion is proved for nonnegative integer
polynomials. Coercive minima and the explicit separated centers give a monic,
separable critical-value specialization with source-derived degree and log-mass
bounds. Integer value resultants bound nonzero algebraic test values, including
nonmonic and repeated-root source polynomials. Rational sign products and positive
denominator clearing turn short derivative-test lists into integer root labels
with uniform margins. Conjugate-pair products then identify feasibility with a
negative actual quotient multiplication determinant for one short label and shift.

Native evaluators construct the objective, relations and small Jacobian from
source evaluations, using one additional level for simultaneous first and mixed
second derivatives. The critical coefficients cost nine levels, the sparse label
thirteen, the final integer norm twenty-one and its sign twenty-four. Polynomial-width
coded witnesses and one bounded existential step prove `Controlled.feasibility_mem`:
real feasibility of any controlled `F_a` family lies in `C_(a+26) P`.

The native modular expression-tree evaluator connects this result to the existing
equation compiler: `etr_mem_CountingLevel` proves the repository's total encoded ETR
language belongs to `C_26 P`, and `existsReal_subset_CountingLevel` transfers the bound
to all of ∃ℝ. The controlled-family theorem supports general degrees.

For the two-block construction, finite-field fingerprints now select any prescribed
real root. Their integer positivity labels have uniform margins and explicit degree
and log-mass bounds; addressed coefficients give a native label evaluator in
`F_(max(a,3)+8)`. Joint continuity of coercive fiber minima and their divergence on
empty fibers are proved. Coordinate characteristic polynomials supply one integer
candidate grid meeting every nonempty relatively clopen part of a zero set, using
the existing constrained compactness argument. The fixed-power algebraic growth test,
local constancy of empty fibers on degree pieces, and the inverse-variable closed
lift are proved. Native controlled families instantiate the full construction:
`Controlled.twoBlock_mem` places existential-universal zero avoidance for any
controlled `F_a` polynomial family in `C_(a+60) P`, including empty blocks.

`ExistsForall.mem_CountingLevel` places the total encoded existential-universal
real language in `C_60 P`. Its encoding pairs a unary existential block length
with an arbitrary Boolean formula over integer polynomial expression trees;
all remaining variables are universal. The equation compiler preserves the
existential prefix while introducing counterexample variables. Noncanonical
frames and malformed formulas are rejected. `ExistsForall.RealClass` is the
polynomial-time many-one downward closure, with the same `C_60 P` bound.

Shared arithmetic circuits use shallow equations for their intermediate wires.
`RealCircuit.sentence_iff` proves that universally quantified wire values under
these equations agree with the actual acyclic circuit run; the original two
blocks are preserved. `RealCircuit.guardedBits_mem_FP` supplies the native matrix
writer, and `RealCircuit.generated_mem_CountingLevel` transfers the `C_60 P`
bound to native circuit families. The existential circuit bridge similarly
retains the sharper `C_26 P` bound. Gate equations retain sharing, so the bridge
does not expand a circuit into its computed polynomial.

| Result | Entry point |
| --- | --- |
| Controlled feasibility in `C_(a+26) P` | [ControlledFeasibility.lean](LeanCanny/CountingHierarchy/ControlledFeasibility.lean) |
| Encoded ETR and ∃ℝ in `C_26 P` | [ExistentialUpperBound.lean](LeanCanny/CountingHierarchy/ExistentialUpperBound.lean) |
| Controlled two-block zero avoidance in `C_(a+60) P` | [ControlledTwoBlockDecision.lean](LeanCanny/CountingHierarchy/ControlledTwoBlockDecision.lean) |
| Encoded existential-universal sentences in `C_60 P` | [ExistsForallUpperBound.lean](LeanCanny/CountingHierarchy/ExistsForallUpperBound.lean) |
| Shared-circuit semantics and native writers | [RealCircuit.lean](LeanCanny/CountingHierarchy/RealCircuit.lean) |

```sh
lake build LeanCannyCountingHierarchy --wfail --iofail
lake env lean scripts/CheckCountingHierarchy.lean
```

The standalone check also audits the CH declarations and their transitive
dependencies for standard Lean axioms.

## Connectivity

The separate `LeanCannyConnectivity` target (`import LeanCanny.Connectivity`)
proves both original connectivity languages are in native PSPACE:

```lean
LeanCanny.Connectivity.pointLanguage_mem_PSPACE :
  LeanCanny.Connectivity.pointLanguage ∈ LeanCanny.PSPACE
LeanCanny.Connectivity.connectedLanguage_mem_PSPACE :
  LeanCanny.Connectivity.connectedLanguage ∈ LeanCanny.PSPACE
```

The closed statements are in
[`NativeConnectivityPSPACE.lean`](LeanCanny/Connectivity/NativeConnectivityPSPACE.lean).
Inputs contain a unary dimension and arbitrary Boolean combinations of integer
polynomial sign conditions. Point inputs describe singleton endpoints by formulas,
allowing irrational algebraic points. Whole-space connectivity means
`IsPreconnected`, accepting the empty set. Malformed, ill-scoped, inconsistent
and nonunique endpoint inputs are rejected. Neither theorem takes a geometric
model, component oracle, edge evaluator or radius bound as a premise.

The construction checks both original component labels, the actual radial grid
and every interval cut on one complete sampler tuple. The original frontier
edge is exactly projected-sample equality or oriented guarded joint feasibility.
Endpoint formulas select existing samples after adding tautologies that preserve
the space. Native finite graph scans finish both decision procedures.
See the [connectivity proof outline](RESEARCH.md#connectivity-proof-outline)
and [correctness pitfalls](RESEARCH.md#connectivity-correctness-pitfalls)
for the construction and the failed shortcuts it must avoid. Detailed
[construction notes](CONNECTIVITY-PROTOTYPE.txt) and the
[historical checkpoint ledger](CONNECTIVITY-HISTORY.md) are separate.

## Attribution and report integrity

The Sturm–Tarski proof adaptation and its changes are documented in
[`STURM_SOURCES.md`](STURM_SOURCES.md).

The report PDF [`canny-tr.pdf`](canny-tr.pdf) is from the
[Berkeley Technical Reports archive](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/Archive/CSD-88-439.pdf).
The downloaded file has 936,246 bytes and SHA-256
`7606d41dea23ac1160562a759c196267906d8aec0f754cd4998fdd14fcd185f8`.
The report retains its original rights; the source-code license does not apply
to it.

## Build and verification

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build
```

[`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json)
record the versions used. The default entry point is [`LeanCanny.lean`](LeanCanny.lean).
`lake build` checks the formal abstract and its completed proofs. To build the
retained alternative constructions, run `lake build LeanCannyAlternatives`;
their entry point is [`Alternatives.lean`](LeanCanny/Alternatives.lean).
Build the connectivity extension with `lake build LeanCannyConnectivity`.

Import the formal abstract with `import LeanCanny.Abstract`, or build it with
`lake build --wfail LeanCanny.Abstract`. It is also included in the default build.

Dependencies are pinned to CSLib Frontier revision `1a0acf76` and Lean
`v4.36.0-rc2`, with matching CSLib and Mathlib revisions. The Lake package is
`cslib-frontier`, from its canonical `cslib-community/cslib-frontier` repository.
The build targets above require only their transitive dependency imports;
they do not build CSLib Frontier's full library or result collection.

For stricter verification:

```sh
lake build LeanCanny LeanCannyAlternatives LeanCannyConnectivity LeanCannyCountingHierarchy --wfail --iofail
lake env lean scripts/CheckCoreImports.lean
lake env lean scripts/CheckAxioms.lean
lake env lean scripts/CheckAbstract.lean
lake env lean scripts/CheckAbstractEncoding.lean
lake env lean scripts/CheckGrammar.lean
lake env lean scripts/CheckSpaceFoundation.lean
lake env lean scripts/CheckPolyTimeFoundation.lean
lake env lean scripts/CheckCountingHierarchy.lean
lake env lean scripts/CheckConnectivity.lean
lake env lean scripts/CheckJointFrontier.lean
lake env lean scripts/CheckConnectivityPSPACE.lean
lake env lean scripts/CheckImplicitStratumSampler.lean
lake env lean scripts/CheckEffectiveBallConnections.lean
lake env lean scripts/CheckProviderAtomic.lean
lake env lean scripts/CheckProviderSemantics.lean
lake env lean scripts/CheckProviderRecursive.lean
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
lake env lean scripts/CheckRoadmapBridges.lean
lake env lean scripts/CheckRoadmapChains.lean
lake env lean scripts/CheckRoadmapEncoding.lean
lake env lean scripts/CheckRoadmapInternal.lean
lake env lean scripts/CheckRoadmapLevels.lean
lake env lean scripts/CheckRoadmapNativeGraph.lean
lake env lean scripts/CheckRoadmapOccurrences.lean
lake env lean scripts/CheckRoadmapOrigins.lean
```

The core import check keeps the ETR endpoint independent of the optional tube
route. The formal abstract also imports connectivity and its shared algebra.
The axiom audit includes all four library targets; the space audit covers the
three PSPACE targets. The axiom audit checks
declarations in the `LeanCanny` namespace, local Nat
codec extensions, and their transitive dependencies, allowing only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms. The foundation
checks enforce the native CSLib Frontier time and space interfaces and reject
legacy machine dependencies. `CheckAbstract` also follows public definitions
and statement dependencies to reject hidden implementation references.
