# Semialgebraic Complexity in Lean

This repository contains Lean formalizations of complexity upper
bounds for quantified semialgebraic formula satisfiability
(**theory of the reals**) and
semialgebraic configuration space connectivity.
Specifically, it proves these theorems:

- **[Existential Theory of the Reals (ETR)](https://en.wikipedia.org/wiki/Existential_theory_of_the_reals) / [∃ℝ](https://en.wikipedia.org/wiki/Existential_theory_of_the_reals)** ≈
  SAT / NP over the reals, with polynomial equations and inequalities.
  - ETR ∈ [PSPACE](https://en.wikipedia.org/wiki/PSPACE) and ∃ℝ ⊆ PSPACE
    [[Canny 1988](#ref-canny-1988)].
  - ETR ∈ C₂₆P and ∃ℝ ⊆ C₂₆P [[OpenAI 2026](#ref-openai-2026)], where C₂₆P is a fixed level of the
    [counting hierarchy (CH)](https://en.wikipedia.org/wiki/Counting_hierarchy).
- **Existential–Universal Theory of the Reals / ∃∀ℝ** ≈
  [Σ₂ᴾ](https://en.wikipedia.org/wiki/Polynomial_hierarchy#Quantified_Boolean_formulae_definition) over the reals.
  - ∃∀ℝ ⊆ C₆₀P [[OpenAI 2026](#ref-openai-2026)], where C₆₀P is a fixed level of the
    [counting hierarchy (CH)](https://en.wikipedia.org/wiki/Counting_hierarchy).
    OpenAI's manuscript states a fixed but unspecified level; this formalization supplies 60.
- **Semialgebraic connectivity:**
  [semialgebraic set](https://en.wikipedia.org/wiki/Semialgebraic_set)
  point-to-point reachability and whole-set connectivity
  are in PSPACE [[Canny 1988](#ref-canny-1988)].
- **Arithmetic circuits:** the same CH bounds hold for
  inputs that share intermediate computations (DAGs instead of trees)
  [[OpenAI 2026](#ref-openai-2026)].

Approximate sizes of the formalizations:

| Result | Lean source lines |
| --- | ---: |
| ETR ∈ PSPACE; ∃ℝ ⊆ PSPACE | ≈ 91,000 |
| ETR ∈ C₂₆P; ∃ℝ ⊆ C₂₆P | ≈ 42,000 |
| ∃∀ℝ ⊆ C₆₀P | ≈ 69,000 |
| Point reachability and whole-set connectivity in PSPACE | ≈ 503,000 |
| Arithmetic-circuit CH bounds | ≈ 70,000 |

Counts include each implementation’s transitive local imports, comments, and
blank lines; they exclude Mathlib, CSLib, and CSLib Frontier. Shared files count
toward every result that uses them.

## Motivation

I started this project because I was worried that Canny's PSPACE membership
proofs from 1988 were simultaneously very important, very complicated, but not
very thoroughly checked (e.g., no journal version). Luckily, it turns out that
the main complexity bounds hold! However, there was one small bug: see the
[coordinate-recovery counterexample and how the completed proof avoids it](RESEARCH.md#gap-in-cannys-symmetric-coordinate-recovery).

Then the project grew to formalize the counting-hierarchy results of
OpenAI's 2026 strengthening of the ETR bounds,
which had yet to be formalized.

## Formal abstract

To verify that this repository proves what it should, read
[`Abstract.lean`](LeanCanny/Abstract.lean), which presents
independently readable definitions and checked theorem statements.
Those definitions and statements use only notions introduced in that file,
[Mathlib](https://github.com/leanprover-community/mathlib4), and
[CSLib Frontier](https://github.com/cslib-community/cslib-frontier).
Lean verifies the proofs through two bridge files:
[one for PSPACE results](LeanCanny/AbstractBridge.lean) and
[one for CH results](LeanCanny/CountingHierarchy/AbstractBridge.lean).

## Build and verification

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build
```

[`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json)
record the pinned versions of Lean and the dependencies. The default build checks
the unified abstract and its PSPACE, CH, and connectivity proofs. Import it with
`import LeanCanny` or `import RealCountingHierarchy`.

To audit the abstract's definitions, statements, axioms, and encoding:

```sh
lake env lean scripts/CheckAbstract.lean
lake env lean scripts/CheckAbstractEncoding.lean
```

The axiom checks allow only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms. The abstract audit also checks that public definitions and
statements do not depend on implementation declarations.

Run [the verification script](scripts/verify.sh) with Bash:

```sh
bash scripts/verify.sh
```

It builds all five library targets, then runs every `scripts/Check*.lean` audit
with warnings treated as errors, stopping on the first failure. New audit files
are included automatically.

<details>
<summary>Optional build targets and audit details</summary>

The optional `LeanCannyAlternatives` target builds the retained alternative
constructions (`import LeanCanny.Alternatives`). The connectivity and CH
implementations can also be built separately with `LeanCannyConnectivity` and
`LeanCannyCountingHierarchy`, respectively.

The core import check keeps the ETR endpoint independent of the optional tube
route. The formal abstract also imports connectivity and its shared algebra.
The axiom audit includes all five library targets; the space audit covers the
three PSPACE targets. The axiom audit checks
declarations in the `LeanCanny` namespace, local Nat
codec extensions, and their transitive dependencies, allowing only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms. The foundation
checks enforce the native CSLib Frontier time and space interfaces and reject
legacy machine dependencies. `CheckAbstract` also follows public definitions
and statement dependencies to reject hidden implementation references.

</details>

## PSPACE upper bounds [[Canny 1988](#ref-canny-1988)]

The PSPACE endpoints in
[`ETR/CoercivePSPACE.lean`](LeanCanny/ETR/CoercivePSPACE.lean) are:

```lean
LeanCanny.ETR.etr_mem_PSPACE : LeanCanny.ETR.language ∈ LeanCanny.PSPACE
LeanCanny.ETR.existsReal_subset_PSPACE : LeanCanny.ExistsReal ⊆ LeanCanny.PSPACE
```

These theorems concern the project's encoded ETR language and CSLib Frontier's
machine-based PSPACE class. The proof uses a coercive one-parameter sampling
construction rather than following every intermediate construction in Canny's
report verbatim.

### ETR proof outline

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

## Counting-hierarchy upper bounds [[OpenAI 2026](#ref-openai-2026)]

The encoded-language bounds are proved in
[`ExistentialUpperBound.lean`](LeanCanny/CountingHierarchy/ExistentialUpperBound.lean)
and [`ExistsForallUpperBound.lean`](LeanCanny/CountingHierarchy/ExistsForallUpperBound.lean).
The proof replaces real quantification with determinant-sign tests and bounded
searches whose counting-hierarchy levels can be tracked explicitly.

### Counting-hierarchy proof outline

1. **Compile the real formulas.** For ETR, Boolean combinations of polynomial
   comparisons become one polynomial equation. For an existential–universal
   sentence, compile a counterexample to its matrix: truth means that some
   existential assignment admits no universal counterexample.
2. **Compute critical-value information without expanding polynomials.**
   Modular polynomial evaluations supply coefficient access. A finite quotient
   algebra and a trace–residue identity give power traces; Newton's identities
   recover characteristic coefficients. These computations stay within fixed
   counting levels even when the expanded polynomials are large.
3. **Reduce real feasibility to determinant signs.** Coercive perturbations
   yield critical samples. Short algebraic root labels and quantitative separation
   bounds turn feasibility into a determinant-sign test with a bounded witness.
   Tracking the evaluation and sign costs gives ETR ∈ C₂₆P; closure under
   polynomial-time reductions gives ∃ℝ ⊆ C₂₆P.
4. **Handle the universal block with two feasibility tests.** A finite candidate
   grid and root-selection labels identify existential assignments. For each
   selected candidate, one test establishes that it exists and a second checks
   for a universal counterexample. Continuity and algebraic growth bounds prove
   that the candidate search is complete. The resulting decision procedure and
   reduction closure give ∃∀ℝ ⊆ C₆₀P.
5. **Preserve the bounds for encoded formulas and circuits.** Polynomial-time
   translations connect the mathematical tests to the input languages and reject
   malformed strings. Circuits introduce equations for shared intermediate values,
   preserving the quantifier blocks without expanding the circuit into a tree.

Selected entry points:

| Result | Entry point |
| --- | --- |
| Controlled feasibility in `C_(a+26) P` | [ControlledFeasibility.lean](LeanCanny/CountingHierarchy/ControlledFeasibility.lean) |
| Encoded ETR and ∃ℝ in `C_26 P` | [ExistentialUpperBound.lean](LeanCanny/CountingHierarchy/ExistentialUpperBound.lean) |
| Controlled two-block zero avoidance in `C_(a+60) P` | [ControlledTwoBlockDecision.lean](LeanCanny/CountingHierarchy/ControlledTwoBlockDecision.lean) |
| Existential–universal truth and ∃∀ℝ in `C_60 P` | [ExistsForallUpperBound.lean](LeanCanny/CountingHierarchy/ExistsForallUpperBound.lean) |
| Shared-circuit semantics and native writers | [RealCircuit.lean](LeanCanny/CountingHierarchy/RealCircuit.lean) |

See the [CH construction details](RESEARCH.md#counting-hierarchy-construction-details)
for the polynomial-family interfaces, coefficient algorithms, and level accounting.

## Connectivity

The connectivity implementation (`import LeanCanny.Connectivity`) proves:

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

### Connectivity proof outline

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

## Alternatives and future work

The repository also develops Canny's compact tube and generic projection
constructions, projective elimination, finite-root sign feasibility, and
nonsingular tube sampling. These are independently proved ingredients and
alternative samplers. The tube route's effective epsilon/delta/direction and
retained-level choices are unresolved; the completed ETR theorem uses the
coercive route and does not depend on those choices.

Further work includes relating this encoding to other ETR presentations,
proving the NP lower inclusion, and constructing explicit roadmaps and
motion-planning interfaces. The alternative library is included in the full
verification commands above.
See [`RESEARCH.md`](RESEARCH.md) for prior work,
proof details, and the unused tube route's precise gaps.

## References

- <a id="ref-canny-1988"></a>John F. Canny. [*Some Algebraic and Geometric Computations in PSPACE*](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/6041.html).
  Technical Report UCB/CSD-88-439, University of California, Berkeley, August 1988.
  [PDF in this repository](canny-tr.pdf).
- John F. Canny. [*Some Algebraic and Geometric Computations in PSPACE*](https://doi.org/10.1145/62212.62257).
  Proceedings of the 20th Annual ACM Symposium on Theory of Computing (STOC ’88),
  ACM, 1988, pp. 460–467.
- <a id="ref-openai-2026"></a>OpenAI. [*Existential–universal real sentences in the counting hierarchy*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/etr-counting-hierarchy.pdf).
  OpenAI Math Release preprint, October 4, 2026.

## Attribution

The Sturm–Tarski proof adaptation and its changes are documented in
[`STURM_SOURCES.md`](STURM_SOURCES.md).

The report PDF [`canny-tr.pdf`](canny-tr.pdf) is from the
[Berkeley Technical Reports archive](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/Archive/CSD-88-439.pdf).
The report retains its original rights; the source-code license does not apply
to it.
