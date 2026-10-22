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
The isolated [Complexitylib prototype](experiments/complexitylib2/README.md)
records the composition experiments, including a space-bounded child with
exponential running time.

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

Upstream `Classes.Inclusions` supplies exact PSPACE/tidy-machine equivalences
and reduction closure. Using it here would replace small local adapters but
add the PH, PP, probability, and Savitch dependency graph. A lightweight upstream
`Space.Closure` module would make those replacements useful; the current
adapters retain their narrower imports.

Upstream `polytime`, `fun_prop`, and `program_certificate` could also replace
much of the local proof-search machinery. This needs a small compatibility layer:
normalize `FP`/`UnaryFn` goals and local certificates to the native predicate,
extract a Boolean verdict for `FPPred`, and register native-form certificates for
the raw pair codec. Typed `encPair` projections do not implement that codec.
A prototype should retain the existing tactic as a fallback until local-function,
encoded-output, predicate-scan, and malformed-packet regressions pass.

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
