# Prior work and choice of complexity infrastructure

Investigation date: 2026-10-19. Negative findings below describe the repositories and
searches checked; they are not claims that no such formalization exists anywhere.

## Existing real-algebraic formalizations

* [TauCeti](https://github.com/TauCetiProject/TauCeti) includes real-algebraic
  quantifier elimination, CAD existence, Tarski–Seidenberg, and Sturm–Tarski/sign
  determination. See
  [quantifier elimination](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/Semialgebraic/QuantifierElimination.lean)
  and [recursive sign determination](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/SignDetermination/Recursive.lean).
  The inspected sign-determination construction uses noncomputable choices. Its
  correctness results do not supply Canny's workspace bound.
* [Hex](https://github.com/leanprover/hex) develops exact real-algebraic computation,
  including root isolation, algebraic numbers, resultants, and real-closed-field
  tactics. Such arithmetic can be useful without establishing a PSPACE bound for ETR.
* Isabelle AFP has [Ben-Or–Kozen–Reif](https://www.isa-afp.org/entries/BenOr_Kozen_Reif.html)
  and [hybrid real quantifier elimination](https://www.isa-afp.org/entries/Quantifier_Elimination_Hybrid.html).
  These are relevant algorithmic correctness precedents in a different prover.
* Coq has Cohen and Mahboubi's real-closed-field quantifier elimination and
  [MathComp CAD](https://github.com/math-comp/cad). These are additional prior work,
  rather than Lean complexity-class interfaces.

No existing encoded ∃ℝ complexity-class definition or formal proof of `ETR ∈ PSPACE`
was found in the inspected Mathlib, Complexitylib, CSLib, TauCeti, or adjacent projects.
The ∃ℝ definition in this project uses the standard reduction-class formulation;
equivalence with other finite presentations requires explicit efficient translations.

Mathlib already proves the ordinary
[primitive element theorem](https://github.com/leanprover-community/mathlib4/blob/728a93eeff833da3173895bb0575752fdc24edb0/Mathlib/FieldTheory/PrimitiveElement.lean),
including a linear-GCD argument for two separable elements. Its Galois fixed-field and
Lagrange interpolation theorems also supply the algebraic tools used here. The current
project strengthens the representation interface to all pairs of roots of two input
polynomials, with one bounded integer selector, a monic separable degree-`d₁*d₂`
polynomial, and coordinate polynomials over the input field. The GCD coefficient-ratio
recovery specification is proved. The parameter polynomial now uses Mathlib's
[Sylvester resultant](https://github.com/leanprover-community/mathlib4/blob/728a93eeff833da3173895bb0575752fdc24edb0/Mathlib/RingTheory/Polynomial/Resultant/Basic.lean),
with verified specialization, roots, scalar normalization, and degree. Taylor and Hasse
derivatives supply a direct shifted-coefficient formula and integer bit-length bounds.
The project now bounds coefficients of polynomial determinants by column coefficient
masses, and specializes this estimate to the integer resultant. Its degree is at most
`d₁*d₂` without nonzero or separability hypotheses, and its coefficient bit lengths
are bounded explicitly in the input degrees, coefficient lengths, and direction length.
Encoded determinant and subresultant algorithms, subresultant output-size bounds,
and the report's space bounds remain open; the size estimates alone do not establish
an algorithm with the required workspace.

## TM2 versus Complexitylib's machines

The distinction affects implementation and resource-accounting effort, even though
the intended polynomial-space classes agree mathematically.

* `lean-trominoes` uses Mathlib's `FinTM2`: a finite collection of stacks and structured
  statements for push, pop, peek, branching, and control transfer. Its PSPACE package
  requires finite alphabets on **all** stacks and bounds the total occupied stack
  cells on every reachable configuration. Finite labels and finite internal state
  prevent storage hidden in the control. Its input cells count toward space.
* [Complexitylib's base model](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Models/TuringMachine.lean)
  is a custom multitape TM, structurally closer to Mathlib's TM0 than to TM2. It uses
  local read/write/head transitions, a fixed four-symbol alphabet, read-only input,
  and named work/output tapes. It is not an instance of Mathlib's TM0. Its decision
  space predicate also bounds output and excursions of the input head.

TM2 gives a more convenient programming language, but not free arithmetic on arbitrary
integers. Such values still need finite encodings and proofs about the space used to
manipulate them. Conversely, using Complexitylib need not mean writing every algorithm
as individual tape transitions:

* [`SpaceIter.mem_PSPACE_of_iterate`](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Classes/Space/Iterate.lean)
  supplies a machine from a polynomial-time bitstring step function, polynomially
  bounded states, and a bounded terminating run (at most `2^poly` steps). There are
  also FP composition/iteration tools and polynomial-space folds.
* `lean-trominoes` has evaluator workspace certificates and a prepared-evaluator
  bridge to its TM2 PSPACE predicate. These can avoid rebuilding stack accounting
  for each arithmetic subroutine. The bridge already composes polynomial-time input
  preparation with space-certified evaluation, retaining the original input-length
  parameter. This is a concrete advantage. Its benefit depends on implementing the
  algorithm in that evaluator language.

Complexitylib also defines a higher-level
[rose-tree machine language](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Models/RoseTreeMachine/Prog.lean).
Its documentation explicitly states that no simulation theorem connecting its cost
model to the multitape TM has been proved. An RTM cost certificate alone would therefore
leave a bridge obligation before establishing membership in Complexitylib's `FP` or `PSPACE`.

An ordinary tape can be represented by two stacks, and finite alphabets admit
constant-size binary codes. This explains why a space-preserving simulation is
plausible, up to input-size overhead. **No proved bridge between these two library
PSPACE predicates has been established in this project.** Existing Mathlib
computability simulations cannot simply be assumed to preserve the required space.

The useful benchmark is a concrete symbolic-arithmetic routine with encoded inputs,
encoded intermediate states, and a workspace proof through the intended iteration
interface. For Canny, streamed access to large symbolic objects matters more than
the surface machine language alone. Complexitylib is currently pinned for its
reduction infrastructure; the algorithm backend remains undecided. A separate module
would be justified by reusable interfaces or proved interoperability, not merely by
having fewer files.

The project now supplies a concrete benchmark for that comparison: a continuation
machine for one entry of a matrix power, with balanced recursion and a streamed
summation. Its result, exact abstract transition count, and logarithmic frame count
are proved. Its binary representation is injective, and states over `ZMod m` have
a quadratic bound in the binary lengths of the dimension, exponent, and modulus.
Exact decoding and a total encoded transition now preserve the typed run and its
state-size bound. Binary normalization, successor, predecessor, and exponent halves
have actual Complexitylib FP certificates, as do the initial and child-query writers.
Binary natural-number addition, multiplication, and multiply-accumulate are now
certified too, with exact semantics on all words and bounds on every fold state.
The run still uses a supplied entry function and abstract scalar operations.
Certifying the full encoded step, including parsing, uniform entry access, and
modular reduction, remains the backend obligation; the representation bound alone
is not a TM space certificate.

Local comparison sources, at `lean-trominoes` commit
`6fe52dd234bb616fd4fb3c1e7b0a203de1482bc5`:

* `../lean-trominoes/LeanTrominoes/Complexity/Complexity.lean`
* `../lean-trominoes/LeanTrominoes/Computation/Partrec/PartrecPreparedEvaluatorSpace.lean`
* `../lean-trominoes/LeanTrominoes/Computation/Partrec/PartrecGenericSavitchReachSpace.lean`

The current `lean-wang` main branch inspected earlier did not itself define PSPACE;
the relevant Mathlib-only package was found in `lean-trominoes`.

## Savitch's theorem and Canny

Savitch is useful for reachability in an implicitly represented exponential graph,
as occurs in the report's roadmap/motion-planning consequences. Each vertex and the
recursion stack need polynomial-size representations. The adjacency algorithm also
needs a proved workspace bound; treating adjacency as a free Boolean oracle would
leave an essential gap.

The report's §3.1 ETR procedure instead gives a deterministic enumeration and algebraic
sign-testing argument. Savitch is not a substitute for its algebraic space analysis,
and need not be a dependency of that particular proof.

Savitch support is available in **both** candidate libraries:

* [Complexitylib](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Classes/Containments/NPSPACESubsetPSPACE.lean)
  proves `NPSPACE ⊆ PSPACE` and equality of the two polynomial-space classes. Its
  public statement explicitly does not provide the general quantitative theorem
  `NSPACE(S) ⊆ DSPACE(S²)`.
* `lean-trominoes` has a generic Savitch evaluator, reachability correctness, encoded
  search-state bounds, and workspace certificates. Its generic leaf interface accepts
  an evaluator-space certificate for adjacency, not only a polynomial-time test.

Neither result automatically transports algorithms or class membership across the
two machine models.
