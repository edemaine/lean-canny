# lean-canny

Foundations for formalizing John Canny's 1988 report,
[*Some Algebraic and Geometric Computations in PSPACE*](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/6041.html).
The report is saved as [`canny-tr.pdf`](canny-tr.pdf).

**Canny's PSPACE upper bound is not proved here yet.** The current development defines
an encoded existential theory of the reals (ETR), its reduction class ∃ℝ, and several
algebraic ingredients. It uses Lean 4 and pinned Mathlib/Complexitylib dependencies.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build
```

`lean-toolchain` and `lake-manifest.json` record the versions used. The public entry
point is [`LeanCanny.lean`](LeanCanny.lean).

For stricter verification:

```sh
lake build --wfail
lake env lean scripts/CheckAxioms.lean
lake env lean scripts/CheckGrammar.lean
```

The audit checks all declarations in the `LeanCanny` namespace and their transitive
dependencies, allowing only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms.

## Proved so far

| Module | Result |
| --- | --- |
| [`ETR.Syntax`](LeanCanny/ETR/Syntax.lean) | Integer polynomial expressions; Boolean combinations of equality and strict inequality; real semantics; equivalence between an infinite assignment and a finite existential block. |
| [`ETR.Encoding`](LeanCanny/ETR/Encoding.lean) | A canonical binary codec with both round-trip laws; the ETR language rejects malformed strings. Integer constants use binary magnitudes; variable indices use unary. |
| [`ETR.EncodingBounds`](LeanCanny/ETR/EncodingBounds.lean) | Formula arity is at most encoded input length; binary integer payloads have linear bit overhead. |
| [`Encoding.Brackets`](LeanCanny/Encoding/Brackets.lean), [`BracketsFP`](LeanCanny/Encoding/BracketsFP.lean) | A numerical bracket criterion recognizes exactly the image of `Data.toBits`; its one-bit recognizer belongs to Complexitylib's machine-level `FP`. |
| [`Encoding.BracketAccess`](LeanCanny/Encoding/BracketAccess.lean) | Polynomial-time splitting of the first serialized node, child access, enclosing-bracket operations, and cons; exact behavior is proved against the dependency codec. |
| [`ETR.EncodingFP`](LeanCanny/ETR/EncodingFP.lean) | Polynomial-time unary-field writing and recognition, fresh-variable writing, and tagged-node construction; agreement with the typed term/formula encodings. |
| [`ETR.NumericPayloadFP`](LeanCanny/ETR/NumericPayloadFP.lean) | Polynomial-time recognition of exactly the canonical natural and signed-integer payload codes. A finite-state bit-node decoder keeps magnitudes as binary digit lists, with a linear output bound. |
| [`Encoding.TreeFold`](LeanCanny/Encoding/TreeFold.lean), [`TreeFoldFP`](LeanCanny/Encoding/TreeFoldFP.lean) | A bottom-up stack pass agrees with a generic fold on `Data` trees. Fixed finite frames with positive fixed-width injective codes give a uniform machine-level `FP` implementation, with every intermediate stack bounded. |
| [`Encoding.FiniteTreeLanguage`](LeanCanny/Encoding/FiniteTreeLanguage.lean) | Every finite-frame tree classifier yields a polynomial-time predicate on complete canonical tree encodings. |
| [`Encoding.DynamicTreeFold`](LeanCanny/Encoding/DynamicTreeFold.lean) | Input-dependent tree folds can use variable-length frames in a self-delimiting stack. Polynomial-time frame operations and polynomial intermediate stack bounds give `FP`; a polynomial additive frame-growth allowance supplies the stack bound automatically. |
| [`ETR.SyntaxClassifier`](LeanCanny/ETR/SyntaxClassifier.lean), [`SyntaxClassifierCorrect`](LeanCanny/ETR/SyntaxClassifierCorrect.lean) | A finite summary of children recognizes unary fields, bit nodes, canonical binary magnitudes, integers, terms, and formulas; every flag is proved equivalent to the corresponding typed codec image. |
| [`ETR.Grammar`](LeanCanny/ETR/Grammar.lean) | Executable, machine-certified polynomial-time recognizers for exactly the canonical term and formula encodings. Both syntax languages belong to `P`; the formula checker agrees with successful parsing by the original decoder. |
| [`ETR.Complexity`](LeanCanny/ETR/Complexity.lean) | ∃ℝ is the downward closure of ETR under Complexitylib polynomial-time many-one reductions; ETR is complete by definition; reduction closure and `P ⊆ ∃ℝ`. |
| [`ETR.Normalization`](LeanCanny/ETR/Normalization.lean) | Single inequalities and disequalities become equations using fresh witnesses; pairs of equations combine through sums of squares or products. |
| [`ETR.NegationNormalForm`](LeanCanny/ETR/NegationNormalForm.lean), [`NNFEncoding`](LeanCanny/ETR/NNFEncoding.lean), [`NNFFP`](LeanCanny/ETR/NNFFP.lean), [`NNFComplexity`](LeanCanny/ETR/NNFComplexity.lean) | A total polynomial-time normalizer pushes negations to atoms, preserves real semantics and arity, and has linear output length. Both polarities and every intermediate stack are bounded, even on raw malformed trees. NNF satisfiability is ∃ℝ-complete under reductions on all binary strings. |
| [`ETR.EquationSystem`](LeanCanny/ETR/EquationSystem.lean) | Arbitrary Boolean formulas compile into equation systems. Every satisfying assignment extends to a solution, preserving the original variables; every solution satisfies the formula. |
| [`ETR.EquationNormalization`](LeanCanny/ETR/EquationNormalization.lean) | A single final sum of squares collapses the system to one equisatisfiable integer polynomial equation. |
| [`ETR.EquationSize`](LeanCanny/ETR/EquationSize.lean) | For an input of `n` bits, the resulting equation has at most `500*(n+1)^3` encoded bits and arity at most `2*n`. This includes all unary fresh-variable indices and binary integer payloads. |
| [`ETR.SingleEquation`](LeanCanny/ETR/SingleEquation.lean) | A total executable map on binary strings preserves exactly the yes-instances from ETR to the single-equation language. Malformed inputs map to `1 = 0`; the output-length bound holds on all inputs. |
| [`ETR.EquationDegree`](LeanCanny/ETR/EquationDegree.lean) | The corresponding Mathlib integer multivariate polynomial has total degree at most `4*n` and has a real zero exactly when the original formula is satisfiable. |
| [`ETR.SingleEquationComplexity`](LeanCanny/ETR/SingleEquationComplexity.lean) | A polynomial-time many-one reduction from the single-equation language to ETR; hence the single-equation language belongs to ∃ℝ. Correctness covers malformed inputs too. |
| [`ETR.SumSquaresFP`](LeanCanny/ETR/SumSquaresFP.lean) | A polynomial-time bitstring writer collapses an encoded equation list into a sum of squares. Its complete paired state grows by at most 18 bits per iteration; the output vanishes exactly when every input term does. |
| [`ETR.EquationList`](LeanCanny/ETR/EquationList.lean), [`EquationListComplexity`](LeanCanny/ETR/EquationListComplexity.lean) | An exact `FP` recognizer for encoded term lists and a polynomial-time many-one reduction from satisfiable equation systems to one equation. Malformed strings map to `1 = 0`; the equation-system language belongs to ∃ℝ. |
| [`ETR.EquationEncoding`](LeanCanny/ETR/EquationEncoding.lean), [`EquationSystemEncoding`](LeanCanny/ETR/EquationSystemEncoding.lean) | Polynomial-time writers for fresh-witness equations, Boolean selectors, conjunction, and disjunction; exact agreement with the typed operations and literal length formulas. |
| [`ETR.EquationMaskFP`](LeanCanny/ETR/EquationMaskFP.lean) | A polynomial-time pass multiplies every equation by a branch selector, preserving order. The complete loop state adds at most `factor.length + 10` bits per step on all strings. |
| [`ETR.EquationCompilerMachine`](LeanCanny/ETR/EquationCompilerMachine.lean), [`EquationCompilerBounds`](LeanCanny/ETR/EquationCompilerBounds.lean), [`EquationCompilerStateEncoding`](LeanCanny/ETR/EquationCompilerStateEncoding.lean) | A sequential stack compiler agrees exactly with `SignedFormula.equations`, terminates within twice the formula's bit length, and keeps its entire encoded state below `10000*(n+1)^3` bits throughout the run, starting fresh indices at `n`. |
| [`ETR.EquationCompilerAtomEncoding`](LeanCanny/ETR/EquationCompilerAtomEncoding.lean), [`EquationCompilerStepEncoding`](LeanCanny/ETR/EquationCompilerStepEncoding.lean), [`EquationCompilerFP`](LeanCanny/ETR/EquationCompilerFP.lean) | The encoded step implements the typed stack machine and belongs to `FP`. The bounded loop gives polynomial-time reductions from ETR to equation systems and single equations, proving both target languages ∃ℝ-complete. Correctness covers all binary strings. |
| [`Algebra.Separation`](LeanCanny/Algebra/Separation.lean) | For `m` points in a characteristic-zero field, an integer `0 ≤ c ≤ m²` makes `(a,b) ↦ a+c*b` injective. Lagrange interpolation recovers both coordinates with degree below `m`. |
| [`Algebra.GaloisDescent`](LeanCanny/Algebra/GaloisDescent.lean) | For finite point sets stable under a finite Galois group, the nodal polynomial and coordinate interpolants descend to the input field. The nodal polynomial is monic and separable, with exactly the projected points as roots. |
| [`Algebra.PrimitiveCoordinates`](LeanCanny/Algebra/PrimitiveCoordinates.lean) | The algebraic existence part of Lemma 2.1: two square-free polynomials of degrees `d₁,d₂` over a characteristic-zero field have a monic separable degree-`d₁*d₂` representation, with coordinate polynomials over that same field. A common finite Galois splitting field is supplied; `c ≤ (d₁*d₂)^2`. |
| [`Algebra.GCDRecovery`](LeanCanny/Algebra/GCDRecovery.lean) | At `θ = a+c*b`, the GCD of `p₁(θ-c*x)` and `p₂(x)` is linear. Its coefficients recover `b = -g₀/g₁` and `a = θ+c*g₀/g₁`, with `g₁ ≠ 0`. The hypotheses include separability, splitting, and a separating direction. |
| [`Algebra.PrimitiveResultant`](LeanCanny/Algebra/PrimitiveResultant.lean), [`ResultantFactorization`](LeanCanny/Algebra/ResultantFactorization.lean) | The parameter polynomial is defined by a fixed-degree Sylvester determinant. Specialization, its exact roots, its leading-coefficient factor, and degree `d₁*d₂` are proved. Scalar normalization gives a monic polynomial; the sign from swapping the inputs is tracked explicitly. |
| [`Algebra.ResultantCoordinates`](LeanCanny/Algebra/ResultantCoordinates.lean) | The bounded primitive-coordinate representation uses the specified normalized resultant. A separating direction makes it separable, and coordinate polynomials over the input field recover every pair of roots. |
| [`Algebra.ShiftCoefficients`](LeanCanny/Algebra/ShiftCoefficients.lean) | Direct access to the coefficient of `x^i θ^j` in `p(θ-c*x)`: `choose(i+j,i)*p[i+j]*(-c)^i`. For degree `d` and integer input coefficient bound `H`, its magnitude is at most `2^d*H*(c+1)^d` and its bit length at most `d + H.size + (c+1).size*d + 1`. |
| [`Algebra.CoefficientBounds`](LeanCanny/Algebra/CoefficientBounds.lean) | A polynomial determinant with column coefficient-mass bounds `Bⱼ` has each coefficient bounded by `N! * ∏ Bⱼ`. Power-of-two column budgets give explicit binary length bounds. Column degree bounds also bound the determinant's degree, including empty matrices. |
| [`Algebra.ResultantBounds`](LeanCanny/Algebra/ResultantBounds.lean) | The unnormalized integer resultant has explicit coefficient magnitude and binary length bounds. Its degree is at most `d₁*d₂` over any commutative ring, without separability or nonzero hypotheses. The two input orders have equal coefficient magnitudes. |
| [`Algebra.MatrixPowerEntry`](LeanCanny/Algebra/MatrixPowerEntry.lean), [`MatrixPowerMachine`](LeanCanny/Algebra/MatrixPowerMachine.lean), [`MatrixPowerWork`](LeanCanny/Algebra/MatrixPowerWork.lean) | A continuation machine computes one entry of `A^e` over any semiring by balanced recursion, streaming the summation through a counter and accumulator. Correctness and the exact abstract transition count are proved; no intermediate matrix power is stored. |
| [`Algebra.MatrixPowerBounds`](LeanCanny/Algebra/MatrixPowerBounds.lean), [`MatrixPowerEncoding`](LeanCanny/Algebra/MatrixPowerEncoding.lean) | Every reachable state has at most `e.size` frames. A binary state representation is injective when its scalar representation is. For residues modulo nonzero `m`, complete states have at most `64*(N.size + e.size + m.size + 1)^2` bits for an `N`-dimensional matrix supplied as an entry function. |

The full equation compiler is now certified in polynomial time. It pushes negations
to atoms, concatenates conjunctions, and masks disjunction branches using fresh Boolean
selectors. It introduces sums of squares once at the end, avoiding exponential tree
copying. Both equation-system satisfiability and single-equation satisfiability are
∃ℝ-complete under Complexitylib's polynomial-time many-one reductions.

The certified entry points are `EquationCompiler.compileTerms` and
`EquationCompiler.toSingleEquation`. Their fresh-variable counter begins at the
normalized formula's encoded length, reserving all original indices. Every complete
intermediate state has a cubic bit-length bound. The earlier `500*(n+1)^3` output-size
theorem describes `Formula.singleEquation`, whose counter begins at the formula's arity.

The grammar checker agrees with the original decoder and validates canonical integer
payloads. It accepts well-formed unsatisfiable formulas; real satisfiability remains
the decision problem. Negation normalization copies arithmetic payloads unchanged.

The parameter polynomial in Lemma 2.1 is now the specified normalized Sylvester
resultant, with its roots, degree, and separability proved. Coordinate polynomials over
the original input field still come from Galois descent and interpolation. Linear-GCD
coefficient recovery is also verified. The shifted input family's coefficients have
direct formulas and integer bit-length bounds. The unnormalized integer resultant
has at most `d₁*d₂+1` supported coefficients. Writing `N = d₁+d₂` and
`b = (d₁+1).size + d₁ + H₁.size + (c+1).size*d₁`, each coefficient's magnitude
has binary length at most `N.size*N + d₂*b + d₁*H₂.size + 1` when the input
coefficient magnitudes are bounded by `H₁,H₂`. Encoded determinant computation,
symbolic subresultant recovery and its output-size bounds, and the report's
polylogarithmic-space computation remain open.

The streamed matrix-power primitive now has a verified continuation machine and
binary state-size bounds. Its abstract run takes at most
`2^((N.size+2)*e.size+1)` transitions. Entry access and scalar arithmetic count as
single abstract operations here. A decoder, certified implementations of the
encoded step and its arithmetic, and a determinant algorithm using this primitive
remain to be supplied before obtaining a machine-level space theorem.

## Next obligations

1. Relate the chosen encoding to standard ETR presentations and prove an NP lower inclusion.
2. Choose an algorithm interface after comparing a representative arithmetic routine
   and its workspace proof in Complexitylib and the Mathlib/TM2 evaluator used by
   `lean-trominoes`. A smaller dependency alone does not justify a separate library.
3. Implement encoded determinant and subresultant algorithms for the verified
   construction, with workspace bounds and the remaining subresultant output-size
   bounds; formalize the parallel/streamed algebra used by the report.
4. Formalize critical points, perturbations, sign tests, and the correctness of Canny's
   ETR decision procedure; prove `ETR ∈ PSPACE`.
5. Supply the required closure of PSPACE under polynomial-time reductions to derive
   `∃ℝ ⊆ PSPACE`. A suitable packaged theorem was not found in the pinned dependency.
6. Extend to roadmap connectivity and the geometric consequences in the report.

See [`RESEARCH.md`](RESEARCH.md) for prior work, the machine-model comparison, and
where Savitch's theorem enters.

## Report integrity

Source: [Berkeley PDF](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/Archive/CSD-88-439.pdf).
The downloaded file has 936,246 bytes and SHA-256
`7606d41dea23ac1160562a759c196267906d8aec0f754cd4998fdd14fcd185f8`.
The report retains its original rights; the source-code license does not apply to it.
