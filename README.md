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
| [`Encoding.BinaryNatFP`](LeanCanny/Encoding/BinaryNatFP.lean) | Machine-certified polynomial-time normalization, successor, truncated predecessor, floor half, and ceiling half directly on binary words. The arithmetic specifications cover arbitrary little-endian inputs and produce canonical outputs; no magnitude is expanded to unary. Canonical binary words have an `FP` recognizer. |
| [`Encoding.BinaryAddFP`](LeanCanny/Encoding/BinaryAddFP.lean) | Binary natural-number addition belongs to Complexitylib's machine-level `FP`. A Horner fold doubles the partial sum and adds the two digits by binary increment; every intermediate word is linearly bounded in the input length. Correctness covers arbitrary little-endian words and canonical output has at most `a.length+b.length+1` bits. |
| [`Encoding.BinaryMulFP`](LeanCanny/Encoding/BinaryMulFP.lean) | Binary natural-number multiplication and multiply-accumulate belong to `FP`. Every partial product in the shift-and-add fold is canonical and has at most the sum of the operand bit lengths. Correctness includes zero, empty words, and redundant high zeroes. |
| [`Encoding.BinarySubFP`](LeanCanny/Encoding/BinarySubFP.lean) | Comparison and truncated subtraction on binary natural words have machine-level polynomial-time certificates. Fixed-width complement addition detects the subtraction carry; the low bits recover the difference. All specifications include noncanonical inputs. |
| [`Encoding.BinaryModFP`](LeanCanny/Encoding/BinaryModFP.lean) | Uniform `FP` modular reduction and modular multiply-accumulate, with the modulus supplied in binary. Long division uses one comparison and at most one subtraction per digit. Every partial remainder is canonical and no longer than the processed dividend; modulus zero follows `a % 0 = a`. |
| [`Encoding.BinaryDivFP`](LeanCanny/Encoding/BinaryDivFP.lean) | Uniform FP binary quotient and paired quotient/remainder, with exact semantics on all words. Reusing the remainder routine determines each quotient digit. Every partial quotient is canonical and no longer than the processed dividend; division by zero gives zero. The final paired output has at most `3*a.length+2` bits. |
| [`Algebra.MatrixPowerQueryFP`](LeanCanny/Algebra/MatrixPowerQueryFP.lean) | Total `FP` writers for the initial query and both child queries agree with the typed machine. Initial height comes from the exponent word's bit length. |
| [`Algebra.MatrixPowerDecoding`](LeanCanny/Algebra/MatrixPowerDecoding.lean) | Exact decoders for queries, frames, stacks, residues, and complete states. Successful state decoding characterizes equality with the canonical encoding. A checked total transition agrees with the typed step and inherits its result and quadratic modular-state bound. |
| [`Algebra.MatrixPowerArithmeticFP`](LeanCanny/Algebra/MatrixPowerArithmeticFP.lean) | The uniform modular multiply-accumulate routine agrees exactly with `ZMod` residue encodings for every nonzero modulus. Encoded zero and one are certified too, including modulus one. The modulus is an input field of one FP routine. |
| [`Algebra.MatrixPowerController`](LeanCanny/Algebra/MatrixPowerController.lean), [`MatrixPowerControllerCorrect`](LeanCanny/Algebra/MatrixPowerControllerCorrect.lean) | A total context-carrying bitstring transition belongs to `FP` when its explicit callbacks do. It simulates every typed transition on encoded states. The modular specialization supplies scalar callbacks and retains the original context for entry access. Packet initialization is certified too. Every modular packet has at most `2*c.length+2+64*(N.size+e.size+m.size+1)^2` bits throughout the run. |
| [`Computation.HaltingIteration`](LeanCanny/Computation/HaltingIteration.lean) | An FP initializer, transition, halting test, and answer yield a PSPACE decision procedure when states have polynomial length and the first halting time is at most exponential in a polynomial. The wrapper supplies the exact completion/answer protocol required by Complexitylib's `SpaceIter`; the clock need not be computed. |
| [`Algebra.MatrixPowerHalting`](LeanCanny/Algebra/MatrixPowerHalting.lean), [`MatrixPowerPSPACE`](LeanCanny/Algebra/MatrixPowerPSPACE.lean) | The controller first finishes at exactly `work N e.size e + 1` steps. Testing whether a selected entry of a modular matrix power is zero belongs to Complexitylib's `PSPACE`, given canonical FP field writers and uniform FP entry access on every input. Dimensions and exponents may be exponentially large; only their binary descriptions enter the bound. |
| [`Algebra.CharacteristicAdjugate`](LeanCanny/Algebra/CharacteristicAdjugate.lean), [`BorderedDeterminant`](LeanCanny/Algebra/BorderedDeterminant.lean) | Every coefficient of `adj(XI-A)` is a sum of characteristic coefficients times powers of `A`. Block elimination proves the bordered determinant formula by cancellation of a regular determinant; a monic characteristic polynomial supplies that cancellation over arbitrary commutative rings. |
| [`Algebra.BerkowitzRecurrence`](LeanCanny/Algebra/BerkowitzRecurrence.lean), [`BerkowitzCoefficients`](LeanCanny/Algebra/BerkowitzCoefficients.lean) | The division-free bordered characteristic-coefficient recurrence uses scalar moments `r A^k c`. A recursive reference on `Fin n` matrices agrees with every Mathlib characteristic coefficient, and its signed constant coefficient equals the determinant, including the empty matrix. This reference has linear recursion depth and no space certificate. |
| [`Algebra.BerkowitzTransform`](LeanCanny/Algebra/BerkowitzTransform.lean), [`BerkowitzProduct`](LeanCanny/Algebra/BerkowitzProduct.lean) | Padded coefficient vectors turn each bordered recurrence into a square matrix action. The ordered product's first column gives all characteristic coefficients; its signed top-left entry is the determinant. Factor entries depend on input entries and scalar power moments, without using characteristic coefficients. |
| [`Algebra.MatrixProductEntry`](LeanCanny/Algebra/MatrixProductEntry.lean), [`BerkowitzBalanced`](LeanCanny/Algebra/BerkowitzBalanced.lean) | Balanced interval recursion computes an entry of any ordered matrix product over a semiring, preserving factor order. Applied to the coefficient transformations, height `n.size` suffices to recover every characteristic coefficient and the determinant. A factor accessor avoids constructing the full list. These identities establish correctness and recursion height; the power-machine bridge below still needs certified factor access. |
| [`Algebra.LayeredMatrix`](LeanCanny/Algebra/LayeredMatrix.lean), [`LayeredMatrixMachine`](LeanCanny/Algebra/LayeredMatrixMachine.lean) | An ordered product interval is one entry of a layered matrix power. Flattening the layer-coordinate pairs gives `Fin` indices. The existing streamed power machine and context-carrying controller evaluate the product under their entry-access contract, with the inherited exact clock and modular state bound. |
| [`Algebra.BerkowitzPower`](LeanCanny/Algebra/BerkowitzPower.lean) | The `n`th power of an `(n+1)^2`-dimensional layered matrix contains every characteristic coefficient. The power machine computes them, and its encoded controller tests determinant zero under the explicit callback contract. Stored residue states have at most `64*(3*n.size+m.size+2)^2` bits; controller packets add `2*c.length+2`. Factor-access workspace is excluded and remains open. |
| [`Computation.SubroutineIteration`](LeanCanny/Computation/SubroutineIteration.lean), [`SubroutineBounds`](LeanCanny/Computation/SubroutineBounds.lean), [`SubroutinePSPACE`](LeanCanny/Computation/SubroutinePSPACE.lean) | An FP transition suspends a parent while a child evaluator runs, retaining both encoded states. A variable clock simulates the abstract parent iteration and classifies every intermediate state. Parent and child bounds `S,U` give at most `2*S+U+3` stored bits. Polynomial state bounds and exponential parent/child clocks yield PSPACE without requiring an entire child call to be FP. |
| [`Algebra.MatrixPowerSubroutine`](LeanCanny/Algebra/MatrixPowerSubroutine.lean) | Exponent-one queries launch a child entry evaluator; its output resumes the saved power stack. Request writing, resumption, and the complete suspended step have FP certificates from the control operations and child primitives. Correct, terminating child calls simulate the original power controller and preserve the final matrix-power result at the expanded clock. The determinant-factor child still needs to assemble the components below. |
| [`Algebra.BerkowitzFactorAccess`](LeanCanny/Algebra/BerkowitzFactorAccess.lean) | Factor `s` is accessed directly through the trailing block `A[s+i,s+j]`, with a proved identity default beyond the last factor. Its entries split into one, a negated diagonal entry, a negated scalar moment, or zero. The moment case is exactly the negative of an augmented matrix-power entry. No preceding factors or coefficient vectors are needed. |
| [`Algebra.MatrixMomentPower`](LeanCanny/Algebra/MatrixMomentPower.lean), [`MatrixMomentFP`](LeanCanny/Algebra/MatrixMomentFP.lean) | Adding a source and sink makes `r A^k c` one entry of the `(k+2)`nd power of an `(n+2)`-dimensional matrix. Uniform FP binary field, row, column, and original-entry access gives certified augmented-entry access, child initialization, and a complete power controller. Result extraction, first halting time, and every packet's size are proved. The child computes one moment without storing its summands. |
| [`Algebra.ModularNegFP`](LeanCanny/Algebra/ModularNegFP.lean) | Uniform FP negation of binary residues agrees with `ZMod`, including modulus one. Reducing, subtracting from the modulus, and reducing again handles arbitrary binary input words. The moment child has a certified negated-output projection for the factor evaluator. |
| [`Algebra.BerkowitzQueryFP`](LeanCanny/Algebra/BerkowitzQueryFP.lean), [`BerkowitzMomentAccessFP`](LeanCanny/Algebra/BerkowitzMomentAccessFP.lean) | FP division/remainder decodes flattened layer and coefficient indices. FP writers supply the trailing dimension, offset, moment exponent, and four-case selector, with exact numeric specifications. Offset query writers access the original input matrix and give certified callbacks for exactly the trailing block and border vectors in the moment formula. |

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
single abstract operations here. Exact decoding and certified initial/child-query
writers and modular scalar arithmetic are now provided. The context-carrying
controller has a complete `FP` transition certificate given certified dimension,
modulus, and matrix-entry callbacks. It simulates the typed run on encoded states;
the initial packet writer is `FP` given certified exponent and index writers.
`ModularAccess.zeroLanguage_mem_PSPACE` connects this controller to `SpaceIter`:
zero testing of a selected modular power entry is in `PSPACE` under the explicit
FP access contract. The contract specifies a nonzero modulus and valid indices
on every binary input; a concrete input format must supply validation and defaults.
`MatrixPowerSubroutine` now supplies a second interface: a child evaluator runs
through FP steps while the outer state is saved. Its whole entry computation need
not be FP. `SubroutineIteration.mem_PSPACE` accounts for both states and the expanded
clock, under explicit polynomial workspace and exponential time bounds on the
reachable parent run and its child calls. The determinant-factor evaluator still
must instantiate those contracts. The division-free bordered recurrence behind
Berkowitz's algorithm is now proved, together with a recursive determinant reference.
Padded coefficient transformations give an ordered matrix product whose first
column contains the characteristic coefficients. `Berkowitz.balancedDeterminant`
recovers the determinant using product-entry recursion of height `n.size`.
The layered construction reduces that ordered product to the existing streamed
power machine, so no separate outer-product controller is needed. Its matrix has
dimension `(n+1)^2`, and stored residue states have at most
`64*(3*n.size+m.size+2)^2` bits. The abstract clock is at most
`2^((2*n.size+3)*n.size+1)`, counting entry access as one operation.
Direct trailing-block access now agrees with the recursive factor specification.
The nontrivial moment `r A^k c` is one power entry after adding a source and sink.
Its uniform child controller has FP initialization, transition, halting test,
result extraction, and modular negation, given certified binary fields and
row/column/matrix access.
For inner dimension `d`, exponent `k`, modulus `m`, and context `c`, every child
packet has at most `2*c.length+2+64*((d+2).size+(k+2).size+m.size+1)^2` bits.
Binary division/remainder, query decoding, and case selection now have FP
certificates. The offset writers supply exactly the trailing block and border
vectors from the original matrix, giving certified moment-child callbacks.
The immediate and moment cases still need to be assembled into one factor child,
with a combined parent/child resource proof. This evaluator and
Canny's remaining algebraic and geometric arguments remain open; a determinant
PSPACE theorem is not yet proved.

Binary addition, multiplication, comparison, subtraction, division, and modular reduction
now have uniform `FP` certificates, with exact semantics and bounds on intermediate
states. Their modular multiply-accumulate composition supplies the scalar arithmetic
callback required by the modular power machine.

## Next obligations

1. Relate the chosen encoding to standard ETR presentations and prove an NP lower inclusion.
2. Instantiate the modular power PSPACE theorem with concrete validated input
   formats and uniform entry evaluators;
   instantiate the suspended-entry interface when the whole entry computation
   requires more than polynomial time.
3. Assemble the determinant-factor child from the certified case selector,
   trailing-block query writers, scalar-moment child, and modular negation.
   Prove its complete correctness, termination, and combined resource contracts
   for the suspended controller. Supply encoded subresultant computation
   and its remaining output-size bounds; formalize the parallel/streamed algebra used by the report.
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
